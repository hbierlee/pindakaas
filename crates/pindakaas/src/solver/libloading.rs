#[cfg(feature = "ipasir-up")]
use std::{any::Any, collections::VecDeque};
use std::{
	ffi::{c_char, c_int, c_void, CStr},
	fmt,
	num::NonZeroI32,
	ptr,
};

use libloading::{Library, Symbol};

use super::{
	FailedAssumtions, LearnCallback, SlvTermSignal, SolveAssuming, SolveResult, Solver,
	TermCallback, VarFactory,
};
#[cfg(feature = "ipasir-up")]
use super::{Propagator, SolvingActions};
use crate::{ClauseDatabase, ConditionalDatabase, Lit, Result, Valuation, Var};

#[derive(Debug)]
pub struct IpasirLibrary {
	lib: Library,
}

pub type SymResult<'a, S, E = libloading::Error> = std::result::Result<Symbol<'a, S>, E>;

impl IpasirLibrary {
	fn ipasir_signature_sym(&self) -> SymResult<extern "C" fn() -> *const c_char> {
		unsafe { self.lib.get(b"ipasir_signature") }
	}

	fn ipasir_init_sym(&self) -> SymResult<extern "C" fn() -> *mut c_void> {
		unsafe { self.lib.get(b"ipasir_init") }
	}

	fn ipasir_release_sym(&self) -> SymResult<extern "C" fn(*mut c_void)> {
		unsafe { self.lib.get(b"ipasir_release") }
	}

	fn ipasir_add_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		unsafe { self.lib.get(b"ipasir_add") }
	}

	fn ipasir_assume_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		unsafe { self.lib.get(b"ipasir_assume") }
	}

	fn ipasir_solve_sym(&self) -> SymResult<extern "C" fn(*mut c_void) -> c_int> {
		unsafe { self.lib.get(b"ipasir_solve") }
	}
	fn ipasir_value_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> i32> {
		unsafe { self.lib.get(b"ipasir_val") }
	}

	fn ipasir_failed_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> c_int> {
		unsafe { self.lib.get(b"ipasir_failed") }
	}

	fn ipasir_set_terminate_sym(
		&self,
	) -> SymResult<
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	> {
		unsafe { self.lib.get(b"ipasir_set_terminate") }
	}

	fn ipasir_set_learn_sym(
		&self,
	) -> SymResult<
		extern "C" fn(
			*mut c_void,
			*mut c_void,
			c_int,
			Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
		),
	> {
		unsafe { self.lib.get(b"ipasir_set_learn") }
	}

	pub fn signature(&self) -> &str {
		unsafe { CStr::from_ptr((self.ipasir_signature_sym().unwrap())()) }
			.to_str()
			.unwrap()
	}

	pub fn new_solver(&self) -> IpasirSolver<'_> {
		IpasirSolver {
			slv: (self.ipasir_init_sym().unwrap())(),
			vars: VarFactory::default(),
			learn_cb: LearnCB::default(),
			term_cb: TermCB::default(),
			signature_fn: self.ipasir_signature_sym().unwrap(),
			release_fn: self.ipasir_release_sym().unwrap(),
			add_fn: self.ipasir_add_sym().unwrap(),
			assume_fn: self.ipasir_assume_sym().unwrap(),
			solve_fn: self.ipasir_solve_sym().unwrap(),
			value_fn: self.ipasir_value_sym().unwrap(),
			failed_fn: self.ipasir_failed_sym().unwrap(),
			set_terminate_fn: self.ipasir_set_terminate_sym().unwrap(),
			set_learn_fn: self.ipasir_set_learn_sym().unwrap(),
		}
	}
}

impl TryFrom<Library> for IpasirLibrary {
	type Error = libloading::Error;

	fn try_from(lib: Library) -> Result<Self, Self::Error> {
		let lib = IpasirLibrary { lib };
		lib.ipasir_signature_sym()?;
		lib.ipasir_init_sym()?;
		lib.ipasir_release_sym()?;
		lib.ipasir_add_sym()?;
		lib.ipasir_assume_sym()?;
		lib.ipasir_solve_sym()?;
		lib.ipasir_value_sym()?;
		lib.ipasir_failed_sym()?;
		lib.ipasir_set_terminate_sym()?;
		lib.ipasir_set_learn_sym()?;
		Ok(lib)
	}
}

#[derive(Debug)]
pub struct IpasirSolver<'lib> {
	/// The raw pointer to the Intel SAT solver.
	slv: *mut c_void,
	/// The variable factory for this solver.
	vars: VarFactory,

	/// The callback used when a clause is learned.
	learn_cb: LearnCB,
	/// The callback used to check whether the solver should terminate.
	term_cb: TermCB,

	signature_fn: Symbol<'lib, extern "C" fn() -> *const c_char>,
	release_fn: Symbol<'lib, extern "C" fn(*mut c_void)>,
	add_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32)>,
	assume_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32)>,
	solve_fn: Symbol<'lib, extern "C" fn(*mut c_void) -> c_int>,
	value_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> i32>,
	failed_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> c_int>,
	set_terminate_fn: Symbol<
		'lib,
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	>,
	set_learn_fn: Symbol<
		'lib,
		extern "C" fn(
			*mut c_void,
			*mut c_void,
			c_int,
			Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
		),
	>,
}

impl<'lib> Drop for IpasirSolver<'lib> {
	fn drop(&mut self) {
		(self.release_fn)(self.slv)
	}
}

impl<'lib> ClauseDatabase for IpasirSolver<'lib> {
	fn new_var(&mut self) -> Var {
		self.vars.next().expect("variable pool exhaused")
	}

	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, clause: I) -> Result {
		let mut added = false;
		for lit in clause.into_iter() {
			(self.add_fn)(self.slv, lit.into());
			added = true;
		}
		if added {
			(self.add_fn)(self.slv, 0);
		}
		Ok(())
	}

	type CondDB = Self;
	fn with_conditions(&mut self, conditions: Vec<Lit>) -> ConditionalDatabase<Self::CondDB> {
		ConditionalDatabase {
			db: self,
			conditions,
		}
	}
}

impl<'lib> Solver for IpasirSolver<'lib> {
	type ValueFn = IpasirSol<'lib>;

	fn signature(&self) -> &str {
		unsafe { CStr::from_ptr((self.signature_fn)()) }
			.to_str()
			.unwrap()
	}

	fn solve<SolCb: FnOnce(&Self::ValueFn)>(&mut self, on_sol: SolCb) -> SolveResult {
		let res = (self.solve_fn)(self.slv);
		match res {
			10 => {
				// 10 -> Sat
				on_sol(&self.sol_obj());
				SolveResult::Sat
			}
			20 => SolveResult::Unsat, // 20 -> Unsat
			_ => {
				debug_assert_eq!(res, 0); // According to spec should be 0, unknown
				SolveResult::Unknown
			}
		}
	}
}

impl<'lib> SolveAssuming for IpasirSolver<'lib> {
	type FailFn = IpasirFailed<'lib>;

	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&<Self as Solver>::ValueFn),
		FailCb: FnOnce(&Self::FailFn),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult {
		for i in assumptions {
			(self.assume_fn)(self.slv, i.into());
		}
		match self.solve(on_sol) {
			SolveResult::Unsat => {
				on_fail(&self.failed_obj());
				SolveResult::Unsat
			}
			r => r,
		}
	}
}

impl<'lib> IpasirSolver<'lib> {
	fn sol_obj(&self) -> IpasirSol<'lib> {
		IpasirSol {
			slv: self.slv,
			value_fn: self.value_fn.clone(),
		}
	}
	fn failed_obj(&self) -> IpasirFailed<'lib> {
		IpasirFailed {
			slv: self.slv,
			failed_fn: self.failed_fn.clone(),
		}
	}
}

#[derive(Debug)]
pub struct IpasirSol<'lib> {
	slv: *mut c_void,
	value_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> i32>,
}

impl Valuation for IpasirSol<'_> {
	fn value(&self, lit: Lit) -> Option<bool> {
		let lit: i32 = lit.into();
		let val = (self.value_fn)(self.slv, lit);
		match val {
			_ if val == lit => Some(true),
			_ if val == -lit => Some(false),
			_ => {
				debug_assert_eq!(val, 0); // zero according to spec, both value are valid
				None
			}
		}
	}
}

#[derive(Debug)]
pub struct IpasirFailed<'lib> {
	slv: *mut c_void,
	failed_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> c_int>,
}

impl FailedAssumtions for IpasirFailed<'_> {
	fn fail(&self, lit: Lit) -> bool {
		let lit: i32 = lit.into();
		let failed = (self.failed_fn)(self.slv, lit);
		failed != 0
	}
}

impl<'lib> TermCallback for IpasirSolver<'lib> {
	fn set_terminate_callback<F: FnMut() -> SlvTermSignal + 'static>(&mut self, cb: Option<F>) {
		if let Some(mut cb) = cb {
			self.term_cb = TermCB::new(move || -> c_int {
				match cb() {
					SlvTermSignal::Continue => c_int::from(0),
					SlvTermSignal::Terminate => c_int::from(1),
				}
			});

			(self.set_terminate_fn)(self.slv, self.term_cb.as_ptr(), Some(TermCB::exec_callback));
		} else {
			self.term_cb = TermCB::default();
			(self.set_terminate_fn)(self.slv, ptr::null_mut(), None);
		}
	}
}

impl<'lib> LearnCallback for IpasirSolver<'lib> {
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		const MAX_LEN: std::ffi::c_int = 512;
		if let Some(mut cb) = cb {
			self.learn_cb = LearnCB::new(move |clause: *const i32| {
				let mut iter = ExplIter(clause).map(|i: i32| Lit(NonZeroI32::new(i).unwrap()));
				cb(&mut iter)
			});
			(self.set_learn_fn)(
				self.slv,
				self.learn_cb.as_ptr(),
				MAX_LEN,
				Some(LearnCB::exec_callback),
			);
		} else {
			self.learn_cb = LearnCB::default();
			(self.set_learn_fn)(self.slv, ptr::null_mut(), MAX_LEN, None);
		}
	}
}

/// Storage for user provided callbacks when a new clause is learned.
pub(crate) struct LearnCB(pub(crate) Box<Box<dyn FnMut(*const c_int)>>);
impl LearnCB {
	pub(crate) unsafe extern "C" fn exec_callback(data: *mut c_void, clause: *const c_int) {
		let cb: &mut Box<dyn FnMut(*const c_int)> =
			&mut *(data as *mut Box<dyn FnMut(*const c_int)>);
		cb(clause)
	}
	pub(crate) fn new(f: impl FnMut(*const c_int) + 'static) -> Self {
		Self(Box::new(Box::new(f)))
	}
	pub(crate) fn as_ptr(&self) -> *mut c_void {
		#[allow(clippy::borrowed_box)]
		let x: &Box<dyn FnMut(*const c_int)> = &self.0;
		x as *const _ as *mut c_void
	}
}
impl fmt::Debug for LearnCB {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_tuple("LearnCB").field(&self.as_ptr()).finish()
	}
}
impl Default for LearnCB {
	fn default() -> Self {
		Self(Box::new(Box::new(|_| {})))
	}
}

/// Storage for user provided callbacks to check whether a solver should terminate.
pub(crate) struct TermCB(pub(crate) Box<Box<dyn FnMut() -> c_int>>);
impl TermCB {
	pub(crate) unsafe extern "C" fn exec_callback(data: *mut c_void) -> c_int {
		let cb: &mut Box<dyn FnMut() -> c_int> = &mut *(data as *mut Box<dyn FnMut() -> c_int>);
		cb()
	}
	pub(crate) fn new(f: impl FnMut() -> c_int + 'static) -> Self {
		Self(Box::new(Box::new(f)))
	}
	pub(crate) fn as_ptr(&self) -> *mut c_void {
		#[allow(clippy::borrowed_box)]
		let x: &Box<dyn FnMut() -> c_int> = &self.0;
		x as *const _ as *mut c_void
	}
}
impl fmt::Debug for TermCB {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_tuple("TermCB").field(&self.as_ptr()).finish()
	}
}
impl Default for TermCB {
	fn default() -> Self {
		Self(Box::new(Box::new(|| 0)))
	}
}

/// Iterator over the elements of a null-terminated i32 array
#[derive(Debug, Clone, Copy)]
pub(crate) struct ExplIter(pub(crate) *const i32);
impl Iterator for ExplIter {
	type Item = i32;
	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		unsafe {
			if *self.0 == 0 {
				None
			} else {
				let ptr = self.0;
				self.0 = ptr.offset(1);
				Some(*ptr)
			}
		}
	}
}

#[cfg(feature = "ipasir-up")]
#[derive(Debug, Clone, Copy)]
pub(crate) struct NoProp;

#[cfg(feature = "ipasir-up")]
impl Propagator for NoProp {
	fn as_any(&self) -> &dyn Any {
		self
	}
	fn as_mut_any(&mut self) -> &mut dyn Any {
		self
	}
}

#[cfg(feature = "ipasir-up")]
pub(crate) struct IpasirPropStore {
	/// Rust Propagator
	pub(crate) prop: Box<dyn Propagator>,
	/// IPASIR solver pointer
	pub(crate) slv: *mut dyn SolvingActions,
	/// Propagation queue
	pub(crate) pqueue: VecDeque<crate::Lit>,
	/// Reason clause queue
	pub(crate) rqueue: VecDeque<crate::Lit>,
	pub(crate) explaining: Option<Lit>,
	/// External clause queue
	pub(crate) cqueue: Option<VecDeque<crate::Lit>>,
}

#[cfg(feature = "ipasir-up")]
impl IpasirPropStore {
	pub(crate) fn new(prop: Box<dyn Propagator>, slv: *mut dyn SolvingActions) -> Self {
		Self {
			prop,
			slv,
			pqueue: VecDeque::default(),
			rqueue: VecDeque::default(),
			explaining: None,
			cqueue: None,
		}
	}
}

// --- Callback functions for C propagator interface ---

#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_notify_assignment_cb(
	state: *mut c_void,
	lit: i32,
	is_fixed: bool,
) {
	let prop = &mut *(state as *mut IpasirPropStore);
	let lit = crate::Lit(std::num::NonZeroI32::new(lit).unwrap());
	prop.prop.notify_assignment(lit, is_fixed)
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_notify_new_decision_level_cb(state: *mut c_void) {
	let prop = &mut *(state as *mut IpasirPropStore);
	prop.prop.notify_new_decision_level()
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_notify_backtrack_cb(state: *mut c_void, level: usize) {
	let prop = &mut *(state as *mut IpasirPropStore);
	prop.pqueue.clear();
	prop.explaining = None;
	prop.rqueue.clear();
	prop.cqueue = None;
	prop.prop.notify_backtrack(level);
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_check_model_cb(
	state: *mut c_void,
	len: usize,
	model: *const i32,
) -> bool {
	let prop = &mut *(state as *mut IpasirPropStore);
	let sol = if len > 0 {
		std::slice::from_raw_parts(model, len)
	} else {
		&[]
	};
	let sol: std::collections::HashMap<Var, bool> = sol
		.iter()
		.map(|&i| (Var(NonZeroI32::new(i.abs()).unwrap()), i >= 0))
		.collect();
	let value = |l: Lit| sol.get(&l.var()).copied();
	prop.prop.check_model(&mut *prop.slv, &value)
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_decide_cb(state: *mut c_void) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore);
	if let Some(l) = prop.prop.decide() {
		l.0.into()
	} else {
		0
	}
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_propagate_cb(state: *mut c_void) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore);
	if prop.pqueue.is_empty() {
		let slv = &mut *prop.slv;
		prop.pqueue = prop.prop.propagate(slv).into()
	}
	if let Some(l) = prop.pqueue.pop_front() {
		l.0.into()
	} else {
		0 // No propagation
	}
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_add_reason_clause_lit_cb(
	state: *mut c_void,
	propagated_lit: i32,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore);
	let lit = crate::Lit(std::num::NonZeroI32::new(propagated_lit).unwrap());
	debug_assert!(prop.explaining.is_none() || prop.explaining == Some(lit));
	// TODO: Can this be prop.explaining.is_none()?
	if prop.explaining != Some(lit) {
		prop.rqueue = prop.prop.add_reason_clause(lit).into();
		prop.explaining = Some(lit);
	}
	if let Some(l) = prop.rqueue.pop_front() {
		l.0.into()
	} else {
		// End of explanation
		prop.explaining = None;
		0
	}
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_has_external_clause_cb(state: *mut c_void) -> bool {
	let prop = &mut *(state as *mut IpasirPropStore);
	prop.cqueue = prop.prop.add_external_clause(&mut *prop.slv).map(Vec::into);
	prop.cqueue.is_some()
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_add_external_clause_lit_cb(state: *mut c_void) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore);
	if prop.cqueue.is_none() {
		debug_assert!(false);
		// This function shouldn't be called when "has_clause" returned false.
		prop.cqueue = prop.prop.add_external_clause(&mut *prop.slv).map(Vec::into);
	}
	if let Some(queue) = &mut prop.cqueue {
		if let Some(l) = queue.pop_front() {
			l.0.get()
		} else {
			prop.cqueue = None;
			0 // End of clause
		}
	} else {
		debug_assert!(false);
		// Even after re-assessing, no additional clause was found. Just return 0
		0
	}
}
