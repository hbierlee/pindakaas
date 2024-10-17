use std::{any::Any, collections::VecDeque, ffi::c_void, num::NonZeroI32};

use crate::{
	solver::{FFIPointer, Solver},
	Lit, Valuation, Var,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Whether a clause could possibly be removed from the clause database.
pub enum ClausePersistence {
	/// The clause is to be considered forgettable. Its removal would not affect
	/// the solver's correctness (in combination with the propagator), and it can
	/// be re-derived if needed.
	Forgettable,
	/// The clause is to be considered irreduntant. It contains information that
	/// can not (easily) be re-derived.
	Irreduntant,
}

/// A trait containing additional actions that the solver can perform during
/// solving. In contrast to [`SolvingActions`], these additional actions are not
/// exposed to the propagator.
pub(crate) trait ExtendedSolvingActions: SolvingActions {
	fn force_backtrack(&mut self, level: usize);
}

/// Trait implemented by the object given to the callback on detecting failure
pub trait FailedAssumtions {
	/// Check if the given assumption literal was used to prove the unsatisfiability
	/// of the formula under the assumptions used for the last SAT search.
	///
	/// Note that for literals 'lit' which are not assumption literals, the behavior
	/// of is not specified.
	fn fail(&self, lit: Lit) -> bool;
}

pub(crate) struct IpasirPropStore<P, A> {
	/// Rust Propagator
	pub(crate) prop: P,
	/// IPASIR solver pointer
	pub(crate) slv: A,
	/// Propagation queue
	pub(crate) pqueue: VecDeque<Lit>,
	/// Reason clause queue
	pub(crate) rqueue: VecDeque<Lit>,
	pub(crate) explaining: Option<Lit>,
	/// External clause queue
	pub(crate) cqueue: Option<VecDeque<Lit>>,
}

/// Get mutable access to the external propagator given the to solver
pub trait MutPropagatorAccess {
	/// Get mutable access to the external propagator given the to solver
	///
	/// This method will return [`None`] if no propagator is set, or if the
	/// propagator is not of type [`P`].
	fn propagator_mut<P: Propagator + 'static>(&mut self) -> Option<&mut P>;
}

pub trait PropagatingSolver: Solver + PropagatorAccess + MutPropagatorAccess
where
	Self::ValueFn: PropagatorAccess,
{
	/// Set Propagator implementation which allows to learn, propagate and
	/// backtrack based on external constraints.
	///
	/// Only one Propagator can be connected, any previous propagator will be
	/// overriden. This Propagator is notified of all changes to which it has
	/// subscribed, using the [`add_observed_var`] method.
	///
	/// # Warning
	///
	/// Calling this method automatically resets the observed variable set.
	fn set_external_propagator<P: Propagator + 'static>(&mut self, prop: Option<P>);

	fn add_observed_var(&mut self, var: Var);
	fn remove_observed_var(&mut self, var: Var);
	fn reset_observed_vars(&mut self);
}

pub trait Propagator {
	/// Check whether the propagator only checks complete assignments.
	///
	/// This method is called and checked only when the propagator is connected. If
	/// the propagator returns `true`, it is only asked to validate wheter complete
	/// assignments produced are correct.
	fn is_check_only(&self) -> bool {
		false
	}

	/// Check whether the propagator's produced reasons are forgettable.
	///
	/// This method is called and checked only when the propagator is connected. If
	/// the propagator returns [`ClausePersistence::Forgettable`], then the solver
	/// might remove the reason clause to save memory. The propagator must be able
	/// to re-derive the reason clause at a later point.
	fn reason_persistence(&self) -> ClausePersistence {
		ClausePersistence::Irreduntant
	}

	/// Check whether the propagator wants to be notified about persistent
	/// assignments of literals.
	///
	/// This method is called and checked only when the propagator is connected. If
	/// the propagator returns `true`, then the
	/// [`Self::notify_persistent_assignment`] method will be called (in addition
	/// to [`Self::notify_assignments`]) to notify the propagator about assignemnts
	/// that will persist for the remainder of the search for literals concerning
	/// observed variables.
	fn enable_persistent_assignments(&self) -> bool {
		false
	}

	/// Method called to notify the propagator about assignments of literals
	/// concerning observed variables.
	///
	/// The notification is not necessarily eager. It usually happens before the
	/// call of propagator callbacks and when a driving clause is leading to an
	/// assignment.
	fn notify_assignments(&mut self, lits: &[Lit]) {
		let _ = lits;
	}
	fn notify_new_decision_level(&mut self) {}
	fn notify_backtrack(&mut self, new_level: usize, restart: bool) {
		let _ = new_level;
		let _ = restart;
	}
	fn notify_persistent_assignment(&mut self, lit: Lit) {
		let _ = lit;
	}

	/// Method called to check the found complete solution (after solution
	/// reconstruction). If it returns false, the propagator must provide an
	/// external clause during the next callback.
	fn check_model(&mut self, slv: &mut dyn SolvingActions, value: &dyn Valuation) -> bool {
		let _ = value;
		let _ = slv;
		true
	}

	/// Method called when the solver asks for the next search decision.
	///
	/// The propagator can either decide to assign a given literal, force the
	/// solver to backtrack to a given decision level, or leave the decision to the
	/// solver.
	fn decide(&mut self, slv: &mut dyn SolvingActions) -> SearchDecision {
		let _ = slv;
		SearchDecision::Free
	}

	/// Method to ask the propagator if there is an propagation to make under the
	/// current assignment. It returns queue of literals to be propagated in order,
	/// if an empty queue is returned it indicates that there is no propagation
	/// under the current assignment.
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Vec<Lit> {
		let _ = slv;
		Vec::new()
	}

	/// Ask the external propagator for the reason clause of a previous external
	/// propagation step (done by [`Propagator::propagate`]). The clause must
	/// contain the propagated literal.
	fn add_reason_clause(&mut self, propagated_lit: Lit) -> Vec<Lit> {
		let _ = propagated_lit;
		Vec::new()
	}

	/// Method to ask whether there is an external clause to add to the solver.
	fn add_external_clause(
		&mut self,
		slv: &mut dyn SolvingActions,
	) -> Option<(Vec<Lit>, ClausePersistence)> {
		let _ = slv;
		None
	}

	/// Method to help access to the propagator when given to the solver.
	///
	/// See [`PropagatingSolver::propagator`].
	///
	/// # Note
	///
	/// This method can generally be implemented as
	/// ```rust
	/// use std::any::Any;
	/// use pindakaas::solver::Propagator;
	///
	/// struct A;
	///
	/// impl Propagator for A {
	///   fn as_any(&self) -> &dyn Any {
	///     self
	///   }
	///
	/// #  fn as_mut_any(&mut self) -> &mut dyn Any { self }
	/// }
	///
	/// ```
	fn as_any(&self) -> &dyn Any;

	/// Method to help access to the propagator when given to the solver.
	///
	/// See [`PropagatingSolver::propagator`].
	///
	/// # Note
	///
	/// This method can generally be implemented as
	/// ```rust
	/// use std::any::Any;
	/// use pindakaas::solver::Propagator;
	///
	/// struct A;
	///
	/// impl Propagator for A {
	///   fn as_mut_any(&mut self) -> &mut dyn Any {
	///     self
	///   }
	/// #  fn as_any(&self) -> &dyn Any { self }
	/// }
	///
	/// ```
	fn as_mut_any(&mut self) -> &mut dyn Any;
}

/// Access the external propagator given the to solver
pub trait PropagatorAccess {
	/// Access the external propagator given the to solver
	///
	/// This method will return [`None`] if no propagator is set, or if the
	/// propagator is not of type [`P`].
	fn propagator<P: Propagator + 'static>(&self) -> Option<&P>;
}

pub(crate) struct PropagatorPointer {
	ptr: FFIPointer,
	pub(crate) access_prop: fn(*mut c_void) -> *mut dyn Any,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// A representation of a search decision made by a propagator.
pub enum SearchDecision {
	/// Leave the search decision to the solver.
	Free,
	/// Make the decision to assign the given literal.
	Assign(Lit),
	/// Force the solver to backtrack to the given decision level.
	Backtrack(usize),
}

/// A trait containing the solver methods that are exposed to the propagator
/// during solving.
pub trait SolvingActions {
	fn new_var(&mut self) -> Var;
	fn add_observed_var(&mut self, var: Var);
	fn is_decision(&mut self, lit: Lit) -> bool;
}

pub(crate) unsafe extern "C" fn ipasir_add_external_clause_lit_cb<
	P: Propagator,
	A: SolvingActions,
>(
	state: *mut c_void,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let Some(queue) = &mut prop.cqueue else {
		debug_assert!(false);
		// "has_clause" should have been called first and should have returned true.
		// Just return 0 to signal empty clause.
		return 0;
	};
	if let Some(l) = queue.pop_front() {
		l.0.get()
	} else {
		prop.cqueue = None;
		0 // End of clause
	}
}

pub(crate) unsafe extern "C" fn ipasir_add_reason_clause_lit_cb<
	P: Propagator,
	A: SolvingActions,
>(
	state: *mut c_void,
	propagated_lit: i32,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let lit = Lit(NonZeroI32::new(propagated_lit).unwrap());
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

pub(crate) unsafe extern "C" fn ipasir_check_model_cb<P: Propagator, A: SolvingActions>(
	state: *mut c_void,
	model: *const i32,
	len: usize,
) -> bool {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let sol = if len > 0 {
		std::slice::from_raw_parts(model, len)
	} else {
		&[]
	};
	let sol: rustc_hash::FxHashMap<Var, bool> = sol
		.iter()
		.map(|&i| (Var(NonZeroI32::new(i.abs()).unwrap()), i >= 0))
		.collect();
	let value = |l: Lit| sol.get(&l.var()).copied().unwrap_or(false);
	prop.prop.check_model(&mut prop.slv, &value)
}

pub(crate) unsafe extern "C" fn ipasir_decide_cb<P: Propagator, A: ExtendedSolvingActions>(
	state: *mut c_void,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let slv = &mut prop.slv;
	match prop.prop.decide(slv) {
		SearchDecision::Assign(lit) => lit.0.into(),
		SearchDecision::Backtrack(level) => {
			slv.force_backtrack(level);
			0
		}
		SearchDecision::Free => 0,
	}
}

pub(crate) unsafe extern "C" fn ipasir_has_external_clause_cb<P: Propagator, A: SolvingActions>(
	state: *mut c_void,
	is_forgettable: *mut bool,
) -> bool {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	if let Some((clause, p)) = prop.prop.add_external_clause(&mut prop.slv) {
		*is_forgettable = p == ClausePersistence::Forgettable;
		prop.cqueue = Some(clause.into());
	}
	prop.cqueue.is_some()
}

pub(crate) unsafe extern "C" fn ipasir_notify_assignments_cb<P: Propagator, A>(
	state: *mut c_void,
	lits: *const i32,
	len: usize,
) {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	if len > 0 {
		let lits = std::slice::from_raw_parts(lits as *mut Lit, len);
		prop.prop.notify_assignments(lits);
	};
}

pub(crate) unsafe extern "C" fn ipasir_notify_backtrack_cb<P: Propagator, A>(
	state: *mut c_void,
	level: usize,
	restart: bool,
) {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	prop.pqueue.clear();
	prop.explaining = None;
	prop.rqueue.clear();
	prop.cqueue = None;
	prop.prop.notify_backtrack(level, restart);
}

pub(crate) unsafe extern "C" fn ipasir_notify_new_decision_level_cb<P: Propagator, A>(
	state: *mut c_void,
) {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	prop.prop.notify_new_decision_level();
}

pub(crate) unsafe extern "C" fn ipasir_notify_persistent_assignments_cb<P: Propagator, A>(
	state: *mut c_void,
	lit: i32,
) {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let lit = Lit(NonZeroI32::new(lit).unwrap());
	prop.prop.notify_persistent_assignment(lit);
}

pub(crate) unsafe extern "C" fn ipasir_propagate_cb<P: Propagator, A: SolvingActions>(
	state: *mut c_void,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	if prop.pqueue.is_empty() {
		let slv = &mut prop.slv;
		prop.pqueue = prop.prop.propagate(slv).into();
	}
	if let Some(l) = prop.pqueue.pop_front() {
		l.0.into()
	} else {
		0 // No propagation
	}
}

impl<P, A> IpasirPropStore<P, A> {
	pub(crate) fn new(prop: P, slv: A) -> Self {
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

impl PropagatorPointer {
	pub(crate) unsafe fn access_propagator<P: 'static>(&self) -> Option<&P> {
		(*(self.access_prop)(self.get_raw_ptr())).downcast_ref::<P>()
	}

	pub(crate) unsafe fn access_propagator_mut<P: 'static>(&self) -> Option<&mut P> {
		(*(self.access_prop)(self.get_raw_ptr())).downcast_mut::<P>()
	}

	pub(crate) fn get_raw_ptr(&self) -> *mut c_void {
		self.ptr.get_ptr()
	}

	pub(crate) fn new<P, A>(prop: P, slv: A) -> Self
	where
		P: Propagator + 'static,
		A: ExtendedSolvingActions + 'static,
	{
		// Construct wrapping structures
		let store = IpasirPropStore::new(prop, slv);
		let prop = FFIPointer::new(store);
		let access_prop = |x: *mut c_void| -> *mut dyn Any {
			// SAFETY: The pointer is known to be created using
			// Box::<IpasirPropStore<P, A>>::leak()
			let store = unsafe { &mut *(x as *mut IpasirPropStore<P, A>) };
			&mut store.prop
		};
		Self {
			ptr: prop,
			access_prop,
		}
	}
}
