use crate::{int::helpers::Format, BddEncoder, Comparator, Encoder, Unsatisfiable};
use itertools::Itertools;
use std::{
	cell::RefCell,
	collections::{BTreeSet, HashMap},
	rc::Rc,
};

use iset::IntervalMap;

use crate::{
	int::{TernLeConstraint, TernLeEncoder},
	ClauseDatabase, Coefficient, Literal,
};

use super::{enc::GROUND_BINARY_AT_LB, IntVarBin, IntVarEnc, IntVarOrd};

// TODO usize -> intId struct

// TODO should we keep IntVar i/o IntVarEnc?
#[derive(Debug)]
pub struct Model<Lit: Literal, C: Coefficient> {
	pub(crate) vars: HashMap<usize, IntVarEnc<Lit, C>>,
	pub(crate) cons: Vec<Lin<C>>,
	pub(crate) num_var: usize,
	pub(crate) obj: Obj<C>,
}

// TODO Domain will be used once (/if) this is added as encoder feature.
#[allow(dead_code)]
#[derive(Default, Clone, PartialEq)]
pub enum Consistency {
	None,
	#[default]
	Bounds,
	Domain,
}

#[derive(Debug, Clone)]
pub enum Obj<C: Coefficient> {
	Minimize(LinExp<C>),
	Maximize(LinExp<C>),
	Satisfy,
}

use crate::{CheckError, Checker};

impl<Lit: Literal, C: Coefficient> Checker for Model<Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let a = self
			.vars
			.iter()
			.flat_map(|(id, x)| x.assign(solution).map(|a| (*id, a)))
			.collect::<HashMap<_, _>>();
		self.cons.iter().try_for_each(|con| con.check::<Lit>(&a))
	}
}

impl<Lit: Literal, C: Coefficient> Default for Model<Lit, C> {
	fn default() -> Self {
		Self {
			vars: HashMap::new(),
			cons: vec![],
			num_var: 0,
			obj: Obj::Satisfy,
		}
	}
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	pub fn new(num_var: usize) -> Self {
		Self {
			num_var,
			..Self::default()
		}
	}

	pub(crate) fn add_int_var_enc(
		&mut self,
		x: IntVarEnc<Lit, C>,
	) -> Result<Rc<RefCell<IntVar<C>>>, Unsatisfiable> {
		let dom = x
			.dom()
			.iter(..)
			.map(|d| d.end - C::one())
			.collect::<Vec<_>>();
		let var = self.new_var(&dom, false, None)?;
		self.vars.insert(var.borrow().id, x);
		Ok(var)
	}

	pub fn new_var(
		&mut self,
		dom: &[C],
		add_consistency: bool,
		lbl: Option<String>,
	) -> Result<Rc<RefCell<IntVar<C>>>, Unsatisfiable> {
		(!dom.is_empty())
			.then(|| {
				self.num_var += 1;
				Rc::new(RefCell::new(IntVar {
					id: self.num_var,
					dom: dom.iter().cloned().collect(),
					add_consistency,
					views: HashMap::default(),
					lbl,
				}))
			})
			.ok_or(Unsatisfiable)
	}

	pub fn add_constraint(&mut self, constraint: Lin<C>) -> crate::Result {
		self.cons.push(constraint);
		Ok(())
	}

	pub fn new_constant(&mut self, c: C) -> Rc<RefCell<IntVar<C>>> {
		self.new_var(&[c], false, None).unwrap()
	}

	// TODO pass Decomposer (with cutoff, etc..)
	pub fn decompose(&self) -> Result<Model<Lit, C>, Unsatisfiable> {
		// TODO aggregate constants + encode trivial constraints
		let mut model = Model::new(self.num_var);
		model.vars = self.vars.clone(); // TODO we should design the interaction between the model (self) and the decomposed model better (by consuming self?)
		model.cons = self
			.cons
			.iter()
			.cloned()
			.map(|con| -> Result<Vec<_>, Unsatisfiable> {
				match &con.exp.terms[..] {
					[] => Ok(vec![]),
					[term] => {
						match con.cmp {
							Comparator::LessEq => {
								term.x.borrow_mut().le(&C::zero());
							}
							Comparator::Equal => {
								term.x.borrow_mut().fix(&C::zero())?;
							}
							Comparator::GreaterEq => {
								term.x.borrow_mut().ge(&C::zero());
							}
						};
						todo!("Untested code: fixing of vars from unary constraints");
						// Ok(vec![])
					}
					[x, y] => Ok(vec![Lin::new(
						&[x.clone(), y.clone()],
						con.cmp,
						C::zero(),
						None,
					)]),
					_ if con.is_tern() => Ok(vec![con]),
					_ => {
						let new_model =
							BddEncoder::default().decompose::<Lit>(con, model.num_var)?;
						model.vars.extend(new_model.vars);
						Ok(new_model.cons)
					}
				}
			})
			.flatten_ok()
			.flatten()
			.collect::<Vec<_>>();
		Ok(model)
	}

	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		cutoff: Option<C>,
	) -> Result<Self, Unsatisfiable> {
		// Create decomposed model and its aux vars
		let mut decomposition = self.decompose()?;

		// Encode (or retrieve encoded) variables (in order of id)
		let mut all_views = HashMap::new();
		let enc_vars = decomposition
			.vars()
			.iter()
			.filter(|var| !var.borrow().is_constant())
			.sorted_by_key(|var| var.borrow().id)
			.map(|var| {
				(
					var.borrow().id,
					self.vars
						.entry(var.borrow().id)
						.or_insert_with(|| {
							var.borrow().encode(
								db,
								&mut all_views,
								var.borrow().prefer_order(cutoff),
							)
						})
						.clone(),
				)
			})
			.collect::<HashMap<_, _>>();

		for con in &decomposition.cons {
			let Lin {
				exp: LinExp { terms },
				cmp,
				k,
				..
			} = con;

			assert!(terms.len() == 3 && k.is_zero(), "{decomposition}");

			// Get term's variable's base encoding
			let terms = terms
				.iter()
				.map(|term| {
					let x = term.x.borrow();
					(
						term.c,
						if x.is_constant() {
							x.encode(db, &mut all_views, x.prefer_order(cutoff))
						} else {
							enc_vars[&x.id].clone()
						},
					)
				})
				.collect::<Vec<_>>();

			// Apply coefficient
			let mut process_c = |i: usize, to_rhs: bool| {
				terms[i]
					.1
					.multiply(db, if to_rhs { -terms[i].0 } else { terms[i].0 })
			};

			let x = process_c(0, false);
			let y = process_c(1, false);
			let z = process_c(2, true);

			TernLeEncoder::default()
				.encode(db, &TernLeConstraint::new(&x, &y, cmp, &z))
				.unwrap();
		}

		decomposition.vars = enc_vars;
		Ok(decomposition)
	}

	pub fn propagate(&mut self, consistency: &Consistency) {
		// TODO for Gt/Bdd we actually know we can start propagation at the last constraint
		let mut queue = BTreeSet::from_iter(0..self.cons.len());
		if consistency == &Consistency::None {
			return;
		}
		while let Some(con) = queue.pop_last() {
			let changed = self.cons[con].propagate(consistency);
			queue.extend(self.cons.iter().enumerate().filter_map(|(i, con)| {
				con.exp
					.terms
					.iter()
					.any(|term| changed.contains(&term.x.borrow().id))
					.then_some(i)
			}));
		}
	}

	pub(crate) fn extend(&mut self, other: Model<Lit, C>) {
		// TODO potentially, we could increment the other var ids by self.num_var here
		self.vars.extend(other.vars);
		self.num_var = other.num_var;
		self.cons.extend(other.cons);
	}
	pub(crate) fn vars(&self) -> Vec<Rc<RefCell<IntVar<C>>>> {
		self.cons
			.iter()
			.flat_map(|con| {
				con.exp
					.terms
					.iter()
					.filter_map(|term| (!term.x.borrow().is_constant()).then(|| term.x.clone()))
			})
			.unique_by(|x| x.borrow().id)
			.collect()
	}
}

#[derive(Debug, Clone)]
pub struct LinExp<C: Coefficient> {
	pub(crate) terms: Vec<Term<C>>,
}

#[derive(Debug, Clone)]
pub struct Lin<C: Coefficient> {
	pub exp: LinExp<C>,
	pub cmp: Comparator,
	pub k: C,
	pub lbl: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Term<C: Coefficient> {
	pub c: C,
	pub x: Rc<RefCell<IntVar<C>>>,
}

impl<C: Coefficient> From<Rc<RefCell<IntVar<C>>>> for Term<C> {
	fn from(value: Rc<RefCell<IntVar<C>>>) -> Self {
		Term::new(C::one(), value)
	}
}

impl<C: Coefficient> Term<C> {
	pub fn new(c: C, x: Rc<RefCell<IntVar<C>>>) -> Self {
		Self { c, x }
	}

	pub fn lb(&self) -> C {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().ub()
			} else {
				self.x.borrow().lb()
			})
	}

	pub(crate) fn ub(&self) -> C {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().lb()
			} else {
				self.x.borrow().ub()
			})
	}

	// TODO [?] correct way to return iter?
	pub(crate) fn dom(&self) -> Vec<C> {
		self.x.borrow().dom.iter().map(|d| self.c * *d).collect()
	}

	pub(crate) fn size(&self) -> usize {
		self.x.borrow().size()
	}
}

impl<C: Coefficient> Lin<C> {
	pub fn new(terms: &[Term<C>], cmp: Comparator, k: C, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: terms.to_vec(),
			},
			cmp,
			k,
			lbl,
		}
	}

	pub fn tern(x: Term<C>, y: Term<C>, cmp: Comparator, z: Term<C>, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: vec![x, y, Term::new(-z.c, z.x)],
			},
			cmp,
			k: C::zero(),
			lbl,
		}
	}

	pub fn lb(&self) -> C {
		self.exp.terms.iter().map(Term::lb).fold(C::zero(), C::add)
	}

	pub fn ub(&self) -> C {
		self.exp.terms.iter().map(Term::ub).fold(C::zero(), C::add)
	}

	pub(crate) fn propagate(&mut self, consistency: &Consistency) -> Vec<usize> {
		let mut changed = vec![];
		match consistency {
			Consistency::None => unreachable!(),
			Consistency::Bounds => loop {
				let mut fixpoint = true;
				if self.cmp == Comparator::Equal {
					let xs_ub = self.ub() - self.k;
					for term in &self.exp.terms {
						let mut x = term.x.borrow_mut();
						let size = x.size();

						let id = x.id;
						let x_ub = if term.c.is_positive() {
							*x.dom.last().unwrap()
						} else {
							*x.dom.first().unwrap()
						};

						// c*d >= x_ub*c + xs_ub := d >= x_ub - xs_ub/c
						let b = x_ub - (xs_ub / term.c);

						if !term.c.is_negative() {
							x.ge(&b);
						} else {
							x.le(&b);
						}

						if x.size() < size {
							changed.push(id);
							fixpoint = false;
						}
						assert!(x.size() > 0);
					}
				}

				let rs_lb = self.lb() - self.k;
				for term in &self.exp.terms {
					let mut x = term.x.borrow_mut();
					let size = x.size();
					let x_lb = if term.c.is_positive() {
						*x.dom.first().unwrap()
					} else {
						*x.dom.last().unwrap()
					};

					let id = x.id;

					// c*d <= c*x_lb - rs_lb
					// d <= x_lb - (rs_lb / c) (or d >= .. if d<0)
					let b = x_lb - (rs_lb / term.c);

					if term.c.is_negative() {
						x.ge(&b);
					} else {
						x.le(&b);
					}

					if x.size() < size {
						//println!("Pruned {}", size - x.size());
						changed.push(id);
						fixpoint = false;
					}
					assert!(x.size() > 0);
				}

				if fixpoint {
					return changed;
				}
			},
			Consistency::Domain => {
				assert!(self.cmp == Comparator::Equal);
				loop {
					let mut fixpoint = true;
					for (i, term) in self.exp.terms.iter().enumerate() {
						let id = term.x.borrow().id;
						term.x.borrow_mut().dom.retain(|d_i| {
							if self
								.exp
								.terms
								.iter()
								.enumerate()
								.filter_map(|(j, term_j)| {
									(i != j).then(|| {
										term_j
											.x
											.borrow()
											.dom
											.iter()
											.map(|d_j_k| term_j.c * *d_j_k)
											.collect::<Vec<_>>()
									})
								})
								.multi_cartesian_product()
								.any(|rs| {
									term.c * *d_i + rs.into_iter().fold(C::zero(), |a, b| a + b)
										== C::zero()
								}) {
								true
							} else {
								fixpoint = false;
								changed.push(id);
								false
							}
						});
						assert!(term.x.borrow().size() > 0);
					}

					if fixpoint {
						return changed;
					}
				}
			}
		}
	}

	pub(crate) fn is_tern(&self) -> bool {
		let cs = self.exp.terms.iter().map(|term| term.c).collect::<Vec<_>>();
		cs[0].is_positive() && cs[1].is_positive() && cs[2].is_negative() && self.k.is_zero()
	}

	fn check<Lit: Literal>(&self, a: &HashMap<usize, C>) -> Result<(), CheckError<Lit>> {
		let lhs = self
			.exp
			.terms
			.iter()
			.map(|term| term.c * a[&term.x.borrow().id])
			.fold(C::zero(), C::add);

		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

// TODO perhaps id can be used by replacing vars HashMap to just vec
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct IntVar<C: Coefficient> {
	pub(crate) id: usize,
	pub(crate) dom: BTreeSet<C>, // TODO implement rangelist
	pub(crate) add_consistency: bool,
	pub(crate) views: HashMap<C, (usize, C)>,
	lbl: Option<String>,
}

impl<C: Coefficient> IntVar<C> {
	pub fn is_constant(&self) -> bool {
		self.size() == 1
	}

	fn encode<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		views: &mut HashMap<(usize, C), DB::Lit>,
		prefer_order: bool,
	) -> IntVarEnc<DB::Lit, C> {
		if self.is_constant() {
			IntVarEnc::Const(*self.dom.first().unwrap())
		} else {
			let x = if prefer_order {
				let dom = self
					.dom
					.iter()
					.sorted()
					.cloned()
					.tuple_windows()
					.map(|(a, b)| (a + C::one())..(b + C::one()))
					.map(|v| (v.clone(), views.get(&(self.id, v.end - C::one())).cloned()))
					.collect::<IntervalMap<_, _>>();
				IntVarEnc::Ord(IntVarOrd::from_views(db, dom, "x".to_string()))
			} else {
				let y = IntVarBin::from_bounds(
					db,
					*self.dom.first().unwrap(),
					*self.dom.last().unwrap(),
					"x".to_string(),
				);
				IntVarEnc::Bin(y)
			};

			if self.add_consistency {
				x.consistent(db).unwrap();
			}

			for view in self
				.views
				.iter()
				.map(|(c, (id, val))| ((*id, *val), x.geq(*c..(*c + C::one()))))
			{
				// TODO refactor
				if !view.1.is_empty() {
					views.insert(view.0, view.1[0][0].clone());
				}
			}
			x
		}
	}

	pub(crate) fn dom(&self) -> std::collections::btree_set::Iter<C> {
		self.dom.iter()
	}

	// TODO should not be C i/o &C?
	fn fix(&mut self, q: &C) -> crate::Result {
		if self.dom.contains(q) {
			self.dom = [*q].into();
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}

	fn ge(&mut self, bound: &C) {
		self.dom = self.dom.split_off(bound);
	}

	fn le(&mut self, bound: &C) {
		self.dom.split_off(&(*bound + C::one()));
	}

	pub(crate) fn size(&self) -> usize {
		self.dom.len()
	}

	pub(crate) fn lb(&self) -> C {
		*self.dom.first().unwrap()
	}

	pub(crate) fn ub(&self) -> C {
		*self.dom.last().unwrap()
	}

	pub fn required_bits(lb: C, ub: C) -> u32 {
		if GROUND_BINARY_AT_LB {
			C::zero().leading_zeros() - ((ub - lb).leading_zeros())
		} else {
			C::zero().leading_zeros() - (ub.leading_zeros())
		}
	}

	fn prefer_order(&self, cutoff: Option<C>) -> bool {
		match cutoff {
			None => true,
			Some(cutoff) if cutoff == C::zero() => false,
			Some(cutoff) => C::from(self.dom.len()).unwrap() < cutoff,
		}
	}

	pub fn lbl(&self) -> String {
		self.lbl.clone().unwrap_or_else(|| format!("x{}", self.id))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{helpers::tests::TestDB, int::model::Format, Cnf, Lin, Model};

	impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
		fn check_assignment(&self, assignment: &HashMap<usize, C>) -> Result<(), CheckError<Lit>> {
			self.cons
				.iter()
				.try_for_each(|con| con.check::<Lit>(assignment))
		}
	}

	#[test]
	fn model_test() {
		let mut model = Model::<i32, i32>::default();
		let x1 = model
			.new_var(&[0, 2], true, Some("x1".to_string()))
			.unwrap();
		let x2 = model
			.new_var(&[0, 3], true, Some("x2".to_string()))
			.unwrap();
		let x3 = model
			.new_var(&[0, 5], true, Some("x3".to_string()))
			.unwrap();
		let k = 6;
		model
			.add_constraint(Lin::new(
				&[Term::new(1, x1), Term::new(1, x2), Term::new(1, x3)],
				Comparator::LessEq,
				k,
				Some(String::from("c1")),
			))
			.unwrap();
		let mut cnf = Cnf::new(0);
		// model.propagate(&Consistency::Bounds);
		model.encode(&mut cnf, None).unwrap();
	}

	macro_rules! lp_test_case {
		($lp:expr) => {
			use super::*; // TODO why is this not necessary for linear_test_suite?

			#[test]
			fn test() {
				let mut model = Model::<i32, i32>::from_string($lp.into(), Format::Lp).unwrap();
				// let mut cnf = Cnf::new(0);
				// let vars = decomp_model.vars();

				let vars = model.vars();
				let sols = vars
					.iter()
					.map(|var| var.borrow().dom.clone().into_iter().collect::<Vec<_>>())
					.multi_cartesian_product()
					.map(|a| {
						vars.iter()
							.map(|var| var.borrow().id.clone())
							.zip(a)
							.collect::<HashMap<_, _>>()
					})
					.filter(|a| model.check_assignment(a).is_ok())
					.collect::<Vec<_>>();

				let mut db = TestDB::new(0);
				let decomposition = model.encode(&mut db, None).unwrap();
				println!("decomposition = {decomposition}");

				// Count principal variables
				let principal_enc_vars = vars
					.iter()
					.map(|var| (var.borrow().id, &decomposition.vars[&var.borrow().id]))
					.collect::<HashMap<_, _>>();

				db.num_var = principal_enc_vars
					.iter()
					.map(|(_, var)| var.lits())
					.sum::<usize>() as i32;

				let lit_assignments = db.solve().into_iter().sorted().collect::<Vec<_>>();

				let int_assignments = lit_assignments
					.iter()
					.flat_map(|lit_assignment| {
						let int_assignment = principal_enc_vars
							.iter()
							.flat_map(|(id, var)| var.assign(&lit_assignment).map(|a| (*id, a)))
							.collect::<HashMap<_, _>>();

						// Check principal constraints
						model
							.check_assignment(&int_assignment)
							.map(|_| int_assignment)
					})
					.collect::<Vec<_>>();

				let extra_int_assignments = int_assignments
					.iter()
					.filter(|a| !sols.contains(a))
					.cloned()
					.collect::<Vec<_>>();

				let missing_int_assignments = sols
					.iter()
					.filter(|a| !int_assignments.contains(a))
					.cloned()
					.collect::<Vec<_>>();

				fn show_int_assignments(a: &Vec<HashMap<usize, i32>>) -> Vec<String> {
					a.iter()
						.map(|a| {
							a.iter()
								.sorted()
								.map(|(id, a)| format!("x_{id}={a}"))
								.join(", ")
						})
						.collect()
				}

				assert!(
					extra_int_assignments.is_empty() && missing_int_assignments.is_empty(),
					"
Extra solutions:
{}
Missing solutions:
{}",
					show_int_assignments(&extra_int_assignments)
						.iter()
						.map(|a| format!("+ {a}"))
						.join("\n"),
					show_int_assignments(&missing_int_assignments)
						.iter()
						.map(|a| format!("- {a}"))
						.join("\n"),
				);

				assert_eq!(int_assignments, sols);
			}
		};
	}

	mod lp_1 {
		lp_test_case!(
			r"
Subject To
  c0: + 2 x1 + 3 x2 + 5 x3 <= 6
Binary
  x1
  x2
  x3
End
"
		);
	}

	mod lp_2 {
		lp_test_case!(
			r"
Subject To
  c0: + 2 x1 + 3 x2 + 5 x3 >= 6
Binary
  x1
  x2
  x3
End
"
		);
	}

	/*
		mod soh {
			lp_test_case!(
				r"
	Subject To
	\ c0: + 1 x1 - 1 x3 >= 0
	\ c1: + 1 x2 - 1 x4 >= 0
	  c2: + 1 x1 + 1 x2 - 1 x3 - 1 x4 <= -1
	Bounds
	  0 <= x1 <= 5
	  0 <= x2 <= 5
	  0 <= x3 <= 5
	  0 <= x4 <= 5
	End
	"
			);
		}
		*/
}
