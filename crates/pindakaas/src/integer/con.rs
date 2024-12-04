use crate::helpers::{emit_clause, unsigned_binary_range};
use crate::integer::term::Term;
use crate::integer::var::IntVarId;
use crate::integer::Format;
use crate::integer::{lex_geq_const, rca, var::IntVarRef};
use crate::{bool_linear::Comparator, integer::lex_leq_const};
use crate::{log, CheckError};
use itertools::Itertools;

use super::enc::IntVarEnc;
use super::model::{Consistency, Model, ModelConfig, USE_COUPLING_IO_LEX, VIEW_COUPLING};
use crate::{
	bool_linear::PosCoeff,
	helpers::{add_clauses_for, div_ceil, div_floor},
	integer::{
		bin::BinEnc,
		helpers::{display_cnf, required_lits},
		Assignment, Dom,
	},
	ClauseDatabase, Coeff, Lit, Result, Unsatisfiable,
};

#[derive(Debug, Clone, Default)]
pub struct LinExp {
	pub terms: Vec<Term>,
}

#[derive(Debug, Clone)]
pub struct Lin {
	pub exp: LinExp,
	pub cmp: Comparator,
	pub k: Coeff,
	pub lbl: Option<String>,
}

pub(crate) enum LinCase {
	Couple(Term, Term),
	Fixed(Lin),
	Unary(Term, Comparator, Coeff),
	Binary(Term, Comparator, Term), // just for binary ineqs
	Scm(Term, IntVarRef),
	Rca(Term, Term, Term),
	Order,
	Other,
}

impl TryFrom<&Lin> for LinCase {
	type Error = Unsatisfiable;

	fn try_from(con: &Lin) -> Result<Self, Unsatisfiable> {
		let term_encs = con
			.exp
			.terms
			.iter()
			.map(|t| (t, t.x.borrow().e.clone()))
			.collect_vec();

		Ok(match (&term_encs[..], con.cmp, con.k) {
			([], _, _) => LinCase::Fixed(con.clone()),
			([(t, Some(IntVarEnc::Bin(_)))], cmp, _)
				if (t.c == 1
					|| t.c % 2 == 0) // multiple of 2
                    && !USE_COUPLING_IO_LEX =>
			{
				LinCase::Unary((*t).clone().encode_bin(None, cmp, None)?, cmp, con.k)
			}
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_)))],
				Comparator::LessEq | Comparator::GreaterEq,
				0,
			) => LinCase::Binary((*x).clone(), con.cmp, (*y).clone()),
			// VIEW COUPLING
			// TODO this makes single literal comparisons views if possible
			// ([(t, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(None)))], _)
			// // | ([(y, Some(IntVarEnc::Bin(None))), (t, Some(IntVarEnc::Ord(_)))], _)
			// 	if y.c == -1
			// 		&& t.x.borrow().dom.size() <= 2
			// 		&& VIEW_COUPLING =>
			// {
			// 	// t.x.borrow_mut().encode(db, None)?;
			// 	// // let view = (*t).clone().encode_bin(None, self.cmp, None)?;
			// 	// let view = (*t).clone().encode_bin(None, self.cmp, None)?;
			// 	// y.x.borrow_mut().e = view.0.x.borrow().e.clone();
			// 	// Ok(())
			// }
			// SCM
			(
				[(t_x, Some(IntVarEnc::Bin(_))), (Term { c: -1, x: y }, Some(IntVarEnc::Bin(_)))]
				| [(Term { c: -1, x: y }, Some(IntVarEnc::Bin(_))), (t_x, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
				0,
			) if matches!(y.borrow().e, Some(IntVarEnc::Bin(_))) => LinCase::Scm((*t_x).clone(), y.clone()),
			([(t, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(_)))], _, 0)
				if y.c == -1 && VIEW_COUPLING =>
			{
				LinCase::Couple((*t).clone(), (*y).clone())
			}
			// ([(x, Some(IntVarEnc::Bin(_)))], Comparator::Equal, k) => {
			// 	LinCase::Rca((*x).clone(), Term::from(0), Term::from(k))
			// }
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
				k,
			) => LinCase::Rca((*x).clone(), (*y).clone(), Term::from(-k)),
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_))), (z, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
				0,
			) if z.c.is_negative() => LinCase::Rca((*x).clone(), (*y).clone(), (*z).clone()),
			(encs, _, _)
				if encs
					.iter()
					.all(|e| matches!(e.1, Some(IntVarEnc::Ord(_)) | None)) =>
			{
				LinCase::Order
			}
			_ => LinCase::Other,
		})
	}
}

impl Lin {
	pub fn new(terms: &[Term], cmp: Comparator, k: Coeff, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: terms.to_vec(),
			},
			cmp,
			k,
			lbl,
		}
	}

	pub fn tern(x: Term, y: Term, cmp: Comparator, z: Term, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: vec![x, y, Term::new(-z.c, z.x)],
			},
			cmp,
			k: 0,
			lbl,
		}
	}

	pub fn lb(&self) -> Coeff {
		self.exp.terms.iter().map(Term::lb).sum()
	}

	pub fn ub(&self) -> Coeff {
		self.exp.terms.iter().map(Term::ub).sum()
	}

	pub fn propagate(&mut self, consistency: &Consistency) -> Result<Vec<IntVarId>, Unsatisfiable> {
		let mut changed = vec![];
		match consistency {
			Consistency::None => unreachable!(),
			Consistency::Bounds => loop {
				let mut fixpoint = true;
				self.cmp.split().into_iter().try_for_each(|cmp| {
					match cmp {
						Comparator::LessEq => {
							let rs_lb = self.lb() - self.k;
							for term in &self.exp.terms {
								let mut x = term.x.borrow_mut();
								let size = x.size();
								let x_lb = if term.c.is_positive() {
									x.dom.lb()
								} else {
									x.dom.ub()
								};

								let id = x.id;

								// c*d <= c*x_lb - rs_lb
								// d <= x_lb - (rs_lb / c) (or d >= .. if d<0)
								let b = x_lb - (rs_lb / term.c);

								if term.c.is_negative() {
									x.ge(b);
								} else {
									x.le(b);
								}

								if x.size() < size {
									log!("Pruned {}", size - x.size());
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == 0 {
									return Err(Unsatisfiable);
								}
							}
							Ok(())
						}
						Comparator::GreaterEq => {
							let xs_ub = self.ub() - self.k;
							for term in &self.exp.terms {
								let mut x = term.x.borrow_mut();
								let size = x.size();

								let id = x.id;
								let x_ub = if term.c.is_positive() {
									x.dom.ub()
								} else {
									x.dom.lb()
								};

								// c*d >= x_ub*c + xs_ub := d >= x_ub - xs_ub/c
								let b = x_ub - (xs_ub / term.c);

								if !term.c.is_negative() {
									x.ge(b);
								} else {
									x.le(b);
								}

								if x.size() < size {
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == 0 {
									return Err(Unsatisfiable);
								}
							}
							Ok(())
						}
						_ => unreachable!(),
					}
				})?;

				if fixpoint {
					return Ok(changed);
				}
			},
			Consistency::Domain => {
				todo!(
					"TODO: (super naive) Domain consistency propagator is not tested. Maybe remove"
				)
				/*
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
									term.c * *d_i + rs.into_iter().sum()
										== 0
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
				*/
			}
		}
	}

	pub(crate) fn is_tern(&self) -> bool {
		let cs = self.exp.terms.iter().map(|term| term.c).collect::<Vec<_>>();
		cs.len() == 3 && cs[2] == -1 && self.k == 0
	}

	pub(crate) fn check(&self, assignment: &Assignment) -> Result<(), CheckError> {
		let lhs = self
			.exp
			.terms
			.iter()
			.map(|term| {
				term.c
					* assignment.value(&term.x.borrow()).unwrap_or_else(|| {
						panic!("Expected {} to be assigned in {}", term, assignment)
					})
			})
			.sum::<Coeff>();

		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			const SHOW_LP: bool = false;
			Err(CheckError::Fail(format!(
				"Inconsistency in {}: {} == {} !{} {}\n{} (A = {assignment})",
				self.lbl.clone().unwrap_or_default(),
				self.exp
					.terms
					.iter()
					.map(|term| {
						let (a, lits) = (
							assignment.value(&term.x.borrow()).unwrap(),
							assignment.sol(&term.x.borrow()),
						);
						format!(
							"{} * {}={} [{}] (={})",
							term.c,
							term.x.borrow().lbl(),
							a,
							lits.unwrap_or_default().unwrap_or_default(),
							term.c * a,
						)
					})
					.join(" + "),
				lhs,
				self.cmp,
				self.k,
				SHOW_LP
					.then(|| {
						Model {
							cons: vec![self.clone()],
							..Model::default()
						}
						.to_text(Format::Lp)
					})
					.unwrap_or_default()
			)))
		}
	}

	fn _is_simplified(&self) -> bool {
		self.exp
			.terms
			.iter()
			.all(|term| term.c != 0 && !term.x.borrow().is_constant())
	}

	#[cfg_attr(
		feature = "tracing",
		tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub fn encode<DB: ClauseDatabase>(&self, db: &mut DB, _config: &ModelConfig) -> Result {
		match LinCase::try_from(self)? {
			LinCase::Fixed(con) => con.check(&Assignment::default()).map_err(|_| Unsatisfiable),
			LinCase::Unary(x, cmp, k) => {
				// TODO refactor.....
				x.x.borrow_mut().encode_bin(db)?;
				let dom = x.x.borrow().dom.clone();
				let x = x.encode_bin(None, cmp, None)?;
				let x: IntVarRef = x.try_into().unwrap();
				let x_enc = x.clone().borrow_mut().encode_bin(db)?;
				x_enc.encode_unary_constraint(db, &cmp, k, &dom, false)
			}
			LinCase::Binary(t_x, cmp, t_y) => {
				// assert!(t_x.x.borrow().lb() == t_y.x.borrow().lb());

				let k = t_y.x.borrow().lb() - t_x.x.borrow().lb(); // used to make lbs match
				t_x.x.borrow_mut().encode_bin(db)?;
				t_y.x.borrow_mut().encode_bin(db)?;

				let x_enc = t_x.x.borrow_mut().encode_bin(db)?;
				let y_enc = (t_y * -1).x.borrow_mut().encode_bin(db)?;
				x_enc.lex(db, cmp, y_enc, k)
			}
			LinCase::Couple(t_x, t_y) => {
				t_x.x.borrow_mut().encode_ord(db)?;
				if !t_x.x.borrow().add_consistency {
					t_x.x.borrow_mut().consistent(db)?;
				}
				let y_enc = t_y.x.borrow_mut().encode_bin(db)?;

				match self.cmp {
					Comparator::LessEq | Comparator::GreaterEq => {
						let up = self.cmp == Comparator::GreaterEq;

						let (range_lb, range_ub) = y_enc.range();
						let dom = &t_y.x.borrow().dom;

						let mut xs = t_x
							.ineqs(up)
							.into_iter()
							.map(|(c, x, _)| (*y_enc.normalize((t_x.c * c) - self.k, dom), x))
							.collect_vec();

						if up {
							xs.reverse();
							xs.push((range_ub, vec![]));
						} else {
							xs.insert(0, (range_lb, vec![]));
						};

						xs.into_iter()
							.tuple_windows()
							.try_for_each(|((c_a, x_a), (c_b, x_b))| {
								let x = if up { x_a } else { x_b };
								let (c_a, c_b) = (c_a + 1, c_b);
								log!("{up} {c_a}..{c_b} -> {x:?}");
								let y = y_enc.ineqs(c_a, c_b, !up);
								log!("{y:?}");
								add_clauses_for(db, vec![vec![x.clone()], y])
							})
					}
					Comparator::Equal => {
						log!("CHANNEL: {t_x} = {t_y}");
						assert!(matches!(t_x.x.borrow().e, Some(IntVarEnc::Ord(_))));
						assert!(matches!(t_y.x.borrow().e, Some(IntVarEnc::Bin(_))));
						t_x.x.borrow_mut().encode_ord(db)?;
						t_x.x.borrow_mut().consistent(db)?; // channelling requires consitency on both vars
						let y_enc = t_y.x.borrow_mut().encode_bin(db)?;
						t_y.x.borrow_mut().consistent(db)?;

						let (range_lb, range_ub) = unsigned_binary_range(y_enc.bits());
						y_enc.x.iter().enumerate().try_for_each(|(i, &y_i)| {
							let r = Coeff::from(2).pow(i as u32);
							let (l, u) = ((*range_lb).div_euclid(r), (*range_ub).div_euclid(r));
							(l..=u).sorted_by_key(|k| *k).try_for_each(|k| {
								let y_i = if k % 2 == 0 { !y_i } else { y_i };
								let a = y_enc.denormalize(r * k, &t_y.x.borrow().dom); // x<a
								let b = a + r; // x>=b (next segment)
								let (a, b) = (a - 1, b); // not x>=a == x<a == x<=a-1, x>=b
								 // (x>=a /\ x<b) -> b = k%2
								 //   x<a \/ x>=b \/ b = k%2
								 //   x<=a-1 \/ x>=b \/ b = k%2 (note
								 // log!(
								 // 	"({t_x}<={a}) or ({t_x}>={b}) OR {y_i}"
								 // );
								let x_a = t_x.ineq(a, false, None);
								let x_b = t_x.ineq(b, true, None);
								log!("({t_x}<={a} = {x_a:?}) OR {y_i} OR ({t_x}>={b} = {x_b:?})");
								add_clauses_for(db, vec![x_a, y_i.into(), x_b])

								// if x_a == negate_cnf(x_b.clone()) && false {
								// 	None
								// } else {
								// 	Some(
								// 		dbg!([x_a, y_i.into(), x_b]
								// 			.into_iter()
								// 			.flatten()
								// 			.flatten()
								// 			.collect()), // .into_iter()
								// 		              // .multi_cartesian_product()
								// 		              // .concat()
								// 		              // .into_iter()
								// 		              // // .into_iter()
								// 		              // .flatten()
								// 		              // .collect())
								// 	)
								// }
							})
						})
					}
				}
			}
			LinCase::Scm(t_x, y) => {
				t_x.x.borrow_mut().encode_bin(db)?; // encode x (if not encoded already)
										// encode y

				let tmp_y = t_x.clone().encode_bin(None, self.cmp, None)?;

				// TODO make Term decompose and use encode_bin for actual encoding incl scm, but for now (since it's not given Db, call scm_dnf) here
				(*y).borrow_mut().e = Some(IntVarEnc::Bin(Some(
					tmp_y.x.borrow_mut().encode_bin(db)?.scm_dnf(db, tmp_y.c)?,
				)));
				// TODO handle if y is already encoded
				y.borrow_mut().dom = t_x.bounds();
				Ok(())
			}
			LinCase::Rca(x, y, z) => {
				assert!(
					x.lb() + y.lb() <= -z.ub(),
					"LBs for addition not matching: {self}"
				);

				log!("RCA: {x} + {y} + {z} = 0");
				let z: IntVarRef = (z * -1).try_into().expect("Expected unit term after -1*z");
				log!("RCA: {x} + {y} = {}", z.borrow());

				let (x, y) = &[x, y]
					.into_iter()
					.map(|t| {
						// encode term and return underlying var
						t.x.borrow_mut().encode(db).unwrap();
						let t = t.encode_bin(None, self.cmp, None).unwrap();
						let x: IntVarRef = t.clone().try_into().unwrap_or_else(|_| {
							panic!("Calling Term::encode_bin on {t} should return 1*y")
						});
						x
					})
					.collect_tuple()
					.unwrap();

				let w_ground = x.borrow().lb() + y.borrow().lb();
				let w_dom = Dom::from_bounds(w_ground, z.borrow().ub());
				let (x, y) = (
					x.borrow_mut().encode_bin(db)?.xs(),
					y.borrow_mut().encode_bin(db)?.xs(),
				);

				// if z is constant
				// x{0..2} + y{2..4} = 000 + 4 == x+y = 010 + 2
				if let Ok(c) = z.borrow().as_constant() {
					return rca(
						db,
						&x,
						&y,
						None,
						Some(&BinEnc::from(PosCoeff::new(c - w_ground)).xs()),
					)
					.map(|_| ());
				}
				// x{0..2} + y{2..4} = z{4..5}
				// x{0..2} + y{2..4} = z{2..3} + 2
				// x+y=w{2..ub(z)=5}, w=z
				let w_lb = z.borrow().lb();
				let lits = Some(required_lits(&w_dom));
				// x+y=w, w+lb(z)=z (knowing lb(w)<=lb(z))

				// TODO check whether z's domain is smaller, and/or already encoded.

				assert!(
					matches!(z.borrow().e, Some(IntVarEnc::Bin(None))),
					"Last var {} should not have been encoded yet",
					z.borrow()
				);

				// z=w if z unencoded, changing its domain and encoding to w
				z.borrow_mut().dom = w_dom; // fix lower bound to ground
				let z_bin = BinEnc::from_lits(&rca(db, &x, &y, lits, None).unwrap());

				lex_geq_const(
					db,
					&z_bin.xs(),
					PosCoeff::new(w_lb - w_ground),
					z_bin.bits(),
				)?;

				// TODO [!] only has to be done for last constraint of lin decomp.. (could add_consistency to differentiate?)
				lex_leq_const(
					db,
					&z_bin.xs(),
					PosCoeff::new(z.borrow().ub() - w_ground),
					z_bin.bits(),
				)?;
				z.borrow_mut().e = Some(IntVarEnc::Bin(Some(z_bin)));
				Ok(())
			}
			LinCase::Order => {
				// encode all variables
				self.exp
					.terms
					.iter()
					.try_for_each(|t| t.x.borrow_mut().encode(db).map(|_| ()))?;

				assert!(
					self.exp.terms.iter().all(|t| match t.x.borrow().e {
						Some(IntVarEnc::Ord(_)) => true,
						Some(IntVarEnc::Bin(_)) => t.x.borrow().dom.size() <= 2,
						_ => false,
					}),
					"Non-order: {self}"
				);

				const SORT_BY_COEF: bool = false;
				let terms = if SORT_BY_COEF {
					self.exp
						.terms
						.iter()
						.cloned()
						.sorted_by_key(|t| -t.c)
						.collect_vec()
				} else {
					self.exp.terms.clone()
				};

				self.cmp.split().into_iter().try_for_each(|cmp| {
					let (_, cnf) = Self::encode_rec(&terms, &cmp, self.k, 0);
					log!("{}", display_cnf(&cnf));

					for c in cnf {
						if c.is_empty() {
							return Err(Unsatisfiable);
						}
						emit_clause!(db, c)?;
					}
					Ok(())
				})
			}
			LinCase::Other => todo!("Cannot constrain: {self}\n{self:?}"),
		}

		/*
		   // TODO Support order-binary channelling
		// CHANNEL
		(
			[(t_x, Some(IntVarEnc::Ord(_))), (t_y, Some(IntVarEnc::Bin(_)))],
			Comparator::Equal,
		) if t_x.c.is_one() && t_y.c == -1 && USE_CHANNEL => {

		}
		*/
	}

	fn encode_rec(
		terms: &[Term],
		cmp: &Comparator,
		k: Coeff,
		_depth: usize,
	) -> (Option<Coeff>, Vec<Vec<Lit>>) {
		const LOOKAHEAD: bool = true;
		if let Some((head, tail)) = terms.split_first() {
			let up = head.c.is_positive() == (cmp == &Comparator::GreaterEq);
			if tail.is_empty() {
				let k_ = if up {
					div_ceil(k, head.c)
				} else {
					div_floor(k, head.c) + 1
				};

				log!(
					"{}{} ({}*{} {cmp} {k}) (= {} {} {k_})",
					"\t".repeat(_depth),
					if up { "up: " } else { "down: " },
					head.c,
					head.x.borrow(),
					head.x.borrow().lbl(),
					if head.c.is_positive() {
						*cmp
					} else {
						cmp.reverse()
					}
				);

				let (c, cnf) = head.x.borrow().ineq(k_, up, None);

				let _disp_cnf = display_cnf(&cnf); // TODO inlining this function won't be removed with feature trace
				log!("== {:?}", _disp_cnf);

				(c.map(|c| head.c * c), cnf)
			} else {
				let mut last_a = None; // last antecedent implies till here
				let mut last_k = None; // last consequent implies to here
				(
					None,
					head.ineqs(up)
						.into_iter()
						.map_while(|(d, conditions, implies)| {
							// l = x>=d+1, ~l = ~(x>=d+1) = x<d+1 = x<=d
							let k_ = k - head.c * d;

								log!(
									"{} {} {}*({} {cmp} {}) (->x{cmp}{implies}) = [{:?}] (k={k} - {}*{d} = {k_}) last_a={last_a:?} last_k={last_k:?}",
                                    "\t".repeat(_depth),
									if up {
										"up: "
									} else {
										"down: "
									},
									head.c,
									head.x.borrow(),
									if up { d + 1 } else { d },
									conditions,
									head.c
								);


							let antecedent_implies_next = last_a
								.map(|last_a| {
									if cmp == &Comparator::GreaterEq {
										d >= last_a
									} else {
										d <= last_a
									}
								})
								.unwrap_or_default();
							let consequent_implies_next = last_k
								.map(|last_k| {
									if cmp == &Comparator::GreaterEq {
                                        k_ <= last_k
                                    } else {
                                        k_ >= last_k
                                    }
								})
								.unwrap_or_default();

								log!(" {}/{} \n", antecedent_implies_next, consequent_implies_next);

							let (c, cnf) = Self::encode_rec(tail, cmp, k_, _depth + 1);
							let cnf = cnf
								.into_iter()
								.map(|r| conditions.clone().into_iter().chain(r).collect())
								.collect_vec();


							if antecedent_implies_next && consequent_implies_next  {
									return Some(vec![]); // some consequent -> skip clause
							}

                                                        if LOOKAHEAD {
                                                            last_k = c;
                                                            last_a = Some(implies);
                                                        } else { // disable feature
                                                            last_k = None;
                                                            last_a = None;
                                                        }

							Some(cnf)
						})
						.flatten()
						.collect(),
				)
			}
		} else {
			unreachable!();
		}
	}

	pub fn vars(&self) -> Vec<IntVarRef> {
		self.exp
			.terms
			.iter()
			.map(|term| &term.x)
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	pub(crate) fn _simplified(self) -> Result<Lin> {
		let mut k = self.k;
		let con = Lin {
			exp: LinExp {
				terms: self
					.exp
					.terms
					.into_iter()
					.filter_map(|t| {
						if t.x.borrow().is_constant() {
							k -= t.c * t.x.borrow().dom.lb();
							None
						} else {
							Some(t)
						}
					})
					.collect(),
			},
			k,
			..self
		};
		if con.exp.terms.is_empty() {
			con.check(&Assignment::default())
				.map(|_| con)
				.map_err(|_| Unsatisfiable)
		} else {
			Ok(con)
		}
	}
}

#[cfg(test)]
#[cfg(feature = "cadical")]
mod tests {

	use crate::helpers::tests::assert_encoding;
	use crate::helpers::tests::expect_file;
	use crate::integer::Model;
	use crate::Cnf;

	#[cfg(feature = "tracing")]
	use traced_test::test;

	use super::Format;

	#[test]
	fn test_enc_rec_lookahead() {
		let mut m = Model::from_string(
			&std::fs::read_to_string("./res/lps/enc_rec_lookahead.lp").unwrap(),
			Format::Lp,
		)
		.unwrap();
		// LOOKAHEAD feature removes redundant x>=2/\y>=3->z>=5 (-1 -2 3), since we have x>=2->x>=0 (tautological) and x>=0/\y>=3->z>=5 (-2 3)
		let mut cnf = Cnf::default();
		m.encode_pub(&mut cnf).unwrap();
		assert_encoding(&cnf, &expect_file!["integer/con/enc_rec_lookahead.cnf"]);
	}

	#[test]
	fn test_enc_rec_bdd_style_view() {
		let mut m = Model::from_string(
			&std::fs::read_to_string("./res/lps/bdd_style_view.lp").unwrap(),
			Format::Lp,
		)
		.unwrap();
		let mut cnf = Cnf::default();
		m.encode_pub(&mut cnf).unwrap();
		assert_encoding(
			&cnf,
			&expect_file!["integer/con/enc_rec_bdd_style_view.cnf"],
		);
	}
}
