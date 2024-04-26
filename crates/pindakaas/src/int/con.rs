#![allow(clippy::absurd_extreme_comparisons)]
use crate::helpers::{add_clauses_for, unsigned_binary_range};
use crate::int::bin::BinEnc;
use crate::int::helpers::display_cnf;
use crate::int::{required_lits, Dom, LitOrConst};
use crate::linear::{lex_geq_const, lex_leq_const, log_enc_add_fn};
use crate::{
	trace::emit_clause, Assignment, CheckError, ClauseDatabase, Coefficient, Comparator,
	Consistency, IntVarRef, Literal, Model, ModelConfig, Result, Term, Unsatisfiable,
};
use itertools::Itertools;

use super::{
	model::{PRINT_COUPLING, USE_COUPLING_IO_LEX, VIEW_COUPLING},
	IntVarEnc, IntVarId,
};

static mut SKIPS: u32 = 0;

#[derive(Debug, Clone, Default)]
pub struct LinExp<Lit: Literal, C: Coefficient> {
	pub terms: Vec<Term<Lit, C>>,
}

#[derive(Debug, Clone)]
pub struct Lin<Lit: Literal, C: Coefficient> {
	pub exp: LinExp<Lit, C>,
	pub cmp: Comparator,
	pub k: C,
	pub lbl: Option<String>,
}

pub(crate) enum LinCase<Lit: Literal, C: Coefficient> {
	Couple(Term<Lit, C>, Term<Lit, C>),
	Fixed(Lin<Lit, C>),
	Unary(IntVarRef<Lit, C>, Comparator, C),
	Scm(Term<Lit, C>, IntVarRef<Lit, C>),
	Rca(Term<Lit, C>, Term<Lit, C>, Term<Lit, C>),
	Order,
	Other,
}

impl<Lit: Literal, C: Coefficient> TryFrom<&Lin<Lit, C>> for LinCase<Lit, C> {
	type Error = Unsatisfiable;

	fn try_from(con: &Lin<Lit, C>) -> Result<Self, Unsatisfiable> {
		let term_encs = con
			.exp
			.terms
			.iter()
			.map(|t| (t, t.x.borrow().e.clone()))
			// TODO hopefully does not clone inner enc?
			.collect_vec();

		Ok(match (&term_encs[..], con.cmp) {
			([], _) => LinCase::Fixed(con.clone()),
			([(t, Some(IntVarEnc::Bin(_)))], cmp)
				if (t.c.is_one() || t.c.is_multiple_of(&C::from(2).unwrap()))
					&& !USE_COUPLING_IO_LEX =>
			{
				LinCase::Unary(
					(*t).clone()
						.encode_bin(None, cmp, None)?
						.try_into()
						.unwrap(),
					cmp,
					con.k,
				)
			}
			// VIEW COUPLING
			// ([(t, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(None)))], _)
			// // | ([(y, Some(IntVarEnc::Bin(None))), (t, Some(IntVarEnc::Ord(_)))], _)
			// 	if y.c == -C::one()
			// 		&& t.x.borrow().dom.size() <= C::one() + C::one()
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
				[(t_x, Some(IntVarEnc::Bin(_))), (Term { c: y_c, x: y }, Some(IntVarEnc::Bin(None)))],
				Comparator::Equal,
			) if *y_c == -C::one()
				&& con.k.is_zero()
				&& matches!(y.borrow().e, Some(IntVarEnc::Bin(_))) =>
			{
				LinCase::Scm((*t_x).clone(), y.clone())
			}
			([(t, Some(IntVarEnc::Ord(_))), (y, Some(IntVarEnc::Bin(_)))], _)
				if y.c == -C::one()
                    && con.k.is_zero()
					// && t.x.borrow().dom.size() <= C::one() + C::one()
					&& VIEW_COUPLING =>
			{
				LinCase::Couple((*t).clone(), (*y).clone())
			}

			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_))), (z, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
			) if z.c.is_negative() && con.k.is_zero() => {
				LinCase::Rca((*x).clone(), (*y).clone(), (*z).clone())
			}
			(encs, _)
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

impl<Lit: Literal, C: Coefficient> Lin<Lit, C> {
	pub fn new(terms: &[Term<Lit, C>], cmp: Comparator, k: C, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: terms.to_vec(),
			},
			cmp,
			k,
			lbl,
		}
	}

	pub fn tern(
		x: Term<Lit, C>,
		y: Term<Lit, C>,
		cmp: Comparator,
		z: Term<Lit, C>,
		lbl: Option<String>,
	) -> Self {
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

	pub(crate) fn propagate(
		&mut self,
		consistency: &Consistency,
	) -> Result<Vec<IntVarId>, Unsatisfiable> {
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
									x.ge(&b);
								} else {
									x.le(&b);
								}

								if x.size() < size {
									//println!("Pruned {}", size - x.size());
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == C::zero() {
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
									x.ge(&b);
								} else {
									x.le(&b);
								}

								if x.size() < size {
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == C::zero() {
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
				todo!()
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
				*/
			}
		}
	}

	pub(crate) fn is_tern(&self) -> bool {
		let cs = self.exp.terms.iter().map(|term| term.c).collect::<Vec<_>>();
		cs.len() == 3 && cs[2] == -C::one() && self.k.is_zero()
	}

	pub(crate) fn check(
		&self,
		a: &Assignment<C>,
		lit_assignment: Option<&[Lit]>,
	) -> Result<(), CheckError<Lit>> {
		let lhs = self
			.exp
			.terms
			.iter()
			.map(|term| term.c * a[&term.x.borrow().id].1)
			.fold(C::zero(), C::add);

		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			const SHOW_LP: bool = false;
			Err(CheckError::Fail(format!(
				"Inconsistency in {}: {} == {} !{} {}\n{}",
				self.lbl.clone().unwrap_or_default(),
				self.exp
					.terms
					.iter()
					.map(|term| {
						format!(
							"{} * {}={} (={}) [{:?}]",
							term.c,
							term.x.borrow().lbl(),
							a[&term.x.borrow().id].1,
							term.c * a[&term.x.borrow().id].1,
							lit_assignment
								.map(|lit_assignment| lit_assignment
									.iter()
									.filter(|lit| term.x.borrow().lits().contains(&lit.var()))
									.collect_vec())
								.unwrap_or_default()
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
						.to_text(crate::Format::Lp)
					})
					.unwrap_or_default()
			)))
		}
	}

	fn _is_simplified(&self) -> bool {
		self.exp
			.terms
			.iter()
			.all(|term| !term.c.is_zero() && !term.x.borrow().is_constant())
	}

	// fn into_tern(self) -> Self {
	// 	Lin {
	// 		exp: LinExp {
	// 			terms: self
	// 				.exp
	// 				.terms
	// 				.into_iter()
	// 				.with_position()
	// 				.map(|pos| match pos {
	// 					(Position::Last, term) => term * -C::one(),
	// 					(_, term) => term, // also matches Only element; so unary constraints are not minused
	// 				})
	// 				.collect(),
	// 		},
	// 		..self
	// 	}
	// }

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		_config: &ModelConfig<C>,
	) -> Result {
		match LinCase::try_from(self)? {
			LinCase::Fixed(con) => con
				.check(&Assignment::default(), None)
				.map_err(|_| Unsatisfiable),
			LinCase::Unary(x, cmp, k) => {
				let x_enc = x.borrow_mut().encode_bin(db)?; // avoid BorrowMutError
				x_enc.encode_unary_constraint(db, &cmp, k, &x.borrow().dom, false)
			}
			LinCase::Couple(t_x, t_y) => {
				t_x.x.borrow_mut().encode_ord(db)?;
				if !t_x.x.borrow().add_consistency {
					t_x.x.borrow_mut().consistent(db)?;
				}
				let y_enc = t_y.x.borrow_mut().encode_bin(db)?;

				let up = match self.cmp {
					Comparator::LessEq => false,
					Comparator::Equal => unreachable!(),
					Comparator::GreaterEq => true,
				};

				let (range_lb, range_ub) = unsigned_binary_range::<C>(y_enc.bits());
				let dom = &t_y.x.borrow().dom;

				let mut xs = t_x
					.ineqs(up)
					.into_iter()
					.map(|(c, x, _)| (y_enc.normalize((t_x.c * c) - self.k, dom), x))
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
						let (c_a, c_b) = (c_a + C::one(), c_b);
						let y = y_enc.ineqs(c_a, c_b, !up);
						if PRINT_COUPLING >= 2 {
							println!("{up} {c_a}..{c_b} -> {x:?}");
						}
						if PRINT_COUPLING >= 2 {
							println!("{y:?}");
						}
						add_clauses_for(db, vec![vec![x.clone()], y])
					})
			}
			LinCase::Scm(t_x, y) => {
				assert!(t_x.c.is_positive(), "neg scm: {self}");

				t_x.x.borrow_mut().encode_bin(db)?; // encode x (if not encoded already)
									// encode y

				let tmp_y = t_x.clone().encode_bin(None, self.cmp, None)?;

				// TODO make Term decompose and use encode_bin for actual encoding incl scm, but for now (since it's not given Db, call scm_dnf) here
				(*y).borrow_mut().e = Some(IntVarEnc::Bin(Some(
					tmp_y.x.borrow_mut().encode_bin(db)?.scm_dnf(db, tmp_y.c)?,
				)));
				Ok(())
			}
			LinCase::Rca(x, y, z) => {
				assert!(
					x.lb() + y.lb() <= -z.ub(),
					"LBs for addition not matching: {self}"
				);

				let z: IntVarRef<_, _> = (z * -C::one()).try_into().unwrap();

				let z_ground = x.lb() + y.lb();
				let (x, y) = &[x, y]
					.into_iter()
					.map(|t| {
						// encode
						t.x.borrow_mut().encode(db, None).unwrap();
						// encode term and return underlying var
						let t = t.encode_bin(None, self.cmp, None).unwrap();
						let x: IntVarRef<_, _> = t
							.try_into()
							.expect("Calling Term::encode_bin should return 1*y");
						// x.clone().encode_bin(db).unwrap().xs()
						if let Some(IntVarEnc::Bin(Some(x_enc))) = x.clone().borrow().e.clone() {
							x_enc.xs()
						} else {
							unreachable!()
						}
					})
					.collect_tuple()
					.unwrap();

				assert!(
					matches!(z.borrow().e, Some(IntVarEnc::Bin(None))),
					"Last var {} should not have been encoded yet",
					z.borrow()
				);
				let z_dom = Dom::from_bounds(z_ground, z.borrow().ub());

				let z_lb = z.borrow().lb();
				z.borrow_mut().dom = z_dom; // fix lower bound to ground
				let lits = Some(required_lits(z_ground, z.borrow().dom.ub()));
				let z_bin = BinEnc::from_lits(
					&log_enc_add_fn(db, x, y, &self.cmp, LitOrConst::Const(false), lits).unwrap(),
				);

				lex_geq_const(db, &z_bin.xs(), z_lb - z_ground, z_bin.bits())?;

				// TODO only has to be done for last constraint of lin decomp..
				lex_leq_const(db, &z_bin.xs(), z.borrow().ub() - z_ground, z_bin.bits())?;
				z.borrow_mut().e = Some(IntVarEnc::Bin(Some(z_bin)));
				Ok(())
			}
			LinCase::Order => {
				// encode all variables
				self.exp
					.terms
					.iter()
					.try_for_each(|t| t.x.borrow_mut().encode(db, None).map(|_| ()))?;

				assert!(
					self.exp.terms.iter().all(|t| match t.x.borrow().e {
						Some(IntVarEnc::Ord(_)) => true,
						Some(IntVarEnc::Bin(_)) => t.x.borrow().dom.size() <= C::one() + C::one(),
						_ => false,
					}),
					"Non-order: {self}"
				);

				const SORT_BY_COEF: bool = true;
				// const SORT_BY_COEF: bool = false;
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
					if PRINT_COUPLING >= 1 {
						unsafe {
							println!("skips = {}", SKIPS);
							SKIPS = 0;
						}
					}
					if PRINT_COUPLING >= 3 {
						println!("{}", display_cnf(&cnf));
					}

					for c in cnf {
						emit_clause!(db, &c)?;
					}
					Ok(())
				})
			}
			LinCase::Other => todo!("Cannot constrain: {self}"),
		}

		/*
		// CHANNEL
		(
			[(t_x, Some(IntVarEnc::Ord(_))), (t_y, Some(IntVarEnc::Bin(_)))],
			Comparator::Equal,
		) if t_x.c.is_one() && t_y.c == -C::one() && USE_CHANNEL => {
			t_x.x.borrow_mut().encode_ord(db)?;
			if !t_x.x.borrow().add_consistency {
				t_x.x.borrow_mut().consistent(db)?;
			}
			let y_enc = t_y.x.borrow_mut().encode_bin(db)?;

			let (range_lb, range_ub) = unsigned_binary_range::<C>(y_enc.bits());
			y_enc.x.iter().enumerate().try_for_each(|(i, y_i)| {
				let r = C::one().shl(i);
				let (l, u) = (range_lb.div(r), range_ub.div(r));
				add_clauses_for(
					db,
					vec![remove_red(
						num::iter::range_inclusive(l, u)
							.sorted_by_key(|k| (k.is_even(), *k))
							.filter_map(|k| {
								let y_i = if k.is_even() {
									-y_i.clone()
								} else {
									y_i.clone()
								};
								let a = y_enc.denormalize(r * k, &t_y.x.borrow().dom); // ??
								let b = a + r;
								let x_a = t_x.x.borrow().ineq(a, false, None).1;
								let x_b = t_x.x.borrow().ineq(b, true, None).1;
								if x_a == negate_cnf(x_b.clone()) {
									None
								} else {
									Some(
										[x_a, y_i.into(), x_b]
											.into_iter()
											.multi_cartesian_product()
											.concat()
											.into_iter()
											// .into_iter()
											.flatten()
											.collect(),
									)
								}
							})
							.collect(),
					)],
				)
			})
		}
		*/
	}

	// #[cfg_attr(
	// 	feature = "trace",
	// 	tracing::instrument(name = "encode_rec", skip_all, fields(constraint = format!("{} {} {}", terms.iter().join(" "), cmp, k)))
	// )]
	fn encode_rec(
		terms: &[Term<Lit, C>],
		cmp: &Comparator,
		k: C,
		depth: usize,
	) -> (Option<C>, Vec<Vec<Lit>>) {
		if let Some((head, tail)) = terms.split_first() {
			let up = head.c.is_positive() == (cmp == &Comparator::GreaterEq);
			if tail.is_empty() {
				let k_ = if up {
					k.div_ceil(&head.c)
				} else {
					k.div_floor(&head.c.clone()) + C::one()
				};

				if PRINT_COUPLING >= 2 {
					print!(
						"{}{} ({}*{} {cmp} {k}) (= {} {} {k_})",
						"\t".repeat(depth),
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
				}

				let (c, cnf) = head.x.borrow().ineq(k_, up, None);

				if PRINT_COUPLING >= 2 {
					println!("== {cnf:?}",);
				}

				(c.map(|c| head.c * c), cnf)
			} else {
				let mut last_a = None; // last antecedent implies till here
				let mut last_k = None; // last consequent implies to here
					   // let mut last_cnf = None;
				(
					None,
					head.ineqs(up)
						.into_iter()
						.map_while(|(d, conditions, implies)| {
							// l = x>=d+1, ~l = ~(x>=d+1) = x<d+1 = x<=d
							let k_ = k - head.c * d;

							if PRINT_COUPLING >= 2 {
								print!(
									"{} {} {}*({} {cmp} {}) (->x{cmp}{implies}) = [{:?}] (k={k} - {}*{d} = {k_}) last_a={last_a:?} last_k={last_k:?}",
                                    "\t".repeat(depth),
									if up {
										"up: "
									} else {
										"down: "
									},
									head.c,
									head.x.borrow(),
									if up { d + C::one() } else { d },
									conditions,
									head.c,
								);
							}


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

							if PRINT_COUPLING >= 2 {
								print!(" {}/{}", antecedent_implies_next, consequent_implies_next);
							}

							if PRINT_COUPLING >= 2 {
								println!();
							}

							let (c, cnf) = Self::encode_rec(tail, cmp, k_, depth + 1);
							let cnf = cnf
								.into_iter()
								.map(|r| conditions.clone().into_iter().chain(r).collect())
								.collect_vec();


							if antecedent_implies_next && consequent_implies_next  {
                                if PRINT_COUPLING >= 2 {
										println!("SKIP");
                                }
                                if PRINT_COUPLING >= 1 {
                                unsafe {
                                    SKIPS += 1;
                                }
                                }
									return Some(vec![]); // some consequent -> skip clause
							}

							last_k = c;
							last_a = Some(implies);

							// // TODO or if r contains empty clause?
                            // TODO remove; probably redundant with antecedent stuff above
							// if cnf == vec![vec![]] {
							// 	stop = true;
							// }

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

	pub fn vars(&self) -> Vec<IntVarRef<Lit, C>> {
		self.exp
			.terms
			.iter()
			.map(|term| &term.x)
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	pub(crate) fn _simplified(self) -> Result<Lin<Lit, C>> {
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
			con.check(&Assignment::default(), None)
				.map(|_| con)
				.map_err(|_| Unsatisfiable)
		} else {
			Ok(con)
		}
	}

	/*
		#[cfg_attr(
			feature = "trace",
			tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
		)]
		pub fn _encode<DB: ClauseDatabase<Lit = Lit>>(
			&self,
			db: &mut DB,
			config: &ModelConfig<C>,
		) -> Result {
			// TODO assert simplified/simplify
			// assert!(self._is_simplified());

			let mut encoder = TernLeEncoder::default();
			// TODO use binary heap

			if config.decomposer == Decomposer::Rca || config.scm == Scm::Pow {
				assert!(config.cutoff == Some(C::zero()));
				let mut k = self.k;
				let mut encs = self
					.clone()
					.exp
					.terms
					.into_iter()
					.flat_map(|term| {
						term.encode(db, config).map(|(xs, c)| {
							k -= c;
							xs.into_iter()
								.filter(|x| {
									if let IntVarEnc::Const(c) = x {
										k -= *c;
										false
									} else {
										true
									}
								})
								.collect_vec()
						})
					})
					.flatten()
					.collect::<Vec<_>>();
				assert!(
					encs.iter().all(|e| matches!(e, IntVarEnc::Bin(_))),
					"{encs:?}"
				);

				if self
					.exp
					.terms
					.iter()
					.all(|term| matches!(term.x.borrow().e.as_ref().unwrap(), IntVarEnc::Bin(_)))
				{
					// TODO hard to do in a reduce ..
					// TODO Replace 0 for first element

					encs.sort_by_key(IntVarEnc::ub);
					while encs.len() > 1 {
						let x = encs.pop().unwrap();
						let z = if let Some(y) = encs.pop() {
							x.add(db, &mut encoder, &y, None, None)?
						} else {
							x
						};

						encs.insert(
							encs.iter()
								.position(|enc| z.ub() < enc.ub())
								.unwrap_or(encs.len()),
							z,
						);
						debug_assert!(encs.windows(2).all(|x| x[0].ub() <= x[1].ub()));
					}

					assert!(encs.len() == 1);
					encoder.encode(
						db,
						&TernLeConstraint::new(
							&encs.pop().unwrap(),
							&IntVarEnc::Const(C::zero()),
							&self.cmp,
							&IntVarEnc::Const(k),
						),
					)?;
				}
				return Ok(());
			}

			let mut k = self.k;
			let encs = self
				.clone()
				// Encodes terms into ternary constrain (i.e. last term is multiplied by -1)
				.into_tern()
				.exp
				.terms
				.into_iter()
				.with_position()
				.flat_map(|(pos, term)| {
					term.encode(db, config).map(|(xs, c)| {
						match pos {
							Position::Last => {
								k += c;
							}
							_ => {
								k -= c;
							}
						}
						xs
					})
				})
				.flatten()
				.collect::<Vec<_>>();

			// TODO generalize n-ary encoding; currently using fallback of TernLeEncoder
			return match &encs[..] {
				[] => return Ok(()),
				[x] if DECOMPOSE => encoder.encode(
					db,
					&TernLeConstraint::new(
						x,
						&IntVarEnc::Const(C::zero()),
						&self.cmp,
						&IntVarEnc::Const(k),
					),
				),
				[x, z] if DECOMPOSE => encoder.encode(
					db,
					&TernLeConstraint::new(x, &IntVarEnc::Const(-k), &self.cmp, z),
				),
				[x, y, z] if DECOMPOSE => {
					let z = z.add(db, &mut encoder, &IntVarEnc::Const(k), None, None)?;
					encoder.encode(db, &TernLeConstraint::new(x, y, &self.cmp, &z))
				}
				_ => {
					assert!(
						encs.iter()
							.all(|enc| matches!(enc, IntVarEnc::Ord(_) | IntVarEnc::Const(_))),
						"TODO: {encs:?}"
					);

					// just get encoding; does not need to handle terms coefficient here
					// let encs = self
					// 	.clone()
					// 	.exp
					// 	.terms
					// 	.into_iter()
					// 	.map(|term| {
					// 		term.x.borrow_mut().encode(db, &mut HashMap::new(), true)?;
					// 		Ok(term.x.borrow().e.as_ref().unwrap().clone())
					// 	})
					// 	.collect::<Result<Vec<_>>>()?;
					// TODO support binary
					self.cmp.split().into_iter().try_for_each(|cmp| {
						let is_leq = matches!(cmp, Comparator::LessEq);

						// encs[0..encs.len() - 1]
						self.exp
							.terms
							.iter()
							// .zip(&self.exp.terms)
							.map(|term| {
								term.ineqs(&Comparator::GreaterEq)
								// if is_leq == term.c.is_positive() {
								// 	term.geqs()
								// } else {
								// 	term.leqs()
								// }
							})
							.multi_cartesian_product()
							.try_for_each(|geqs| {
								let rhs = geqs
									.iter()
									.zip(&self.exp.terms)
									.map(|((d, _), term)| {
										if is_leq == term.c.is_positive() {
											term.c * (d.end - C::one())
										} else {
											term.c * d.start
										}
									})
									.fold(self.k, C::sub);

								let conditions = geqs
									.iter()
									.map(|(_, cnf)| negate_cnf(cnf.clone()))
									.collect::<Vec<_>>();

								let (last_enc, last_c) =
									(&encs[encs.len() - 1], &self.exp.terms[encs.len() - 1].c);

								let last = if is_leq == last_c.is_positive() {
									last_enc.leq_(rhs.div_ceil(last_c))
								} else {
									last_enc.geq_(rhs.div_floor(last_c))
								};

								let cnf = conditions.iter().cloned().chain([last]).collect();
								add_clauses_for(db, cnf)
							})
					})
				}
			};
		}
	*/
}