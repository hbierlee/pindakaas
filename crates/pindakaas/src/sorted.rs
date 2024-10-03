use cached::proc_macro::cached;
use iset::interval_map;
use itertools::Itertools;

use crate::{
	helpers::{add_clauses_for, negate_cnf},
	int::{IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	trace::emit_clause,
	CheckError, Checker, ClauseDatabase, Coeff, Encoder, LinExp, Lit, Result, Unsatisfiable,
	Valuation,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortedEncoder {
	pub(crate) add_consistency: bool,
	pub(crate) strategy: SortedStrategy,
	pub(crate) overwrite_direct_cmp: Option<LimitComp>,
	pub(crate) overwrite_recursive_cmp: Option<LimitComp>,
	pub(crate) sort_n: SortN,
}
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SortN {
	One,
	#[allow(dead_code)] // TODO
	DivTwo,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum SortedStrategy {
	Direct,
	Recursive,
	Mixed(u32),
}

impl Default for SortedEncoder {
	fn default() -> Self {
		Self {
			strategy: SortedStrategy::Mixed(10),
			add_consistency: false,
			overwrite_direct_cmp: Some(LimitComp::LessEq),
			overwrite_recursive_cmp: Some(LimitComp::Equal),
			sort_n: SortN::DivTwo,
		}
	}
}

impl SortedEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn set_strategy(&mut self, strategy: SortedStrategy) -> &mut Self {
		self.strategy = strategy;
		self
	}
}

#[derive(Debug, Clone)]
pub struct Sorted<'a> {
	pub(crate) xs: &'a [Lit],
	pub(crate) cmp: LimitComp,
	pub(crate) y: &'a IntVarEnc,
}

impl<'a> Sorted<'a> {
	pub(crate) fn new(xs: &'a [Lit], cmp: LimitComp, y: &'a IntVarEnc) -> Self {
		Self { xs, cmp, y }
	}
}

impl<'a> Checker for Sorted<'a> {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<(), CheckError> {
		let lhs = LinExp::from_terms(self.xs.iter().map(|x| (*x, 1)).collect_vec().as_slice())
			.value(sol)?;
		let rhs = LinExp::from(self.y).value(sol)?;

		if match self.cmp {
			LimitComp::LessEq => lhs <= rhs,
			LimitComp::Equal => lhs == rhs,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

impl<DB: ClauseDatabase> Encoder<DB, Sorted<'_>> for SortedEncoder {
	fn encode(&self, db: &mut DB, sorted: &Sorted) -> Result {
		let xs = sorted
			.xs
			.iter()
			.map(|x| Some(*x))
			.enumerate()
			.map(|(i, x)| {
				IntVarOrd::from_views(db, interval_map! { 1..2 => x }, format!("x_{}", i + 1))
					.into()
			})
			.collect_vec();

		if self.add_consistency {
			sorted.y.consistent(db).unwrap();
		}

		self.sorted(db, &xs, &sorted.cmp, sorted.y, 0)
	}
}

impl<DB: ClauseDatabase> Encoder<DB, TernLeConstraint<'_>> for SortedEncoder {
	fn encode(&self, db: &mut DB, tern: &TernLeConstraint) -> Result {
		let TernLeConstraint { x, y, cmp, z } = tern;
		if tern.is_fixed()? {
			Ok(())
		} else if matches!(x, IntVarEnc::Ord(_))
			&& matches!(y, IntVarEnc::Ord(_))
			&& matches!(z, IntVarEnc::Ord(_))
		{
			self.merged(db, x, y, cmp, z, 0)
		} else {
			TernLeEncoder::default().encode(db, tern)
		}
	}
}

impl SortedEncoder {
	fn next_int_var<DB: ClauseDatabase>(&self, db: &mut DB, ub: Coeff, lbl: String) -> IntVarEnc {
		// TODO We always have the view x>=1 <-> y>=1, which is now realized using equiv
		if ub == 0 {
			IntVarEnc::Const(0)
		} else {
			let y = IntVarOrd::from_bounds(db, 0, ub, lbl);
			if self.add_consistency {
				y.consistent(db).unwrap();
			}
			y.into()
		}
	}

	/// The sorted/merged base case of x1{0,1}+x2{0,1}<=y{0,1,2}
	fn smerge<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		x1: &IntVarEnc,
		x2: &IntVarEnc,
		cmp: &LimitComp,
		y: &IntVarEnc,
	) -> Result {
		// we let x2 take the place of z_ceil, so we need to add 1 to both sides
		let x2 = x2.add(
			db,
			&TernLeEncoder::default(),
			&IntVarEnc::Const(1),
			None,
			None,
		)?;
		let y = y.add(
			db,
			&TernLeEncoder::default(),
			&IntVarEnc::Const(1),
			None,
			None,
		)?;
		self.comp(db, x1, &x2, cmp, &y, 1)
	}

	fn sorted<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		xs: &[IntVarEnc],
		cmp: &LimitComp,
		y: &IntVarEnc,
		_lvl: usize,
	) -> Result {
		let (n, m) = (xs.len(), y.ub());
		let direct = false;

		// TODO: Add tracing
		// eprintln!(
		// 	"{:_lvl$}sorted([{}] {} {}, {})",
		// 	"",
		// 	xs.iter().join(", "),
		// 	cmp,
		// 	y,
		// 	direct,
		// 	_lvl = _lvl
		// );

		debug_assert!(xs.iter().all(|x| x.ub() == 1));
		if direct {
			return (1..=m + 1).try_for_each(|k| {
				xs.iter()
					.map(|x| x.geq(1..2)[0][0])
					.combinations(k as usize)
					.try_for_each(|lits| {
						emit_clause!(
							db,
							lits.into_iter()
								.map(|lit| !lit)
								.chain(y.geq(k..(k + 1))[0].iter().cloned())
						)
					})
			});
		}
		match xs {
			[] => Ok(()),
			[x] => TernLeEncoder::default().encode(
				db,
				&TernLeConstraint {
					x,
					y: &IntVarEnc::Const(0),
					cmp: cmp.clone(),
					z: y,
				},
			),
			[x1, x2] if m <= 2 => self.smerge(db, x1, x2, cmp, y),
			xs => {
				let n = match self.sort_n {
					SortN::One => 1,
					SortN::DivTwo => n / 2,
				};
				let y1 = self.sort(
					db,
					&xs[..n],
					cmp,
					std::cmp::min((0..n).fold(0, |a, _| a + 1), y.ub()),
					String::from("y1"),
					_lvl,
				);
				let y2 = self.sort(
					db,
					&xs[n..],
					cmp,
					std::cmp::min((n..xs.len()).fold(0, |a, _| a + 1), y.ub()),
					String::from("y2"),
					_lvl,
				);

				if let Some(y1) = y1 {
					if let Some(y2) = y2 {
						self.merged(db, &y1, &y2, cmp, y, _lvl + 1)
					} else {
						Ok(())
					}
				} else {
					Ok(())
				}
			}
		}
	}

	fn sort<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		xs: &[IntVarEnc],
		cmp: &LimitComp,
		ub: Coeff,
		lbl: String,
		_lvl: usize,
	) -> Option<IntVarEnc> {
		match xs {
			[] => None,
			[x] => Some(x.clone()),
			xs => {
				let y = self.next_int_var(db, ub, lbl);
				self.sorted(db, xs, cmp, &y, _lvl).unwrap();
				Some(y)
			}
		}
	}

	fn merged<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		x1: &IntVarEnc,
		x2: &IntVarEnc,
		cmp: &LimitComp,
		y: &IntVarEnc,
		_lvl: usize,
	) -> Result {
		let (a, b, c) = (x1.ub(), x2.ub(), y.ub());
		let (strat, _cost) = merged_cost(a as u128, b as u128, c as u128, self.strategy.clone());

		// TODO: Add tracing
		// eprintln!(
		//	"{:_lvl$}merged({}, {}, {}, {:?})",
		//	"",
		//	x1,
		//	x2,
		//	y,
		//	_cost,
		//	_lvl = _lvl
		// );

		match strat {
			SortedStrategy::Direct => {
				let cmp = self.overwrite_direct_cmp.as_ref().unwrap_or(cmp).clone();
				TernLeEncoder::default().encode(
					db,
					&TernLeConstraint {
						x: x1,
						y: x2,
						cmp,
						z: y, // TODO no consistency implemented for this bound yet
					},
				)
			}
			SortedStrategy::Recursive => {
				if a == 0 && b == 0 {
					Ok(())
				} else if a == 1 && b == 1 && c <= 2 {
					self.smerge(db, x1, x2, cmp, y)
				} else {
					let x1_floor = x1.div(2);
					let x1_ceil = x1
						.add(
							db,
							&TernLeEncoder::default(),
							&IntVarEnc::Const(1),
							None,
							None,
						)?
						.div(2);

					let x2_floor = x2.div(2);
					let x2_ceil = x2
						.add(
							db,
							&TernLeEncoder::default(),
							&IntVarEnc::Const(1),
							None,
							None,
						)?
						.div(2);

					let z_floor =
						x1_floor.add(db, &TernLeEncoder::default(), &x2_floor, None, None)?;
					self.encode(
						db,
						&TernLeConstraint::new(&x1_floor, &x2_floor, cmp.clone(), &z_floor),
					)?;

					let z_ceil =
						x1_ceil.add(db, &TernLeEncoder::default(), &x2_ceil, None, None)?;
					self.encode(
						db,
						&TernLeConstraint::new(&x1_ceil, &x2_ceil, cmp.clone(), &z_ceil),
					)?;

					for c in 0..=c {
						self.comp(db, &z_floor, &z_ceil, cmp, y, c)?;
					}

					Ok(())
				}
			}
			_ => unreachable!(),
		}
	}

	fn comp<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		x: &IntVarEnc,
		y: &IntVarEnc,
		cmp: &LimitComp,
		z: &IntVarEnc,
		c: Coeff,
	) -> Result {
		let cmp = self.overwrite_recursive_cmp.as_ref().unwrap_or(cmp);
		let to_iv = |c: Coeff| c..(c + 1);
		let empty_clause: Vec<Vec<Lit>> = vec![Vec::new()];
		let c1 = c;
		let c2 = c + 1;
		let x = x.geq(to_iv(c1)); // c
		let y = y.geq(to_iv(c2)); // c+1
		let z1 = z.geq(to_iv(c1 + c1)); // 2c
		let z2 = z.geq(to_iv(c1 + c2)); // 2c+1

		add_clauses_for(
			db,
			vec![negate_cnf(x.clone()), empty_clause.clone(), z1.clone()],
		)?;
		add_clauses_for(
			db,
			vec![negate_cnf(y.clone()), empty_clause.clone(), z1.clone()],
		)?;
		add_clauses_for(
			db,
			vec![negate_cnf(x.clone()), negate_cnf(y.clone()), z2.clone()],
		)?;

		if cmp == &LimitComp::Equal {
			add_clauses_for(
				db,
				vec![x.clone(), empty_clause.clone(), negate_cnf(z2.clone())],
			)?;
			add_clauses_for(db, vec![y.clone(), empty_clause, negate_cnf(z2)])?;
			add_clauses_for(db, vec![x, y, negate_cnf(z1)])?;
		}
		Ok(())
	}
}

fn merged_dir_cost(a: u128, b: u128, c: u128) -> (u128, u128) {
	if a <= c && b <= c && a + b > c {
		(
			c,
			(a + b) * c - ((c * (c - 1)) / 2) - ((a * (a - 1)) / 2) - ((b * (b - 1)) / 2),
		)
	} else {
		(a + b, a * b + a + b)
	}
}

fn merged_rec_cost(a: u128, b: u128, c: u128, strat: SortedStrategy) -> (u128, u128) {
	let div_ceil = |a: u128, b: u128| {
		a.checked_add(b)
			.unwrap()
			.checked_sub(1)
			.unwrap()
			.checked_div(b)
			.unwrap()
	};

	match (a, b, c) {
		(0, 0, _) => (0, 0),
		(1, 0, _) => unreachable!(),
		(0, 1, _) => (0, 0),
		(1, 1, 1) => (1, 2),
		(1, 1, 2) => (2, 3),
		(a, b, c) => {
			let ((_, (v1, c1)), (_, (v2, c2)), (v3, c3)) = (
				merged_cost(div_ceil(a, 2), div_ceil(b, 2), c / 2 + 1, strat.clone()),
				merged_cost(a / 2, b / 2, c / 2, strat),
				(
					c - 1,
					if c % 2 == 1 {
						(3 * c - 3) / 2
					} else {
						((3 * c - 2) / 2) + 2
					},
				),
			);
			(v1 + v2 + v3, c1 + c2 + c3)
		}
	}
}

fn merged_mix_cost(
	dir_cost: (u128, u128),
	rec_cost: (u128, u128),
	l: u32,
) -> (SortedStrategy, (u128, u128)) {
	if lambda(dir_cost, l) < lambda(rec_cost, l) {
		(SortedStrategy::Direct, dir_cost)
	} else {
		(SortedStrategy::Recursive, rec_cost)
	}
}

#[cached]
fn merged_cost(a: u128, b: u128, c: u128, strat: SortedStrategy) -> (SortedStrategy, (u128, u128)) {
	if a > b {
		merged_cost(b, a, c, strat)
	} else {
		match strat {
			SortedStrategy::Direct => (SortedStrategy::Direct, merged_dir_cost(a, b, c)),
			SortedStrategy::Recursive => {
				(SortedStrategy::Recursive, merged_rec_cost(a, b, c, strat))
			}
			SortedStrategy::Mixed(lambda) => merged_mix_cost(
				merged_dir_cost(a, b, c),
				merged_rec_cost(a, b, c, strat),
				lambda,
			),
		}
	}
}

// TODO safely use floating point for lambda
fn lambda((v, c): (u128, u128), lambda: u32) -> u128 {
	(v * lambda as u128) + c
}

#[cfg(test)]
mod tests {
	use std::num::NonZeroI32;

	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		helpers::tests::{assert_solutions, expect_file},
		solver::{NextVarRange, VarRange},
		Cnf, Var,
	};

	fn get_sorted_encoder(strategy: SortedStrategy) -> SortedEncoder {
		SortedEncoder {
			strategy,
			overwrite_direct_cmp: None,
			overwrite_recursive_cmp: None,
			..SortedEncoder::default()
		}
	}

	#[test]
	fn test_2_merged_eq() {
		let mut cnf = Cnf::default();
		let x: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 1, String::from("x")).into();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 1, String::from("y")).into();
		let z: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("z")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();
		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(
				&mut cnf,
				&TernLeConstraint::new(&x, &y, LimitComp::Equal, &z),
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_2_merged_eq.sol"]);
	}

	#[test]
	fn test_2_sorted_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&[a, b], LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_2_sorted_eq.sol"]);
	}

	#[test]
	fn test_3_sorted_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 3, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&[a, b, c], LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_3_sorted_eq.sol"]);
	}

	#[test]
	fn test_3_2_sorted_eq() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&[a, b, c], LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_3_2_sorted_eq.sol"]);
	}

	#[test]
	fn test_4_sorted_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.next_var_range(4).unwrap().iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 4, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_sorted_eq.sol"]);
	}

	#[test]
	fn test_4_2_sorted_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.next_var_range(4).unwrap().iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 2, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_2_sorted_eq.sol"]);
	}

	#[test]
	fn test_4_3_sorted_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.next_var_range(4).unwrap().iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 3, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_4_3_sorted_eq.sol"]);
	}

	#[test]
	fn test_5_sorted_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.next_var_range(5).unwrap().iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 5, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_5_sorted_eq.sol"]);
	}

	#[test]
	fn test_5_3_sorted_eq() {
		let mut cnf = Cnf::default();
		let lits = cnf.next_var_range(5).unwrap().iter_lits().collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 3, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["sorted/test_5_3_sorted_eq.sol"]);
	}

	#[test]
	fn test_5_1_sorted_eq_negated() {
		let mut cnf = Cnf::default();
		let lits = cnf
			.next_var_range(5)
			.unwrap()
			.iter_lits()
			.map(|l| !l)
			.collect_vec();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut cnf, 0, 1, String::from("y")).into();
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		)
		.iter_lits()
		.collect_vec();

		get_sorted_encoder(SortedStrategy::Recursive)
			.encode(&mut cnf, &Sorted::new(&lits, LimitComp::Equal, &y))
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["sorted/test_5_1_sorted_eq_negated.sol"],
		);
	}
}
