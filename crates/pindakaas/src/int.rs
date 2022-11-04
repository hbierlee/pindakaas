use iset::{interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	helpers::is_powers_of_two,
	linear::{lex_lesseq_const, log_enc_add, LimitComp, LinExp, Part},
	trace::{emit_clause, new_var},
	CheckError, Checker, ClauseDatabase, Coefficient, Encoder, Literal, PosCoeff, Result,
	Unsatisfiable,
};
use std::{
	collections::HashSet,
	fmt,
	hash::BuildHasherDefault,
	ops::{Neg, Range},
};

/// Chooses next integer variable heuristically; returns Ord or Bin based on whether the number of resulting literals is under the provided cutoff
pub(crate) fn next_int_var<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	dom: IntervalSet<C>,
	cutoff: C,
	add_consistency: bool,
	lbl: String,
) -> IntVarEnc<DB::Lit, C> {
	// TODO check for domain of 1 => Constant?
	if cutoff == -C::one() || C::from(dom.len()).unwrap() <= cutoff {
		let x = IntVarOrd::new(db, dom.into_iter(..).map(|iv| (iv, None)).collect(), lbl);
		if add_consistency {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Ord(x)
	} else {
		let x = IntVarBin::new(db, dom.range().unwrap().end - C::one(), lbl);
		if add_consistency {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LitOrConst<Lit: Literal> {
	Lit(Lit),
	Const(bool),
}

impl<Lit: Literal> Neg for LitOrConst<Lit> {
	type Output = Self;

	fn neg(self) -> Self {
		match self {
			Self::Lit(lit) => Self::Lit(lit.negate()),
			Self::Const(b) => Self::Const(!b),
		}
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarBin<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:B in {:?}..{:?} ({})",
			self.lbl,
			self.lb(),
			self.ub(),
			self.lits()
		)
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarOrd<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:O in {:?}..{:?} ({})",
			self.lbl,
			self.lb(),
			self.ub(),
			self.lits()
		)
	}
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarOrd<Lit: Literal, C: Coefficient> {
	xs: IntervalMap<C, Lit>,
	lbl: String,
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		dom: IntervalMap<C, Option<Lit>>,
		lbl: String,
	) -> Self {
		let xs = dom
			.into_iter(..)
			.map(|(v, lit)| {
				let lit = lit.unwrap_or_else(|| new_var!(db, format!("{lbl}>={v:?}")));
				(v, lit)
			})
			.collect::<IntervalMap<_, _>>();
		debug_assert!(!xs.is_empty());
		Self { xs, lbl }
	}

	pub fn _consistency(&self) -> ImplicationChainConstraint<Lit> {
		ImplicationChainConstraint {
			lits: self.xs.values(..).cloned().collect::<Vec<_>>(),
		}
	}

	#[allow(dead_code)]
	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		ImplicationChainEncoder::default()._encode(db, &self._consistency())
	}
}

pub(crate) struct ImplicationChainConstraint<Lit: Literal> {
	lits: Vec<Lit>,
}

#[derive(Default)]
pub(crate) struct ImplicationChainEncoder {}

impl ImplicationChainEncoder {
	pub fn _encode<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
		ic: &ImplicationChainConstraint<DB::Lit>,
	) -> Result {
		for (a, b) in ic.lits.iter().tuple_windows() {
			emit_clause!(db, &[b.negate(), a.clone()])?
		}
		Ok(())
	}
}

impl<Lit: Literal> Checker for ImplicationChainConstraint<Lit> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		self.lits.iter().tuple_windows().try_for_each(|(a, b)| {
			let a = Self::assign(a, solution);
			let b = Self::assign(b, solution);
			if b.is_negated() || !a.is_negated() {
				Ok(())
			} else {
				Err(CheckError::Unsatisfiable(Unsatisfiable))
			}
		})
	}
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	fn dom(&self) -> IntervalSet<C> {
		std::iter::once(self.lb()..self.lb() + C::one())
			.chain(self.xs.intervals(..))
			.collect()
	}

	fn lb(&self) -> C {
		self.xs.range().unwrap().start - C::one()
	}

	fn ub(&self) -> C {
		self.xs.range().unwrap().end - C::one()
	}

	fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		let v = v.end - C::one();
		if v <= self.lb() {
			vec![]
		} else if v > self.ub() {
			vec![vec![]]
		} else {
			match self.xs.overlap(v).collect::<Vec<_>>()[..] {
				[(_, x)] => vec![vec![x.clone()]],
				_ => panic!("No or multiples variables at {v:?}"),
			}
		}
	}

	fn as_lin_exp(&self) -> LinExp<Lit, C> {
		let mut acc = self.lb();
		LinExp::new()
			.add_chain(
				&self
					.xs
					.iter(..)
					.map(|(iv, lit)| {
						let v = iv.end - C::one() - acc;
						acc += v;
						(lit.clone(), v)
					})
					.collect::<Vec<_>>(),
			)
			.add_constant(self.lb())
	}

	fn lits(&self) -> usize {
		self.xs.len()
	}
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	pub(crate) xs: Vec<Lit>,
	lb: C,
	ub: C,
	lbl: String,
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	// TODO change to with_label or something
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, ub: C, lbl: String) -> Self {
		let bits = C::zero().leading_zeros() - ub.leading_zeros();
		Self {
			xs: (0..bits)
				.map(|_i| new_var!(db, format!("{}^{}", lbl, _i)))
				.collect(),
			lb: C::zero(), // TODO support non-zero
			ub,
			lbl,
		}
	}

	pub fn from_terms(
		terms: Vec<(Lit, PosCoeff<C>)>,
		lb: PosCoeff<C>,
		ub: PosCoeff<C>,
		lbl: String,
	) -> Self {
		debug_assert!(is_powers_of_two(
			terms
				.iter()
				.map(|(_, c)| **c)
				.collect::<Vec<_>>()
				.as_slice()
		));
		Self {
			xs: terms.into_iter().map(|(l, _)| l).collect(),
			lb: *lb, // TODO support non-zero
			ub: *ub,
			lbl,
		}
	}

	pub fn _consistency(&self) -> TernLeConstraintContainer<Lit, C> {
		TernLeConstraintContainer {
			x: IntVarEnc::Bin(self.clone()),
			y: IntVarEnc::Const(self.lb),
			cmp: LimitComp::LessEq,
			z: IntVarEnc::Const(self.ub),
		}
	}

	#[allow(dead_code)]
	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		TernLeEncoder::default().encode(db, &self._consistency().get())
	}
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	fn dom(&self) -> IntervalSet<C> {
		num::iter::range_inclusive(self.lb, self.ub)
			.map(|i| i..(i + C::one()))
			.collect()
	}

	fn lb(&self) -> C {
		self.lb
	}

	fn ub(&self) -> C {
		self.ub
	}

	fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		num::iter::range_inclusive(
			std::cmp::max(self.lb(), v.start - C::one()),
			std::cmp::min(self.ub(), v.end - C::one() - C::one()),
		)
		.map(|v| {
			self.xs
				.iter()
				.enumerate()
				.filter_map(|(i, lit)| {
					if ((v >> i) & C::one()) != C::one() {
						Some(lit.clone())
					} else {
						None
					}
				})
				.collect::<Vec<_>>()
		})
		.collect()
	}

	fn as_lin_exp(&self) -> LinExp<Lit, C> {
		let mut exp = LinExp::new();
		let mut k = C::one();
		let two = C::one() + C::one();
		for lit in &self.xs {
			exp += (lit.clone(), k);
			k *= two;
		}
		exp
	}

	fn lits(&self) -> usize {
		self.xs.len()
	}
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	/// Constructs IntVar `y` for linear expression `xs` so that ∑ xs ≦ y, using order encoding
	pub fn from_part_using_le_ord<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		xs: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
		lbl: String,
	) -> Self {
		// TODO add_consistency on coupled leaves (wherever not equal to principal vars)
		// if add_consistency {
		// 	for leaf in &leaves {
		// 		leaf.encode_consistency(db);
		// 	}
		// }

		// couple given encodings to the order encoding
		// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

		match xs {
			Part::Amo(terms) => {
				let terms: Vec<(PosCoeff<C>, Lit)> = terms
					.iter()
					.map(|(lit, coef)| (coef.clone(), lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: FxHashMap<C, Vec<Lit>> =
					FxHashMap::with_capacity_and_hasher(terms.len(), BuildHasherDefault::default());
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(*coef).or_insert_with(Vec::new).push(lit);
				}

				let dom = std::iter::once((C::zero(), vec![]))
					.chain(h.into_iter())
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					.tuple_windows()
					.map(|((prev, _), (coef, lits))| {
						let interval = (prev + C::one())..(coef + C::one());
						if lits.len() == 1 {
							(interval, Some(lits[0].clone()))
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								emit_clause!(db, &[lit.negate(), o.clone()]).unwrap();
							}
							(interval, Some(o))
						}
					})
					.collect();
				IntVarOrd::new(db, dom, lbl)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				IntVarOrd::new(
					db,
					std::iter::once(&(terms[0].0.clone(), C::zero().into()))
						.chain(terms.iter())
						.map(|(lit, coef)| {
							acc += **coef;
							debug_assert!(acc <= *ub);
							(acc, lit.clone())
						})
						.tuple_windows()
						.map(|((prev, _), (coef, lit))| {
							((prev + C::one())..(coef + C::one()), Some(lit))
						})
						.collect(),
					lbl,
				)
			}
			Part::Dom(terms, l, u) => {
				let x_bin =
					IntVarBin::from_terms(terms.to_vec(), l.clone(), u.clone(), String::from("x"));
				let x_ord = IntVarOrd::new(
					db,
					num::iter::range_inclusive(x_bin.lb(), x_bin.ub())
						.map(|i| (i..(i + C::one()), None))
						.collect(),
					String::from("x"),
				);

				TernLeEncoder::default()
					.encode(
						db,
						&TernLeConstraint::new(
							&x_ord.clone().into(),
							&IntVarEnc::Const(C::zero()),
							LimitComp::LessEq,
							&x_bin.into(),
						),
					)
					.unwrap();
				x_ord
			}
		}
	}
}

#[derive(Debug, Clone)]
pub(crate) enum IntVarEnc<Lit: Literal, C: Coefficient> {
	Ord(IntVarOrd<Lit, C>),
	#[allow(dead_code)]
	Bin(IntVarBin<Lit, C>),
	Const(C),
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> {
	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	pub(crate) fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.geq(v),
			IntVarEnc::Bin(b) => b.geq(v),
			IntVarEnc::Const(c) => {
				if *c >= v.end - C::one() {
					vec![]
				} else {
					vec![vec![]]
				}
			}
		}
	}

	/// Returns a partitioned domain
	pub(crate) fn dom(&self) -> IntervalSet<C> {
		match self {
			IntVarEnc::Ord(o) => o.dom(),
			IntVarEnc::Bin(b) => b.dom(),
			IntVarEnc::Const(c) => interval_set!(*c..(*c + C::one())),
		}
	}

	#[allow(dead_code)]
	pub(crate) fn lb(&self) -> C {
		match self {
			IntVarEnc::Ord(o) => o.lb(),
			IntVarEnc::Bin(b) => b.lb(),
			IntVarEnc::Const(c) => *c,
			// _ => self.dom().range().unwrap().start - C::one(),
		}
	}

	pub(crate) fn ub(&self) -> C {
		match self {
			IntVarEnc::Ord(o) => o.ub(),
			IntVarEnc::Bin(b) => b.ub(),
			IntVarEnc::Const(c) => *c,
			// _ => self.dom().range().unwrap().end - C::one(),
		}
	}

	pub(crate) fn as_lin_exp(&self) -> LinExp<Lit, C> {
		match self {
			IntVarEnc::Ord(o) => o.as_lin_exp(),
			IntVarEnc::Bin(b) => b.as_lin_exp(),
			IntVarEnc::Const(c) => LinExp::new().add_constant(*c),
		}
	}
	/// Return number of lits in encoding
	#[allow(dead_code)]
	fn lits(&self) -> usize {
		match self {
			IntVarEnc::Ord(o) => o.lits(),
			IntVarEnc::Bin(b) => b.lits(),
			IntVarEnc::Const(_) => 0,
		}
	}
}

impl<Lit: Literal, C: Coefficient> From<IntVarBin<Lit, C>> for IntVarEnc<Lit, C> {
	fn from(b: IntVarBin<Lit, C>) -> Self {
		Self::Bin(b)
	}
}

impl<Lit: Literal, C: Coefficient> From<IntVarOrd<Lit, C>> for IntVarEnc<Lit, C> {
	fn from(o: IntVarOrd<Lit, C>) -> Self {
		Self::Ord(o)
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarEnc<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			IntVarEnc::Ord(o) => o.fmt(f),
			IntVarEnc::Bin(b) => b.fmt(f),
			IntVarEnc::Const(o) => write!(f, "{o:?}"),
		}
	}
}

pub(crate) struct TernLeConstraint<'a, Lit: Literal, C: Coefficient> {
	pub(crate) x: &'a IntVarEnc<Lit, C>,
	pub(crate) y: &'a IntVarEnc<Lit, C>,
	pub(crate) cmp: LimitComp,
	pub(crate) z: &'a IntVarEnc<Lit, C>,
}

// TODO rename TernLeConstraint => TernLinConstraint/Encoder
impl<'a, Lit: Literal, C: Coefficient> TernLeConstraint<'a, Lit, C> {
	pub fn new(
		x: &'a IntVarEnc<Lit, C>,
		y: &'a IntVarEnc<Lit, C>,
		cmp: LimitComp,
		z: &'a IntVarEnc<Lit, C>,
	) -> Self {
		Self { x, y, cmp, z }
	}
}

impl<'a, Lit: Literal, C: Coefficient> Checker for TernLeConstraint<'a, Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let x = LinExp::from(self.x).assign(solution);
		let y = LinExp::from(self.y).assign(solution);
		let z = LinExp::from(self.z).assign(solution);
		if match self.cmp {
			LimitComp::LessEq => x + y <= z,
			LimitComp::Equal => x + y == z,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

#[allow(dead_code)] // TODO
pub(crate) struct TernLeConstraintContainer<Lit: Literal, C: Coefficient> {
	pub(crate) x: IntVarEnc<Lit, C>,
	pub(crate) y: IntVarEnc<Lit, C>,
	pub(crate) cmp: LimitComp,
	pub(crate) z: IntVarEnc<Lit, C>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraintContainer<Lit, C> {
	#[allow(dead_code)]
	pub(crate) fn get(&'a self) -> TernLeConstraint<'a, Lit, C> {
		TernLeConstraint {
			x: &self.x,
			y: &self.y,
			cmp: self.cmp.clone(),
			z: &self.z,
		}
	}
}

#[derive(Default)]
pub(crate) struct TernLeEncoder {}

impl<'a, DB: ClauseDatabase, C: Coefficient> Encoder<DB, TernLeConstraint<'a, DB::Lit, C>>
	for TernLeEncoder
{
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "tern_le_encoder", skip_all, fields(constraint = format!("{} + {} {} {}", tern.x, tern.y, tern.cmp, tern.z)))
	)]
	fn encode(&mut self, db: &mut DB, tern: &TernLeConstraint<DB::Lit, C>) -> Result {
		// TODO properly use cmp!
		let TernLeConstraint { x, y, cmp, z } = tern;
		if matches!(x, IntVarEnc::Ord(_)) && matches!(x, IntVarEnc::Bin(_)) {
			self.encode(db, &TernLeConstraint::new(*y, *x, cmp.clone(), *z))
		} else if let IntVarEnc::Bin(x_bin) = x {
			if let (IntVarEnc::Const(y_con), IntVarEnc::Const(z_con)) = (y, z) {
				// assert!(
				// 	cmp == &LimitComp::LessEq,
				// 	"Only support <= for x:B+y:Constant ? z:Constant"
				// );
				return lex_lesseq_const(
					db,
					x_bin
						.xs
						.iter()
						.map(|x| Some(x.clone()))
						.collect::<Vec<_>>()
						.as_slice(),
					(*z_con - *y_con).into(),
					x_bin.xs.len(),
				);
			} else if let (IntVarEnc::Bin(y_bin), IntVarEnc::Bin(z_bin)) = (y, z) {
				// assert!(
				// 	cmp == &LimitComp::Equal,
				// 	"Only support == for x:B+y:B ? z:B"
				// );
				log_enc_add(db, &x_bin.xs, &y_bin.xs, &z_bin.xs)
			} else if let (IntVarEnc::Ord(y_ord), IntVarEnc::Bin(z_bin)) = (y, z) {
				let y_bin = IntVarBin::new(db, y_ord.ub(), "x_bin".to_string());
				TernLeEncoder::default()
					.encode(
						db,
						&TernLeConstraint::new(
							&y_ord.clone().into(),
							&IntVarEnc::Const(C::zero()),
							LimitComp::LessEq,
							&y_bin.clone().into(),
						),
					)
					.unwrap();
				self.encode(
					db,
					&TernLeConstraint::new(
						&x_bin.clone().into(),
						&y_bin.into(),
						cmp.clone(),
						&z_bin.clone().into(),
					),
				)
			} else {
				unimplemented!("LHS binary variables only implemented for some cases (and not tested in general method) for {x:?}, {y:?}, {z:?}")
			}
		} else if let (IntVarEnc::Ord(x_ord), IntVarEnc::Ord(y_ord), IntVarEnc::Bin(z_bin)) =
			(x, y, z)
		{
			let dom = ord_plus_ord_le_ord_sparse_dom(
				x.dom().into_iter(..).map(|c| c.end - C::one()).collect(),
				y.dom().into_iter(..).map(|c| c.end - C::one()).collect(),
				z.lb(),
				z.ub(),
			);
			let z_ord = IntVarOrd::new(
				db,
				dom.iter(..).map(|iv| (iv, None)).collect(),
				String::from("z_ord"),
			);
			self.encode(
				db,
				&TernLeConstraint::new(
					&x_ord.clone().into(),
					&y_ord.clone().into(),
					LimitComp::LessEq,
					&z_ord.clone().into(),
				),
			)?;
			self.encode(
				db,
				&TernLeConstraint::new(
					&z_ord.into(),
					&IntVarEnc::Const(C::zero()),
					LimitComp::LessEq,
					&z_bin.clone().into(),
				),
			)
		} else {
			// assert!(cmp == &LimitComp::LessEq, "Only support <= for x+y ? z");
			for c_a in x.dom() {
				for c_b in y.dom() {
					let neg = |clauses: Vec<Vec<DB::Lit>>| -> Vec<Vec<DB::Lit>> {
						if clauses.is_empty() {
							vec![vec![]]
						} else if clauses.contains(&vec![]) {
							vec![]
						} else {
							clauses
								.into_iter()
								.map(|clause| clause.into_iter().map(|lit| lit.negate()).collect())
								.collect()
						}
					};

					// TODO tighten c_c.start
					let c_c = (std::cmp::min(c_a.start, c_b.start))
						..(((c_a.end - C::one()) + (c_b.end - C::one())) + C::one());
					let (a, b, c) = (
						neg(x.geq(c_a.clone())),
						neg(y.geq(c_b.clone())),
						z.geq(c_c.clone()),
					);

					for cls_a in &a {
						for cls_b in &b {
							for cls_c in &c {
								emit_clause!(
									db,
									&[cls_a.clone(), cls_b.clone(), cls_c.clone()].concat()
								)?;
							}
						}
					}
				}
			}
			Ok(())
		}
	}
}

pub(crate) fn ord_plus_ord_le_ord_sparse_dom<C: Coefficient>(
	a: Vec<C>,
	b: Vec<C>,
	l: C,
	u: C,
) -> IntervalSet<C> {
	// TODO optimize by dedup (if already sorted?)
	HashSet::<C>::from_iter(a.iter().flat_map(|a| {
		b.iter().filter_map(move |b| {
			// TODO refactor: use then_some when stabilized
			if *a + *b >= l && *a + *b <= u {
				Some(*a + *b)
			} else {
				None
			}
		})
	}))
	.into_iter()
	.sorted()
	.tuple_windows()
	.map(|(a, b)| (a + C::one())..(b + C::one()))
	.collect::<IntervalSet<_>>()
}

#[cfg(test)]
pub mod tests {
	#![allow(dead_code)]

	use super::*;
	use crate::helpers::tests::{assert_sol, TestDB};
	use iset::interval_set;

	fn get_ord_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: IntervalSet<C>,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarOrd::new(db, dom.into_iter(..).map(|iv| (iv, None)).collect(), lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Ord(x)
	}

	fn get_bin_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		ub: C,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarBin::new(db, ub, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}

	#[test]
	fn constant_test() {
		let c: IntVarEnc<i32, _> = IntVarEnc::Const(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(6..7), Vec::<Vec<i32>>::new());
		assert_eq!(c.geq(45..46), vec![vec![]]);
	}

	#[test]
	fn bin_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_bin_x::<_, i32>(&mut db, 12, true, "x".to_string());
		let x_lin: LinExp<i32, i32> = LinExp::from(&x);

		assert_eq!(x.lits(), 4);
		assert_eq!(x.lb(), 0);
		assert_eq!(x.ub(), 12);
		assert_eq!(x.geq(7..8), vec![vec![1, 4]]); // 7-1=6 == 0110 (right-to-left!)
		assert_eq!(x.geq(5..8), vec![vec![1, 2, 4], vec![2, 4], vec![1, 4]]); // 4=0100,5=0101,6=0110

		assert_eq!(x_lin.assign(&[-1, -2, -3, -4]), 0);
		assert_eq!(x_lin.assign(&[1, -2, -3, -4]), 1);
		assert_eq!(x_lin.assign(&[1, 2, -3, -4]), 3);
		assert_eq!(x_lin.assign(&[1, 2, -3, 4]), 11);
		assert_eq!(x_lin.assign(&[1, 2, 3, 4]), 15);

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			cmp: LimitComp::LessEq,
			z: &IntVarEnc::Const(10), // TODO no consistency implemented for this bound yet
		};

		db.num_var = x.lits() as i32;

		db.generate_solutions(
			|sol| {
				tern.check(sol).is_ok()
					&& match &x {
						IntVarEnc::Bin(b) => b._consistency(),
						_ => unreachable!(),
					}
					.get()
					.check(sol)
					.is_ok()
			},
			db.num_var,
		);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4],
		  vec![1, -2, -3, -4],
		  vec![-1, 2, -3, -4],
		  vec![1, 2, -3, -4],
		  vec![-1, -2, 3, -4],
		  vec![1, -2, 3, -4],
		  vec![-1, 2, 3, -4],
		  vec![1, 2, 3, -4],
		  vec![-1, -2, -3, 4],
		  vec![1, -2, -3, 4],
		  vec![-1, 2, -3, 4],
		]);
	}

	#[test]
	fn bin_geq_2_test() {
		let mut db = TestDB::new(0);
		let x = IntVarBin::new(&mut db, 12, "x".to_string());
		db.num_var = x.lits() as i32;
		let tern = TernLeConstraint {
			x: &IntVarEnc::Bin(x),
			y: &IntVarEnc::Const(0),
			cmp: LimitComp::LessEq,
			z: &IntVarEnc::Const(6),
		};
		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		vec![-1, -2, -3, -4], // 0
		vec![1, -2, -3, -4], // 1
		vec![-1, 2, -3, -4], // 2
		vec![1, 2, -3, -4], // 3
		vec![-1, -2, 3, -4], // 4
		vec![1, -2, 3, -4], // 5
		vec![-1, 2, 3, -4],// 6
		]);
	}

	#[test]
	fn ord_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_ord_x::<_, i32>(
			&mut db,
			interval_set!(3..5, 5..7, 7..11),
			true,
			"x".to_string(),
		);

		let x_lin: LinExp<i32, i32> = LinExp::from(&x);

		assert_eq!(x.lits(), 3);
		assert_eq!(x.lb(), 2);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(6..7), vec![vec![2]]);
		assert_eq!(x.geq(4..7), vec![vec![2]]);

		assert_eq!(x_lin.assign(&[-1, -2, -3]), 2);
		assert_eq!(x_lin.assign(&[1, -2, -3]), 4);
		assert_eq!(x_lin.assign(&[1, 2, -3]), 6);
		assert_eq!(x_lin.assign(&[1, 2, 3]), 10);

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			cmp: LimitComp::LessEq,
			z: &IntVarEnc::Const(6),
		};

		db.num_var = x.lits() as i32;

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3],
		  vec![1, -2, -3],
		  vec![1, 2, -3],
		]);
	}

	#[test]
	fn ord_plus_ord_le_ord_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
			get_ord_x(&mut db, interval_set!(2..3, 4..5), true, "y".to_string()),
			get_ord_x(&mut db, interval_set!(0..4, 4..11), true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, 5, -6],
		  vec![-1, -2, -3, -4, 5, 6],
		  vec![-1, -2, 3, -4, 5, -6],
		  vec![-1, -2, 3, -4, 5, 6],
		  vec![-1, -2, 3, 4, 5, 6],
		  vec![1, -2, -3, -4, 5, -6],
		  vec![1, -2, -3, -4, 5, 6],
		  vec![1, -2, 3, -4, 5, -6],
		  vec![1, -2, 3, -4, 5, 6],
		  vec![1, -2, 3, 4, 5, 6],
		  vec![1, 2, -3, -4, 5, 6],
		  vec![1, 2, 3, -4, 5, 6],
		  vec![1, 2, 3, 4, 5, 6],
				]);
	}

	#[test]
	fn ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
			IntVarEnc::Const(0),
			get_bin_x(&mut db, 7, true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern => vec![
		vec![-1, -2, -3, -4, -5],
		vec![-1, -2, 3, -4, -5],
		vec![1, -2, 3, -4, -5],
		vec![-1, -2, -3, 4, -5],
		vec![1, -2, -3, 4, -5],
		vec![-1, -2, 3, 4, -5],
		vec![1, -2, 3, 4, -5],
		vec![-1, -2, -3, -4, 5],
		vec![1, -2, -3, -4, 5],
		vec![-1, -2, 3, -4, 5],
		vec![1, -2, 3, -4, 5],
		vec![-1, -2, -3, 4, 5],
		vec![1, -2, -3, 4, 5],
		vec![1, 2, -3, 4, 5],
		vec![-1, -2, 3, 4, 5],
		vec![1, -2, 3, 4, 5],
		vec![1, 2, 3, 4, 5],
			 ]);
	}

	#[test]
	fn ord_plus_ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..3), true, "x".to_string()),
			get_ord_x(&mut db, interval_set!(1..4), true, "y".to_string()),
			get_bin_x(&mut db, 6, true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5],
		  vec![-1, -2, 3, -4, -5],
		  vec![-1, -2, -3, 4, -5],
		  vec![1, -2, -3, 4, -5],
		  vec![-1, -2, 3, 4, -5],
		  vec![1, -2, 3, 4, -5],
		  vec![-1, 2, 3, 4, -5],
		  vec![-1, -2, -3, -4, 5],
		  vec![1, -2, -3, -4, 5],
		  vec![-1, 2, -3, -4, 5],
		  vec![-1, -2, 3, -4, 5],
		  vec![1, -2, 3, -4, 5],
		  vec![-1, 2, 3, -4, 5],
		  vec![1, 2, 3, -4, 5],
		  vec![-1, -2, -3, 4, 5],
		  vec![1, -2, -3, 4, 5],
		  vec![-1, 2, -3, 4, 5],
		  vec![1, 2, -3, 4, 5],
		]);
	}

	#[test]
	fn bin_plus_bin_eq_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_bin_x(&mut db, 2, true, "x".to_string()),
			get_bin_x(&mut db, 3, true, "y".to_string()),
			get_bin_x(&mut db, 5, true, "z".to_string()),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::Equal,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarBin<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5, -6, -7],
		  vec![1, -2, -3, -4, 5, -6, -7],
		  vec![-1, -2, 3, -4, 5, -6, -7],
		  vec![-1, 2, -3, -4, -5, 6, -7],
		  vec![1, -2, 3, -4, -5, 6, -7],
		  vec![-1, -2, -3, 4, -5, 6, -7],
		  vec![-1, 2, 3, -4, 5, 6, -7],
		  vec![1, -2, -3, 4, 5, 6, -7],
		  vec![-1, -2, 3, 4, 5, 6, -7],
		  vec![-1, 2, -3, 4, -5, -6, 7],
		  vec![1, -2, 3, 4, -5, -6, 7],
		  vec![-1, 2, 3, 4, 5, -6, 7],
		]
		);
	}

	#[test]
	fn bin_plus_ord_eq_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_bin_x(&mut db, 6, true, String::from("x")),
			get_ord_x(&mut db, interval_set!(1..6), true, String::from("y")),
			get_bin_x(&mut db, 6, true, String::from("z")),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarBin<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5, -6, -7],
		  vec![-1, -2, -3, -4, 5, -6, -7],
		  vec![1, -2, -3, -4, 5, -6, -7],
		  vec![-1, -2, -3, -4, -5, 6, -7],
		  vec![1, -2, -3, -4, -5, 6, -7],
		  vec![-1, 2, -3, -4, -5, 6, -7],
		  vec![-1, -2, -3, -4, 5, 6, -7],
		  vec![1, -2, -3, -4, 5, 6, -7],
		  vec![-1, 2, -3, -4, 5, 6, -7],
		  vec![1, 2, -3, -4, 5, 6, -7],
		  vec![-1, -2, -3, -4, -5, -6, 7],
		  vec![1, -2, -3, -4, -5, -6, 7],
		  vec![-1, 2, -3, -4, -5, -6, 7],
		  vec![1, 2, -3, -4, -5, -6, 7],
		  vec![-1, -2, 3, -4, -5, -6, 7],
		  vec![-1, -2, -3, -4, 5, -6, 7],
		  vec![1, -2, -3, -4, 5, -6, 7],
		  vec![-1, 2, -3, -4, 5, -6, 7],
		  vec![1, 2, -3, -4, 5, -6, 7],
		  vec![-1, -2, 3, -4, 5, -6, 7],
		  vec![1, -2, 3, -4, 5, -6, 7],
		  vec![-1, -2, -3, 4, 5, -6, 7],
		  vec![-1, -2, -3, -4, -5, 6, 7],
		  vec![1, -2, -3, -4, -5, 6, 7],
		  vec![-1, 2, -3, -4, -5, 6, 7],
		  vec![1, 2, -3, -4, -5, 6, 7],
		  vec![-1, -2, 3, -4, -5, 6, 7],
		  vec![1, -2, 3, -4, -5, 6, 7],
		  vec![-1, 2, 3, -4, -5, 6, 7],
		  vec![-1, -2, -3, 4, -5, 6, 7],
		  vec![1, -2, -3, 4, -5, 6, 7],
		]
		);
	}
}
