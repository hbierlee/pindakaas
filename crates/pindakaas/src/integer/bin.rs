use crate::bool_linear::Comparator;
use crate::bool_linear::PosCoeff;
use crate::helpers;
use crate::helpers::new_var;
use crate::integer::{enc::LitOrConst, lex_geq_const, lex_leq_const};
use crate::log;
use std::{collections::BTreeSet, path::PathBuf};

use crate::helpers::emit_clause;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::Dom;
use crate::{
	helpers::{
		add_clauses_for, as_binary, emit_filtered_clause, negate_cnf, pow2, unsigned_binary_range,
	},
	integer::helpers::remove_red,
	ClauseDatabase, Cnf, Coeff, Lit, Unsatisfiable, Var,
};

#[derive(Debug, Clone, Default)]
pub(crate) struct BinEnc {
	pub(crate) x: Vec<LitOrConst>,
}

impl From<Vec<LitOrConst>> for BinEnc {
	fn from(x: Vec<LitOrConst>) -> Self {
		Self { x: x.to_vec() }
	}
}

impl From<PosCoeff> for BinEnc {
	fn from(c: PosCoeff) -> Self {
		Self {
			x: as_binary(c, None)
				.into_iter()
				.map(LitOrConst::from)
				.collect(),
		}
	}
}

impl BinEnc {
	pub(crate) fn new<DB: ClauseDatabase>(db: &mut DB, lits: usize, lbl: Option<String>) -> Self {
		let _lbl = lbl.unwrap_or(String::from("b"));
		Self {
			x: (0..lits)
				.map(|_i| new_var!(db, format!("{_lbl}^{_i}")).into())
				.collect(),
		}
	}

	/// Returns binary encoding of of x{0}+k
	fn from_k(k: Coeff, bits: usize) -> Self {
		Self::from(
			as_binary(PosCoeff::new(k), Some(bits))
				.into_iter()
				.map(LitOrConst::from)
				.collect_vec(),
		)
	}

	pub(crate) fn from_lits(x: &[LitOrConst]) -> Self {
		Self { x: x.to_vec() }
	}

	pub(crate) fn geq_implies(&self, k: Coeff) -> Coeff {
		if k == 0 {
			0
		} else {
			pow2(k.trailing_zeros()) - 1
		}
	}

	/// Encode x:B <=/>= y:B + k
	#[cfg_attr(
    feature = "tracing",
    tracing::instrument(name = "lex", skip_all, fields(constraint = format!("{self} {cmp} {other}")))
)]
	pub(crate) fn lex<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		cmp: Comparator,
		mut other: Self,
		k: Coeff,
	) -> crate::Result {
		let n = std::cmp::max(self.bits(), other.bits());

		fn bit(x: &[LitOrConst], i: usize) -> LitOrConst {
			*x.get(i).unwrap_or(&LitOrConst::Const(false))
		}

		if k != 0 {
			assert!(
				other.x.is_empty(),
				"Can't resolve for different lbs (with non-zero k={k}) yet for non-fixed binary encodings"
			);
			other = Self::from_k(k, self.bits());
		}

		let (x, y, c) = (
			&self.xs(),
			&other.xs(),
			&(0..n)
				.map(|_i| LitOrConst::Lit(new_var!(db, crate::trace::subscripted_name("c", _i))))
				.chain(std::iter::once(LitOrConst::Const(true)))
				.collect_vec(),
		);

		// higher i -> more significant
		for i in 0..n {
			// c = all more significant bits are equal AND current one is
			// if up to i is equal, all preceding must be equal
			emit_filtered_clause(db, [!bit(c, i), bit(c, i + 1)])?;
			// if up to i is equal, x<->y
			emit_filtered_clause(db, [!bit(c, i), !bit(x, i), bit(y, i)])?;
			emit_filtered_clause(db, [!bit(c, i), !bit(y, i), bit(x, i)])?;

			// if not up to i is equal, either preceding bit was not equal, or x!=y
			emit_filtered_clause(db, [bit(c, i), !bit(c, i + 1), bit(x, i), bit(y, i)])?;
			emit_filtered_clause(db, [bit(c, i), !bit(c, i + 1), !bit(x, i), !bit(y, i)])?;

			// if preceding bits are equal, then x<=y (or x>=y)
			match cmp {
				Comparator::LessEq => {
					emit_filtered_clause(db, [!bit(c, i + 1), !bit(x, i), bit(y, i)])
				}
				Comparator::GreaterEq => {
					emit_filtered_clause(db, [!bit(c, i + 1), bit(x, i), !bit(y, i)])
				}
				Comparator::Equal => unreachable!(),
			}?;
		}
		Ok(())
	}
	/// Returns conjunction for x>=k, given x>=b
	pub(crate) fn geqs(&self, k: Coeff, a: Coeff) -> Vec<Vec<Lit>> {
		let (range_lb, range_ub) = self.range();

		if k > range_ub {
			vec![]
		} else {
			assert!(k <= a);
			let k = k.clamp(range_lb, range_ub);
			std::iter::successors(Some(k), |k: &Coeff| {
				let k = k + if k == &0 { 1 } else { pow2(k.trailing_zeros()) };
				if k < a {
					Some(k)
				} else {
					None
				}
			})
			.map(|k| {
				as_binary(PosCoeff::new(k), Some(self.bits()))
					.iter()
					.zip(self.xs().iter().cloned())
					// since geq, find 1's
					.filter_map(|(b, x)| b.then_some(x))
					.filter_map(|x| match x {
						// TODO Move cnf: Vec<Vec<Lit>> functions into Cnf
						LitOrConst::Lit(x) => Some(Ok(x)),
						LitOrConst::Const(true) => None, // literal satisfied
						LitOrConst::Const(false) => Some(Err(Unsatisfiable)), // clause falsified
					})
					.try_collect()
					.unwrap_or_default()
			})
			.collect()
		}
	}

	/// The encoding range
	pub(crate) fn range(&self) -> (Coeff, Coeff) {
		let (range_lb, range_ub) = unsigned_binary_range(self.bits());
		let (range_lb, range_ub) = (*range_lb, *range_ub); // TODO replace all Coeff for PosCoeff in bin.rs
		(range_lb, range_ub)
	}

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub(crate) fn geq(&self, k: Coeff) -> Vec<Lit> {
		let (range_lb, range_ub) = self.range();
		if k > range_ub {
			vec![]
		} else {
			let k = k.clamp(range_lb, range_ub);
			as_binary(PosCoeff::new(k), Some(self.bits()))
				.into_iter()
				.zip(self.xs().iter().cloned())
				// if >=, find 1's, if <=, find 0's
				.filter_map(|(b, x)| b.then_some(x))
				.filter_map(|x| match x {
					// THIS IS A CONJUNCTION
					// TODO make this a bit more clear (maybe simplify function for Cnf)
					LitOrConst::Lit(x) => Some(Ok(x)),
					LitOrConst::Const(true) => None, // literal satisfied
					LitOrConst::Const(false) => Some(Err(Unsatisfiable)), // clause falsified
				})
				.try_collect()
				.unwrap_or_default()
		}
	}

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub(crate) fn ineqs(&self, r_a: Coeff, r_b: Coeff, up: bool) -> Vec<Vec<Lit>> {
		let (range_lb, range_ub) = self.range();

		log!("\t {up} {r_a}..{r_b} [{range_lb}..{range_ub}] -> ");

		if r_a <= range_lb {
			if up {
				return vec![];
			} else {
				return vec![vec![]];
			}
		}

		if r_b > range_ub {
			if up {
				return vec![vec![]];
			} else {
				return vec![];
			}
		}

		let ineqs = (r_a..=r_b)
			.flat_map(|k| {
				let k = if up { k - 1 } else { k };
				#[allow(
					clippy::let_and_return,
					reason = "we need ineq in case of trace enabled"
				)]
				let ineq = self.ineq(k, up); // returns cnf
				log!("{k} -> ineq = {ineq:?}");
				ineq
			})
			.collect_vec();

		// TODO refactor; just got it working
		// // Returning CNF; so a single empty clause
		if ineqs == vec![vec![]] {
			return vec![];
		}

		let ineqs = if up {
			ineqs
		} else {
			ineqs.into_iter().rev().collect()
		};

		if up {
			remove_red(ineqs.into_iter().rev().collect())
				.into_iter()
				.rev()
				.collect_vec()
		} else {
			remove_red(ineqs.into_iter().rev().collect())
		}
	}

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub(crate) fn ineq(&self, k: Coeff, up: bool) -> Vec<Vec<Lit>> {
		let clause: Result<Vec<_>, _> = as_binary(PosCoeff::new(k), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter().cloned())
			// if >=, find 0's, if <=, find 0's
			// .filter_map(|(b, x)| (b != up).then_some(x))
			.filter_map(|(b, x)| (b != up).then_some(x))
			// if <=, negate lits at 0's
			.map(|x| if up { x } else { !x })
			.filter_map(|x| match x {
				// This is a DISJUNCTION
				// TODO Move cnf: Vec<Vec<Lit>> functions into Cnf
				LitOrConst::Lit(x) => Some(Ok(x)),
				LitOrConst::Const(false) => None, // literal falsified
				LitOrConst::Const(true) => Some(Err(Unsatisfiable)), // clause satisfied
			})
			.try_collect();

		match clause {
			Err(Unsatisfiable) => vec![],
			Ok(clause) if clause.is_empty() => vec![],
			Ok(clause) => vec![clause],
		}
	}

	/// Get encoding literals
	pub(crate) fn xs(&self) -> Vec<LitOrConst> {
		self.x.clone()
	}

	/// Get complement
	pub(crate) fn complement(self) -> Self {
		Self::from_lits(&self.xs().into_iter().map(|l| !l).collect_vec())
	}

	/// Constraints bounds and gaps
	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB, dom: &Dom) -> crate::Result {
		self.encode_unary_constraint(db, &Comparator::GreaterEq, dom.lb(), dom, true)?;
		self.encode_unary_constraint(db, &Comparator::LessEq, dom.ub(), dom, true)?;
		for (a, b) in dom.ranges.iter().tuple_windows() {
			for k in (a.1 + 1)..=(b.0 - 1) {
				self.encode_neq(db, k, dom)?;
			}
		}
		Ok(())
	}

	/// Encode `x # k` where `# ∈ {≤,=,≥}`
	#[cfg_attr(
		feature = "tracing",
		tracing::instrument(name = "unary", skip_all, fields(constraint = format!("{} {cmp} {k}", self)))
	)]
	pub(crate) fn encode_unary_constraint<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		cmp: &Comparator,
		k: Coeff,
		dom: &Dom,
		force: bool,
	) -> crate::Result {
		match cmp {
			Comparator::LessEq => {
				if k < dom.lb() {
					Err(Unsatisfiable)
				} else if k >= dom.ub() && !force {
					Ok(())
				} else {
					lex_leq_const(db, &self.xs(), self.normalize(k, dom), self.bits())
				}
			}
			Comparator::Equal => add_clauses_for(db, vec![self.eq(k, dom)]),
			Comparator::GreaterEq => {
				if k > dom.ub() {
					Err(Unsatisfiable)
				} else if k <= dom.lb() && !force {
					Ok(())
				} else {
					lex_geq_const(db, &self.xs(), self.normalize(k, dom), self.bits())
				}
			}
		}
	}

	/// Return conjunction of bits equivalent where `x=k`
	fn eq(&self, k: Coeff, dom: &Dom) -> Vec<Vec<Lit>> {
		as_binary(self.normalize(k, dom), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter())
			.map(|(b, x)| if b { *x } else { !*x })
			.flat_map(|x| match x {
				LitOrConst::Lit(lit) => Some(Ok(vec![lit])),
				LitOrConst::Const(true) => None,
				LitOrConst::Const(false) => Some(Err(Unsatisfiable)),
			})
			.try_collect()
			.unwrap_or(vec![vec![]])
	}

	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn normalize(&self, k: Coeff, dom: &Dom) -> PosCoeff {
		PosCoeff::new(k - dom.lb())
	}

	// TODO Coeff -> PosCoeff
	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn denormalize(&self, k: Coeff, dom: &Dom) -> Coeff {
		k + dom.lb()
	}

	#[cfg_attr(
		feature = "tracing",
		tracing::instrument(name = "unary", skip_all, fields(constraint = format!("{} != {k}", self)))
	)]
	pub(crate) fn encode_neq<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		k: Coeff,
		dom: &Dom,
	) -> crate::Result {
		add_clauses_for(db, vec![negate_cnf(self.eq(k, dom))])
	}

	pub(crate) fn as_lin_exp(&self) -> (Vec<(Lit, Coeff)>, Coeff) {
		let mut add = 0; // resulting from fixed terms

		(
			self.x
				.iter()
				.enumerate()
				.filter_map(|(k, x)| {
					let a = pow2(k as u32);

					match x {
						LitOrConst::Lit(l) => Some((*l, a)),
						LitOrConst::Const(true) => {
							add += a;
							None
						}
						LitOrConst::Const(false) => None,
					}
				})
				.collect::<Vec<_>>(),
			add,
		)
	}

	pub(crate) fn lits(&self) -> BTreeSet<Var> {
		self.x
			.clone()
			.into_iter()
			.filter_map(|x| match x {
				LitOrConst::Lit(x) => Some(x.var()),
				LitOrConst::Const(_) => None,
			})
			.collect()
	}

	// TODO u32 -> usize
	/// Number of bits in the encoding
	pub(crate) fn bits(&self) -> usize {
		self.x.len()
	}

	#[cfg_attr(
	feature = "tracing",
	tracing::instrument(name = "scm_dnf", skip_all, fields(constraint = format!("DNF:{c}*{self}")))
)]
	pub(crate) fn scm_dnf<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		c: Coeff,
	) -> Result<Self, Unsatisfiable> {
		if c == 1 {
			return Ok(self.clone());
		}
		// assume shifts; all Const(false) at front
		// TODO add assertion for this
		let bits = self.bits(); // all
		let lits = self.lits().len(); // unfixed
		let xs = self
			.xs()
			.into_iter()
			.skip(bits - lits)
			.map(|x| match x {
				LitOrConst::Lit(x) => x,
				LitOrConst::Const(_) => panic!("Fixed bits not at front in {self}"),
			})
			.collect_vec();

		// TODO [!] remove reading, check in Cnf objects based on dimacs files
		let cnf = Cnf::from_file(&PathBuf::from(format!(
			"{}/res/ecm/{lits}_{c}.dimacs",
			env!("CARGO_MANIFEST_DIR")
		)))
		.unwrap_or_else(|_| panic!("Could not find Dnf method cnf for {lits}_{c}"));
		// TODO [?] could replace with some arithmetic. Using VarRange?
		let map = cnf
			.vars()
			.zip_longest(xs.iter())
			.flat_map(|yx| match yx {
				itertools::EitherOrBoth::Both(x, y) => Some((x, *y)),
				itertools::EitherOrBoth::Left(x) => {
					// var in CNF but not in x -> new var y
					Some((x, new_var!(db, format!("scm_{x}"))))
				}
				itertools::EitherOrBoth::Right(_) => unreachable!(), // cnf has at least as many vars as xs
			})
			.collect::<FxHashMap<_, _>>();

		// add clauses according to Dnf
		cnf.iter().try_for_each(|clause| {
			emit_clause!(
				db,
				clause
					.iter()
					.map(|x| {
						let lit = map[&x.var()];
						if x.is_negated() {
							!lit
						} else {
							lit
						}
					})
					.collect::<Vec<_>>()
			)
		})?;

		let lits = [false]
			.repeat(bits - lits)
			.into_iter()
			.map(LitOrConst::from)
			.chain(map.into_values().sorted().skip(lits).map(LitOrConst::from))
			.collect_vec();
		Ok(BinEnc::from_lits(&lits))
	}
}

impl std::fmt::Display for BinEnc {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(
			f,
			"({}){}",
			self.x.iter().rev().join(""),
			helpers::subscript_number(2).format("")
		)
	}
}

#[cfg(test)]
mod tests {
	use helpers::tests::{assert_encoding, expect_file};

	use super::*;

	#[test]
	fn test_geqs() {
		let mut cnf = Cnf::default();
		let x = BinEnc::new(&mut cnf, 3, Some(String::from("x")));
		cnf.add_clauses(x.geqs(1, 6)).unwrap();
		assert_encoding(&cnf, &expect_file!("integer/bin/geq_1_6.cnf"));
	}

	#[test]
	fn test_ineq() {
		let mut cnf = Cnf::default();
		let x = BinEnc::new(&mut cnf, 2, Some(String::from("x")));
		for k in 0..=3 {
			assert_encoding(
				&Cnf::try_from(vec![dbg!(x.geq(k))]).unwrap_or_else(|e| e.into()),
				&expect_file![format!("integer/bin/geq_{k}.cnf")],
			);
		}
	}
}