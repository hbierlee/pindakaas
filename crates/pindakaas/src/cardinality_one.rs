use itertools::Itertools;

use crate::{
	bool_linear::{LimitComp, NormalizedBoolLinear},
	helpers::{emit_clause, new_var},
	Checker, ClauseDatabase, Encoder, Lit, Result, Valuation,
};

/// An encoder for [`CardinalityOne`] constraints that uses a logarithm
/// encoded selector variable to ensure the selection of at most one of
/// the given literals
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct BitwiseEncoder {}

#[derive(Debug, Clone)]
pub struct CardinalityOne {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
}

/// An encoder for an At Most One constraints that TODO
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LadderEncoder {}

/// An encoder for an At Most One constraints that for every pair of literals
/// states that one of the literals has to be `false`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PairwiseEncoder {}

pub(crate) fn at_least_one_clause<DB: ClauseDatabase>(
	db: &mut DB,
	card1: &CardinalityOne,
) -> Result {
	debug_assert_eq!(card1.cmp, LimitComp::Equal);
	emit_clause!(db, card1.lits.iter().copied())
}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne> for BitwiseEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "bitwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut DB, card1: &CardinalityOne) -> Result {
		let size = card1.lits.len();
		let bits = (usize::BITS - (size - 1).leading_zeros()) as usize;

		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?;
		}

		// Create a log encoded selection variable
		let signals = (0..bits).map(|_| new_var!(db)).collect_vec();

		// Enforce that literal can only be true when selected
		for (i, lit) in card1.lits.iter().enumerate() {
			for (j, sig) in signals.iter().enumerate() {
				if i & (1 << j) != 0 {
					emit_clause!(db, [!lit, *sig])?;
				} else {
					emit_clause!(db, [!lit, !sig])?;
				}
			}
		}

		Ok(())
	}
}

impl CardinalityOne {
	#[cfg(any(feature = "tracing", test))]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(self.lits.iter().map(trace_print_lit), " + ");
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} 1")
	}
}

impl Checker for CardinalityOne {
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<()> {
		NormalizedBoolLinear::from(self.clone()).check(value)
	}
}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne> for LadderEncoder {
	#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "ladder_encoder", skip_all, fields(constraint = card1.trace_print()))
)]
	fn encode(&self, db: &mut DB, card1: &CardinalityOne) -> Result {
		// TODO could be slightly optimised to not introduce fixed lits
		let mut a = new_var!(db); // y_v-1
		if card1.cmp == LimitComp::Equal {
			emit_clause!(db, [a])?;
		}
		for x in card1.lits.iter() {
			let b = new_var!(db); // y_v
			emit_clause!(db, [!b, a])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			emit_clause!(db, [!x, a])?; // x_v -> y_v-1
			emit_clause!(db, [!x, !b])?; // x_v -> ¬y_v
			emit_clause!(db, [!a, b, *x])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		if card1.cmp == LimitComp::Equal {
			emit_clause!(db, [!a])?;
		}
		Ok(())
	}
}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne> for PairwiseEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "pairwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut DB, card1: &CardinalityOne) -> Result {
		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?;
		}
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in card1.lits.iter().tuple_combinations() {
			emit_clause!(db, [!a, !b])?;
		}
		Ok(())
	}
}

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! card1_test_suite {
		($mod_name:ident, $encoder:expr) => {
			mod $mod_name {
				use itertools::Itertools;

				use crate::{
					bool_linear::LimitComp,
					cardinality_one::CardinalityOne,
					helpers::tests::{assert_checker, assert_solutions, expect_file},
					ClauseDatabase, Cnf, Encoder,
				};

				const LARGE_N: usize = 50;
				// ------ At Most One testing ------
				#[test]
				fn test_amo_pair() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_amo_pair.sol"],
					);
				}
				#[test]
				fn test_amo_one_neg() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, !b],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_amo_one_neg.sol"],
					);
				}
				#[test]
				fn test_amo_neg_only() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![!a, !b],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_amo_neg_only.sol"],
					);
				}
				#[test]
				fn test_amo_triple() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b, c],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["cardinality_one/test_amo_triple.sol"],
					);
				}
				#[test]
				fn test_amo_large() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone(),
						cmp: LimitComp::LessEq,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn test_amo_large_neg() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone().into_iter().map(|l| !l).collect_vec(),
						cmp: LimitComp::LessEq,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn test_amo_large_mix() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();

					let con = CardinalityOne {
						lits: vars
							.clone()
							.into_iter()
							.enumerate()
							.map(|(i, l)| if i % 2 == 0 { l } else { !l })
							.collect_vec(),
						cmp: LimitComp::LessEq,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				// ------ Exactly One testing ------
				#[test]
				fn test_eo_pair() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_eo_pair.sol"],
					);
				}
				#[test]
				fn test_eo_one_neg() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, !b],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_eo_one_neg.sol"],
					);
				}
				#[test]
				fn test_eo_neg_only() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![!a, !b],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_eo_neg_only.sol"],
					);
				}
				#[test]
				fn test_eo_triple() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b, c],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["cardinality_one/test_eo_triple.sol"],
					);
				}
				#[test]
				fn test_eo_large() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone(),
						cmp: LimitComp::Equal,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn test_eo_large_neg() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone().iter().map(|l| !l).collect_vec(),
						cmp: LimitComp::Equal,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn test_eo_large_mix() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars
							.clone()
							.into_iter()
							.enumerate()
							.map(|(i, l)| if i % 2 == 0 { l } else { !l })
							.collect_vec(),
						cmp: LimitComp::Equal,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
			}
		};
	}

	pub(crate) use card1_test_suite;

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{BitwiseEncoder, CardinalityOne, LadderEncoder, PairwiseEncoder},
		helpers::tests::{assert_encoding, assert_solutions, expect_file},
		ClauseDatabase, Cnf, Encoder,
	};

	#[test]
	fn test_amo_pairwise() {
		// AMO on two literals
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise1.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise1.sol"],
		);
		// AMO on a negated literals
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, !b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise2.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise2.sol"],
		);
		// AMO on three literals
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b, c],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise3.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise3.sol"],
		);
	}

	#[test]
	fn test_eo_bitwise() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		BitwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/bitwise/test_eo_bitwise.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/bitwise/test_eo_bitwise.sol"],
		);
	}

	#[test]
	fn test_eo_ladder() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		LadderEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/ladder/test_eo_ladder.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/ladder/test_eo_ladder.sol"],
		);
	}

	card1_test_suite! {
			bitwise_encoder,
			crate::cardinality_one::BitwiseEncoder::default()
	}
	card1_test_suite! {
			ladder_encoder,
			crate::cardinality_one::LadderEncoder::default()
	}
	card1_test_suite! {
			pairwise_encoder,
			crate::cardinality_one::PairwiseEncoder::default()
	}
}
