use std::num::NonZeroI32;

pub use splr::Solver as Splr;
use splr::{Certificate, SatSolverIF, SolveIF, VERSION};

use crate::{
	helpers::const_concat,
	solver::{SolveResult, Solver},
	ClauseDatabase, Cnf, ConditionalDatabase, Lit, Valuation, Var, VarRange,
};

impl Valuation for Certificate {
	fn value(&self, lit: Lit) -> bool {
		if let Certificate::SAT(sol) = self {
			let var = lit.var();
			let v = Into::<i32>::into(var) as usize;
			if v <= sol.len() {
				debug_assert_eq!(sol[v - 1].abs(), lit.var().into());
				sol[v - 1] == lit.into()
			} else {
				false
			}
		} else {
			panic!("value called on an unsatisfiable certificate")
		}
	}
}

impl ClauseDatabase for Splr {
	type CondDB = Self;

	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> crate::Result {
		use splr::SolverError::*;

		let cl: Vec<_> = cl.into_iter().map(Into::<i32>::into).collect();
		match SatSolverIF::add_clause(self, cl) {
			Ok(_) => Ok(()),
			Err(e) => match e {
				InvalidLiteral => panic!("clause referenced a non-existing variable"),
				RootLevelConflict(_) | EmptyClause | Inconsistent => Err(crate::Unsatisfiable),
				TimeOut => unreachable!(),
				SolverBug | UndescribedError | IOError | OutOfMemory => {
					panic!("an error occured in splr while adding a clause")
				}
			},
		}
	}

	fn new_var(&mut self) -> Var {
		let var = self.add_var();
		let var: i32 = var.try_into().expect("exhausted variable pool");
		Var(NonZeroI32::new(var).expect("variables cannot use the value zero"))
	}

	fn new_var_range(&mut self, len: usize) -> VarRange {
		let start = self.new_var();
		let mut last = start;
		for _ in 1..len {
			let x = self.new_var();
			debug_assert_eq!(i32::from(last) + 1, i32::from(x));
			last = x;
		}
		VarRange::new(start, last)
	}

	fn with_conditions(&mut self, conditions: Vec<Lit>) -> ConditionalDatabase<Self::CondDB> {
		ConditionalDatabase {
			db: self,
			conditions,
		}
	}
}

impl From<&Cnf> for Splr {
	fn from(cnf: &Cnf) -> Self {
		use splr::{
			types::{CNFDescription, Instantiate},
			Config,
		};
		let mut slv = Splr::instantiate(
			&Config::default(),
			&CNFDescription {
				num_of_variables: cnf.nvar.emited_vars(),
				..CNFDescription::default()
			},
		);
		for cl in cnf.iter() {
			// Ignore early detected unsatisfiability
			let _ = ClauseDatabase::add_clause(&mut slv, cl.iter().copied());
		}
		slv
	}
}

impl Solver for Splr {
	fn signature(&self) -> &str {
		const SPLR_SIG: &str = const_concat!("SPLR-", VERSION);
		SPLR_SIG
	}

	#[allow(
		refining_impl_trait,
		reason = "user can use more specific type if needed"
	)]
	fn solve(&mut self) -> SolveResult<Certificate, ()> {
		use splr::SolverError::*;

		match SolveIF::solve(self) {
			Ok(Certificate::UNSAT) => SolveResult::Unsatisfiable(()),
			Ok(cert @ Certificate::SAT(_)) => SolveResult::Satisfied(cert),
			Err(e) => match e {
				InvalidLiteral => panic!("clause referenced a non-existing variable"),
				Inconsistent => SolveResult::Unsatisfiable(()),
				RootLevelConflict(_) => SolveResult::Unsatisfiable(()),
				TimeOut | OutOfMemory => SolveResult::Unknown,
				_ => panic!("an error occurred within the splr solver"),
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	// use crate::{linear::LimitComp, solver::SolveResult, CardinalityOne, Encoder, PairwiseEncoder};

	#[test]
	fn test_splr() {
		let mut _slv = splr::Solver::default();

		// TODO: Something weird is happening with the Variables
		// let a = slv.new_var().into();
		// let b = slv.new_var().into();
		// PairwiseEncoder::default()
		// 	.encode(
		// 		&mut slv,
		// 		&CardinalityOne {
		// 			lits: vec![a, b],
		// 			cmp: LimitComp::Equal,
		// 		},
		// 	)
		// 	.unwrap();
		// let SolveResult::Satisfied(solution) = slv.solve() else {
		// 	unreachable!()
		// };
		// assert!(
		// 	(solution.value(!a) && solution.value(b)) || (solution.value(a) && solution.value(!b))
		// );
	}
}
