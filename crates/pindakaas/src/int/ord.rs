use std::collections::HashSet;

use itertools::Itertools;

use crate::{
	helpers::negate_cnf,
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Literal,
};

use super::Dom;

#[derive(Debug, Clone)]
pub struct OrdEnc<Lit: Literal> {
	pub(crate) x: Vec<Lit>,
}

impl<Lit: Literal> OrdEnc<Lit> {
	pub fn new<DB: ClauseDatabase<Lit = Lit>, C: Coefficient>(
		db: &mut DB,
		dom: &Dom<C>,
		_lbl: Option<&String>,
	) -> Self {
		let _lbl = _lbl.cloned().unwrap_or(String::from("b"));
		Self {
			x: dom
				.iter()
				.skip(1)
				.map(|_v| new_var!(db, format!("{_lbl}≥{_v}")))
				.collect(),
		}
	}

	pub fn from_lits(x: &[Lit]) -> Self {
		Self { x: x.to_vec() }
	}

	// pub fn iter(&self) -> impl Iterator<Item = Vec<Lit>> {
	pub fn ineqs(&self, up: bool) -> Vec<(Vec<Vec<Lit>>, bool)> {
		if up {
			[(vec![], false)]
				.into_iter()
				.chain(self.x.iter().map(|x| (vec![vec![x.clone()]], true)))
				.collect()
		} else {
			self.x
				.iter()
				.map(|x| (vec![vec![x.negate()]], true))
				.chain([(vec![], false)])
				.collect()
		}
	}

	/// From domain position to cnf
	pub(crate) fn geq(&self, p: Option<usize>) -> Vec<Vec<Lit>> {
		match p {
			Some(0) => {
				vec![]
			} // true
			Some(p) => {
				vec![vec![self.x[p - 1].clone()]]
			} // lit
			None => {
				vec![vec![]]
			} // false
		}
	}

	/// From domain position to cnf
	pub(crate) fn _ineq(&self, p: Option<usize>, up: bool) -> Vec<Vec<Lit>> {
		let geq = match p {
			Some(0) => {
				vec![]
			} // true
			Some(p) => {
				vec![vec![self.x[p - 1].clone()]]
			} // lit
			None => {
				vec![vec![]]
			} // false
		};
		if up {
			geq
		} else {
			negate_cnf(geq)
		}
	}

	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> crate::Result {
		self.x.iter().tuple_windows().try_for_each(|(a, b)| {
			if a.var() != b.var() {
				emit_clause!(db, &[b.negate(), a.clone()])
			} else {
				Ok(())
			}
		})
	}

	// pub(crate) fn as_lin_exp<C: Coefficient>(&self) -> LinExp<Lit, C> {
	// 	let mut acc = self.lb();
	// 	LinExp::new()
	// 		.add_chain(
	// 			&self
	// 				.xs
	// 				.iter(..)
	// 				.map(|(iv, lit)| {
	// 					let v = iv.end - C::one() - acc;
	// 					acc += v;
	// 					(lit.clone(), v)
	// 				})
	// 				.collect::<Vec<_>>(),
	// 		)
	// 		.add_constant(self.lb())
	// }

	pub(crate) fn lits(&self) -> HashSet<Lit> {
		self.x.clone().into_iter().map(|lit| lit.var()).collect()
	}

	pub(crate) fn iter(&self) -> impl Iterator<Item = &Lit> {
		self.x.iter()
	}
}

impl<Lit: Literal> std::fmt::Display for OrdEnc<Lit> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "[{}]", self.x.iter().join(", "))
	}
}

#[cfg(test)]
mod tests {
	// type Lit = i32;
	// type C = i64;

	use super::*;
	use crate::helpers::tests::TestDB;
	#[test]
	fn test_ineq() {
		// let mut model = Model::<Lit, C>::default();
		// let x = model
		// 	.new_var(&[2, 5, 6, 7, 9], true, None, Some(String::from("x")))
		// 	.unwrap();
		// let x = IntVar::<Lit, C>::new(1, &[2, 5, 6, 7, 9], true, None, Some(String::from("x")))
		// 	.into_ref();
		let mut db = TestDB::new(0);
		let x = OrdEnc::new(&mut db, &Dom::from_slice(&[2, 5, 6, 7, 9]), None);

		for (_up, dom_pos, expected_cnf) in [
			(true, Some(0), vec![]),
			(true, Some(1), vec![vec![1]]),
			(true, Some(2), vec![vec![2]]),
			(true, Some(3), vec![vec![3]]),
			(true, Some(4), vec![vec![4]]),
			(true, None, vec![vec![]]),
			// (false, Some(0), vec![vec![]]),
			// (false, Some(1), vec![vec![-1]]),
			// (false, Some(2), vec![vec![-2]]),
			// (false, Some(3), vec![vec![-3]]),
			// (false, Some(4), vec![vec![-4]]),
			// (false, None, vec![]),
		] {
			assert_eq!(
				x.geq(dom_pos),
				expected_cnf,
				"Domain pos {dom_pos:?} was expected to return {expected_cnf:?}"
			);
		}
	}
}