#![allow(
	unused_qualifications,
	reason = "pyo3 macro will generate unused qualified types"
)]

use std::{fmt::Display, ops::DerefMut, path::PathBuf};

use ::pindakaas as base;
use base::{
	bool_linear::{BoolLinExp, BoolLinear, Comparator, LinearEncoder},
	ClauseDatabase, Encoder,
};
use pyo3::{exceptions::PyArithmeticError, prelude::*};

type Clause = Vec<Lit>;

#[pyclass]
struct ClauseIter {
	inner: std::vec::IntoIter<Clause>,
}

#[pyclass(name = "CNF")]
struct Cnf(base::Cnf);

#[pyclass]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(base::Lit);

#[pyfunction]
fn adder_encode(mut db: PyRefMut<'_, Cnf>) -> Result<(), PyErr> {
	let pref = db.deref_mut();
	let db = &mut pref.0;
	let x = BoolLinExp::from_slices(
		&[1, 2, 3],
		&[
			db.new_var().into(),
			db.new_var().into(),
			db.new_var().into(),
		],
	);
	let con = BoolLinear::new(x, Comparator::Equal, 2);
	let enc: LinearEncoder = LinearEncoder::default();
	enc.encode(db, &con)
		.map_err(|_e| PyArithmeticError::new_err("Unsatisfiable"))
}

#[pymodule]
fn pindakaas(m: &Bound<'_, PyModule>) -> PyResult<()> {
	m.add_class::<Cnf>()?;
	m.add_function(wrap_pyfunction!(adder_encode, m)?)?;
	Ok(())
}

#[pymethods]
impl ClauseIter {
	fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
		slf
	}
	fn __next__(mut slf: PyRefMut<'_, Self>) -> Option<Clause> {
		slf.inner.next()
	}
}

#[pymethods]
impl Cnf {
	fn __iter__(&self) -> ClauseIter {
		// FIXME: It would be great if this could be made lazily instead of copying everything when creating the iterator
		// ClauseIter {
		// 	inner: Vec::from_iter(self.0.iter().map(Vec::from)).into_iter(),
		// }
		todo!()
	}

	fn __str__(&self) -> String {
		self.0.to_string()
	}
	#[staticmethod]
	fn from_file(path: PathBuf) -> Result<Self, std::io::Error> {
		Ok(Self(base::Cnf::from_file(&path)?))
	}
	#[new]
	fn new() -> Self {
		Self(base::Cnf::default())
	}
}
impl Lit {
	pub fn is_negated(&self) -> bool {
		self.0.is_negated()
	}
	pub fn var(&self) -> Self {
		Self(self.0.var().into()) // TODO
	}
}
impl Display for Lit {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.0.fmt(f)
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn it_works() {
		let result = 2 + 2;
		assert_eq!(result, 4);
	}
}
