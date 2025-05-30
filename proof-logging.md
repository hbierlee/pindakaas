# Proof-logging

## Questions/goals/notes meeting 2025-05-30

- [ ] On the doc
- [ ] "Only" defining both dirs, done?
- [ ] Set-up fork / branch
- [ ] Check up Rust experience?
- [ ] RustSAT's bidirectional certification?
  - Is this reverse direction the same as Carlos?
  - Harder question: do they change their encoding?
- Matthew's talk : https://www.youtube.com/watch?v=2U4QSBxsddU&t=3244s

## Potential road map?

- [ ] (Skippable) Ladder encoding (has aux vars, but is very basic)
  - Requires setting up Rust, Pindakaas, Pigeons, VeriPB locally (CI could be nice later)
  - Requires implementing VarLike/ConstraintsLike/ posting reification constraints as `BoolLinear`
- [ ] Totalizer (does not require changes, perhaps normalization)
- [ ] Gen. Totalizer (requires encoding changes; redundant consistency constraints)
- [ ] Gen. Gen. Totalizer for integers (more likely to works out of the box if GT is implemented)

### Notes on GT

- Totalizer, GT, and GGT are all `TotalizerEncoder`
- First, we build an integer model (without encoding variables!) representing the tree using `self.build_totalizer(xs, &lin.cmp, *lin.k);`
- Then the ternary inequalities `x+y<=z` are encoded; I guess we only have to add reification constraints when we encode the integer variables to Boolean variables in `from_dom` for `IntVarOrd`
  - The encoding of the constraint will go `/\ a in D(x), b in D(y) (([x>=a] /\ [y>=b]) -> [z>=a+b])` in some convoluted ways, but this does not require further proof?

## Instructions

- Clone repo: `git clone git@github.com:hbierlee/pindakaas.git`
- Checkout this branch : `git checkout feature/proof-logging`
- To pull in and use the solvers e.g. CaDiCaL, run `git submodule update --remote`
- Run tests with `cargo test`
- You can mostly work from the "sub-crate" ; `cd crates/pindakaas`

### Proof of concept: ladder ladder_encoder

A minimal way to try things out, using the ladder AMO encoding.
We have an Encode trait with a function `fn encode(&self, db: &mut DB, card1: &CardinalityOne) -> Result` returning a `Result<(), Unsatisfiable>` (meaning it returns nothing `()` if succesfull, adding new clause of the AMO constraint `card1` to the ClauseDatabase `db`, but return `Unsatisfiable` if it fails).

Here you can add proof logging, either by directly writing to file and running VeriPB on it, or you can attempt to extend the `pigeons` set-up. To run it, I recommend adding a test like the one I added, `test_cert`, somewhere below, and enabling tracing to see the CNF.

- Add `use traced_test::test;` to your test to see trace!
- Then run test like so: `cargo t --features tracing test_cert -- --show-output`
  - This enables tracing feature so things are traced, and shows output even if the test succeeds

```
running 1 test
╭─╴ladder_encoder: Var(1) + Var(2) + Var(3) ≤ 1
│ Lit(-5) ∨ Lit(4)
│ Lit(-1) ∨ Lit(4)
│ Lit(-1) ∨ Lit(-5)
│ Lit(-4) ∨ Lit(5) ∨ Lit(1)
│ Lit(-6) ∨ Lit(5)
│ Lit(-2) ∨ Lit(5)
│ Lit(-2) ∨ Lit(-6)
│ Lit(-5) ∨ Lit(6) ∨ Lit(2)
│ Lit(-7) ∨ Lit(6)
│ Lit(-3) ∨ Lit(6)
│ Lit(-3) ∨ Lit(-7)
│ Lit(-6) ∨ Lit(7) ∨ Lit(3)
╰─╴time: 134.953µs vars: 0 clauses: 12
test cardinality_one::tests::test_cert ... ok

successes:

---- cardinality_one::tests::test_cert stdout ----
p cnf 7 12
-5 4 0
-1 4 0
-1 -5 0
-4 5 1 0
-6 5 0
-2 5 0
-2 -6 0
-5 6 2 0
-7 6 0
-3 6 0
-3 -7 0
-6 7 3 0
```

## Henk TODOs /roadmap

- look up Gocht's/nordstrom framework
- Fix tracing output:
- Think about encoding/proof argument
- Allow normalization to `>=`
- Enable consistency constraints
- Future: Merge integer branch
- Theory: work out alternative bound/max-based PB reifications example before June 10th meeting with Bart, Dieter
