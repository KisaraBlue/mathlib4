# mathlib4

Work in progress mathlib port for Lean 4.
This is not a port.
It is still trying things out
to gain experience for
the real port.
Anything that is currently in mathlib4 is subject to change/deletion,
and the "real" port hasn't started yet

# Tate's algorithm

Implementation of Tate's algorithm for elliptic curves is mathlib4:
* Some personal ports of Group/Int/Nat/Ring lemmas
* An definition of extended natural numbers 'Enat.lean'
* An implementation of the Kronecker symbol for integers 'Kronecker.lean'
* An environment for the models and quantities associated to elliptic curves 'Model.lean'
* An extension of commutative rings with a normalized valuation 'ValuedRing.lean'
* An implementation of Tate's algorithm over the integers 'TateInt.lean'
* A test to compare our output with LMFDB's data 'DataTest.lean'


# Build instructions

* Get the newest version of `elan`. If you already have installed a version of Lean, you can run
  ```
  elan self update
  ```
  If the above command fails, or if you need to install `elan`, run
  ```
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
  If this also fails, follow the instructions under `Regular install` [here](https://leanprover-community.github.io/get_started.html).
* To build `mathlib4` run `lake build`. To build and run all tests, run `make`.
* If you added a new file, run the following command to update `Mathlib.lean`
  ```
  find Mathlib -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Mathlib.lean
  ```
