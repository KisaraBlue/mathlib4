/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn
-/

import Std.Data.Int.Basic
import Std.Data.Int.Lemmas
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Notation
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Coe
import Mathlib.Algebra.Ring.Basic
open Nat Int

instance : LinearOrder Int where
  le := (·≤·)
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := (·<·)
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  decidable_eq := by infer_instance
  decidable_le := by infer_instance
  decidable_lt := by infer_instance
