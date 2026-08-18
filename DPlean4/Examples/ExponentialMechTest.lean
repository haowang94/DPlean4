/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Exponential
import DPlean4.Basic.Adjacency

/-!
# Exponential Mechanism Tests

End-to-end examples verifying the exponential mechanism.
-/

namespace DPlean4

open scoped NNReal

section BoolOutput

/-! ### Private binary selection

Select True or False privately based on how many elements satisfy a predicate.
Utility u(d, True) = number of elements satisfying predicate.
Utility u(d, False) = number of elements NOT satisfying predicate. -/

variable {α : Type*} [DecidableEq α]

/-- Utility: count of elements satisfying a predicate. -/
def boolCountUtility (p : α → Prop) [DecidablePred p] (l : List α) (b : Bool) : ℝ :=
  if b then (l.filter (fun a => p a)).length
  else (l.filter (fun a => ¬ p a)).length

/-- Adding/removing one element changes count by at most 1. -/
theorem boolCountUtility_sensitivity (p : α → Prop) [DecidablePred p] :
    HasUtilitySensitivity ListAddRemove (boolCountUtility p) 1 := by
  intro l₁ l₂ hadj b
  simp only [boolCountUtility]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj <;> rw [h.1, h.2] <;> split_ifs <;>
    simp [List.filter_cons, List.length_cons] <;>
    split_ifs <;> simp [Nat.cast_add, Nat.cast_one] <;> norm_num

/-- Private selection of True/False with ε-DP via exponential mechanism. -/
theorem private_bool_select (p : α → Prop) [DecidablePred p] (ε : NNReal) :
    IsPureDP ListAddRemove
      (expMech (boolCountUtility p) (ε : ℝ) 1) ε :=
  expMech_isPureDP (by norm_num : (0 : ℝ) < 1) (boolCountUtility_sensitivity p)

end BoolOutput

end DPlean4
