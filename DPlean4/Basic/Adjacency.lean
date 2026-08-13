/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.Data.List.Basic

/-!
# Adjacency Relations for Differential Privacy

This file defines adjacency relations on databases for differential privacy.

## Main Definitions

* `ListAddRemove`: Adjacency via addition or removal of a single element (unbounded DP)
* `ListReplace`: Adjacency via replacement of a single element (bounded DP)

## Design Notes

Adjacency is treated as a **relation parameter**, not a typeclass. A single database type
can have multiple meaningful adjacency relations (add/remove vs replace, different distance
bounds), so baking one choice into a typeclass would be incorrect.

DP definitions and theorems are parameterized over an adjacency relation:
```lean
variable (adj : D → D → Prop)
```

This design follows the principle that adjacency conventions must be explicit in every
theorem statement, as different conventions yield different privacy bounds.
-/

namespace DPlean4

section ListAdjacency

variable {α : Type*}

/-- Two lists are adjacent via add/remove if one can be obtained from the other by
    adding or removing exactly one element. This is the standard adjacency for unbounded DP.

    Example: [1,2,3] and [1,2,3,4] are adjacent
             [1,2,3] and [1,2] are adjacent
             [1,2,3] and [1,3] are NOT adjacent (removal + addition, not atomic)
-/
def ListAddRemove (l₁ l₂ : List α) : Prop :=
  (∃ (a : α) (l : List α), l₁ = a :: l ∧ l₂ = l) ∨
  (∃ (a : α) (l : List α), l₂ = a :: l ∧ l₁ = l)

/-- Two lists are adjacent via replace if they have the same length and differ in
    exactly one position. This is the standard adjacency for bounded DP.

    Example: [1,2,3] and [1,5,3] are adjacent
             [1,2,3] and [1,2,3,4] are NOT adjacent (different lengths)
-/
def ListReplace (l₁ l₂ : List α) : Prop :=
  l₁.length = l₂.length ∧
  ∃ i, i < l₁.length ∧ l₁[i]? ≠ l₂[i]? ∧
  (∀ j, j ≠ i → j < l₁.length → l₁[j]? = l₂[j]?)

/-- `ListAddRemove` is symmetric. -/
theorem listAddRemove_symm : ∀ (l₁ l₂ : List α), ListAddRemove l₁ l₂ → ListAddRemove l₂ l₁ := by
  intro l₁ l₂ h
  cases h with
  | inl h => right; exact h
  | inr h => left; exact h

/-- `ListReplace` is symmetric. -/
theorem listReplace_symm : ∀ (l₁ l₂ : List α), ListReplace l₁ l₂ → ListReplace l₂ l₁ := by
  sorry -- TODO: Fix existential destructuring syntax

/-- `ListReplace` preserves length. -/
theorem listReplace_length_eq : ∀ (l₁ l₂ : List α), ListReplace l₁ l₂ → l₁.length = l₂.length := by
  intro l₁ l₂ h
  exact h.1

/-- Two lists that are `ListAddRemove`-adjacent differ in length by at most 1. -/
theorem listAddRemove_length_diff : ∀ (l₁ l₂ : List α),
    ListAddRemove l₁ l₂ → l₁.length = l₂.length + 1 ∨ l₂.length = l₁.length + 1 := by
  intro l₁ l₂ h
  rcases h with ⟨a, l, rfl, rfl⟩ | ⟨a, l, rfl, rfl⟩
  · left; simp
  · right; simp

end ListAdjacency

end DPlean4
