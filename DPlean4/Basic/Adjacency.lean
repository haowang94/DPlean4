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

* `ListHeadAddRemove`: Head-only addition or removal
* `ListAddRemove`: Addition or removal at an arbitrary position (unbounded DP)
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

/-- Two lists are adjacent if one is obtained from the other by prepending a single
    element. This is a simplified head-only add/remove adjacency sufficient for
    proving DP of order-insensitive queries (e.g., counting, sum, histogram).

    Note: this captures head insertion/removal only, NOT arbitrary-position
    insertion. For queries that depend on element ordering, a more general
    adjacency relation (e.g., via `List.eraseIdx`) would be needed.

    Example: [1,2,3] and [2,3] are adjacent (prepend 1)
             [1,2,3] and [1,2,3,4] are NOT adjacent (4 appended, not prepended)
-/
def ListHeadAddRemove (l₁ l₂ : List α) : Prop :=
  (∃ (a : α) (l : List α), l₁ = a :: l ∧ l₂ = l) ∨
  (∃ (a : α) (l : List α), l₂ = a :: l ∧ l₁ = l)

/-- Standard unbounded-DP adjacency: one list is obtained from the other by
    inserting one element at an arbitrary position. The shared pre and
    suffix make the insertion position explicit. -/
def ListAddRemove (l₁ l₂ : List α) : Prop :=
  (∃ (pre suffix : List α) (a : α), l₁ = pre ++ (a :: suffix) ∧ l₂ = pre ++ suffix) ∨
  (∃ (pre suffix : List α) (a : α), l₂ = pre ++ (a :: suffix) ∧ l₁ = pre ++ suffix)

/-- Two lists are adjacent via replace if they have the same length and differ in
    exactly one position. This is the standard adjacency for bounded DP.

    Example: [1,2,3] and [1,5,3] are adjacent
             [1,2,3] and [1,2,3,4] are NOT adjacent (different lengths)
-/
def ListReplace (l₁ l₂ : List α) : Prop :=
  l₁.length = l₂.length ∧
  ∃ i, i < l₁.length ∧ l₁[i]? ≠ l₂[i]? ∧
  (∀ j, j ≠ i → j < l₁.length → l₁[j]? = l₂[j]?)

/-- `ListHeadAddRemove` is symmetric. -/
theorem listHeadAddRemove_symm : ∀ (l₁ l₂ : List α),
    ListHeadAddRemove l₁ l₂ → ListHeadAddRemove l₂ l₁ := by
  intro l₁ l₂ h
  exact h.elim Or.inr Or.inl

/-- `ListAddRemove` is symmetric. -/
theorem listAddRemove_symm : ∀ (l₁ l₂ : List α), ListAddRemove l₁ l₂ → ListAddRemove l₂ l₁ := by
  intro l₁ l₂ h
  cases h with
  | inl h => right; exact h
  | inr h => left; exact h

/-- `ListReplace` is symmetric. -/
theorem listReplace_symm : ∀ (l₁ l₂ : List α), ListReplace l₁ l₂ → ListReplace l₂ l₁ := by
  intro l₁ l₂ ⟨hlen, i, hi, hne, heq⟩
  exact ⟨hlen.symm, i, hlen ▸ hi, hne.symm, fun j hji hj => (heq j hji (hlen.symm ▸ hj)).symm⟩

/-- `ListReplace` preserves length. -/
theorem listReplace_length_eq : ∀ (l₁ l₂ : List α), ListReplace l₁ l₂ → l₁.length = l₂.length := by
  intro l₁ l₂ h
  exact h.1

/-- Two lists that are `ListAddRemove`-adjacent differ in length by at most 1. -/
theorem listAddRemove_length_diff : ∀ (l₁ l₂ : List α),
    ListAddRemove l₁ l₂ → l₁.length = l₂.length + 1 ∨ l₂.length = l₁.length + 1 := by
  intro l₁ l₂ h
  rcases h with ⟨pre, suffix, a, rfl, rfl⟩ | ⟨pre, suffix, a, rfl, rfl⟩
  · left; simp only [List.length_append, List.length_cons]; omega
  · right; simp only [List.length_append, List.length_cons]; omega

/-- Head insertion/removal is a special case of arbitrary-position adjacency. -/
theorem listAddRemove_of_head {l₁ l₂ : List α} :
    ListHeadAddRemove l₁ l₂ → ListAddRemove l₁ l₂ := by
  rintro (⟨a, l, h₁, h₂⟩ | ⟨a, l, h₂, h₁⟩)
  · exact Or.inl ⟨[], l, a, by simpa using h₁, by simpa using h₂⟩
  · exact Or.inr ⟨[], l, a, by simpa using h₂, by simpa using h₁⟩

end ListAdjacency

end DPlean4
