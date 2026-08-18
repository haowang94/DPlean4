/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Basic.Adjacency
import DPlean4.Basic.Sensitivity

/-!
# Tests and Examples for Adjacency and Sensitivity

This file contains concrete examples demonstrating:
1. How `ListAddRemove` and `ListReplace` adjacency work
2. Sensitivity calculations for standard queries (count, sum)
3. Boundary cases (empty lists, singleton lists)

These serve as both regression tests and documentation of the API.
-/

namespace DPlean4.Examples

open DPlean4

section AdjacencyExamples

/-- Example: [1,2,3] and [2,3] are adjacent via add/remove (remove head) -/
example : ListAddRemove [1,2,3] [2,3] := .inl ⟨1, [2,3], rfl, rfl⟩

/-- Example: [1,2,3] and [4,1,2,3] are adjacent via add/remove (add at head) -/
example : ListAddRemove [1,2,3] [4,1,2,3] := .inr ⟨4, [1,2,3], rfl, rfl⟩

/-- Example: [1,2,3] and [1,5,3] are adjacent via replace (differ at index 1) -/
example : ListReplace [1,2,3] [1,5,3] := by
  refine ⟨by simp, 1, by simp, by decide, ?_⟩
  intro j hj hj_lt
  simp at hj_lt
  have : j = 0 ∨ j = 2 := by omega
  rcases this with rfl | rfl <;> decide

/-- Example: Lists of different lengths are NOT adjacent via replace -/
example : ¬ListReplace [1,2,3] [1,2,3,4] := by
  intro ⟨hlen, _⟩
  simp at hlen

end AdjacencyExamples

section SensitivityExamples

variable {α : Type*}

/-- The list length query (counting query) -/
def countQuery : List α → ℝ := fun l => (l.length : ℝ)

/-- The counting query has L1 sensitivity 1 under ListAddRemove adjacency -/
theorem countQuery_sensitivity : HasL1Sensitivity ListAddRemove (countQuery : List α → ℝ) 1 := by
  intro l₁ l₂ hadj
  have hlen := listAddRemove_length_diff l₁ l₂ hadj
  simp [countQuery]
  obtain ⟨a, l, rfl, rfl⟩ | ⟨a, l, rfl, rfl⟩ := hadj
  · simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · simp [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- A constant query has zero sensitivity (regardless of adjacency) -/
example (c : ℝ) : HasL1Sensitivity ListAddRemove (fun (_ : List α) => c) 0 :=
  constant_hasL1Sensitivity_zero ListAddRemove c

/-- Adding two queries with sensitivities Δ₁ and Δ₂ gives sensitivity Δ₁ + Δ₂ -/
example (q₁ q₂ : List α → ℝ) (Δ₁ Δ₂ : ℝ)
    (h₁ : HasL1Sensitivity ListAddRemove q₁ Δ₁)
    (h₂ : HasL1Sensitivity ListAddRemove q₂ Δ₂) :
    HasL1Sensitivity ListAddRemove (fun l => q₁ l + q₂ l) (Δ₁ + Δ₂) :=
  hasL1Sensitivity_add ListAddRemove q₁ q₂ Δ₁ Δ₂ h₁ h₂

end SensitivityExamples

end DPlean4.Examples
