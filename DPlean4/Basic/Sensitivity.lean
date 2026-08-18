/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Query Sensitivity for Differential Privacy

This file defines the sensitivity of queries with respect to an adjacency relation.

## Main Definitions

* `HasL1Sensitivity`: A query has L1 sensitivity at most Δ
* `HasL2Sensitivity`: A query has L2 sensitivity at most Δ

## Design Notes

Sensitivity is defined with respect to a generic adjacency relation `adj : D → D → Prop`.
This allows the same query to have different sensitivities under different adjacency notions.

For example, a counting query has:
- L1 sensitivity 1 under `ListAddRemove` adjacency
- L1 sensitivity 2 under `ListReplace` adjacency (replace could remove + add)
-/

namespace DPlean4

section Sensitivity

variable {D : Type*}  -- Database type

/-- A real-valued query `q : D → ℝ` has L1 sensitivity at most `Δ` with respect to
    adjacency relation `adj` if for all adjacent databases, the query outputs differ
    by at most `Δ` in absolute value. -/
def HasL1Sensitivity (adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → |q d₁ - q d₂| ≤ Δ

/-- A query with values in a normed space has L2 sensitivity at most `Δ` if the
    L2 norm of the difference is bounded by `Δ`. For real-valued queries, this
    coincides with L1 sensitivity. -/
def HasL2Sensitivity {E : Type*} [NormedAddCommGroup E] (adj : D → D → Prop)
    (q : D → E) (Δ : ℝ) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → ‖q d₁ - q d₂‖ ≤ Δ

/-- For real-valued queries, L1 and L2 sensitivity coincide. -/
theorem hasL1Sensitivity_iff_hasL2Sensitivity (adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ) :
    HasL1Sensitivity adj q Δ ↔ HasL2Sensitivity adj q Δ := by
  simp only [HasL1Sensitivity, HasL2Sensitivity, Real.norm_eq_abs]

/-- Sensitivity is monotone: if a query has sensitivity Δ₁ and Δ₁ ≤ Δ₂, then it
    has sensitivity Δ₂. -/
theorem hasL1Sensitivity_mono (adj : D → D → Prop) (q : D → ℝ) {Δ₁ Δ₂ : ℝ}
    (h : HasL1Sensitivity adj q Δ₁) (hle : Δ₁ ≤ Δ₂) : HasL1Sensitivity adj q Δ₂ := by
  intro d₁ d₂ hadj
  exact le_trans (h d₁ d₂ hadj) hle

/-- Constant queries have zero sensitivity. -/
theorem constant_hasL1Sensitivity_zero (adj : D → D → Prop) (c : ℝ) :
    HasL1Sensitivity adj (fun _ => c) 0 := by
  intro d₁ d₂ _
  simp [abs_zero]

/-- The sum of two queries has sensitivity at most the sum of their sensitivities. -/
theorem hasL1Sensitivity_add (adj : D → D → Prop) (q₁ q₂ : D → ℝ) (Δ₁ Δ₂ : ℝ)
    (h₁ : HasL1Sensitivity adj q₁ Δ₁) (h₂ : HasL1Sensitivity adj q₂ Δ₂) :
    HasL1Sensitivity adj (fun d => q₁ d + q₂ d) (Δ₁ + Δ₂) := by
  intro d₁ d₂ hadj
  have hq₁ := h₁ d₁ d₂ hadj
  have hq₂ := h₂ d₁ d₂ hadj
  calc |(q₁ d₁ + q₂ d₁) - (q₁ d₂ + q₂ d₂)|
      = |(q₁ d₁ - q₁ d₂) + (q₂ d₁ - q₂ d₂)| := by ring_nf
    _ ≤ |q₁ d₁ - q₁ d₂| + |q₂ d₁ - q₂ d₂| := abs_add_le _ _
    _ ≤ Δ₁ + Δ₂ := add_le_add hq₁ hq₂

/-- Scaling a query scales its sensitivity. -/
theorem hasL1Sensitivity_smul (adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ) (c : ℝ)
    (h : HasL1Sensitivity adj q Δ) : HasL1Sensitivity adj (fun d => c * q d) (|c| * Δ) := by
  intro d₁ d₂ hadj
  calc
    |c * q d₁ - c * q d₂|
      = |c * (q d₁ - q d₂)| := by ring_nf
    _ = |c| * |q d₁ - q d₂| := abs_mul c _
    _ ≤ |c| * Δ := mul_le_mul_of_nonneg_left (h d₁ d₂ hadj) (abs_nonneg c)

/-- A utility function `u : D → O → ℝ` has sensitivity at most `Δ` if changing
    the database changes the utility of any output by at most `Δ`.
    This is the sensitivity notion used by the Exponential mechanism. -/
def HasUtilitySensitivity {O : Type*} (adj : D → D → Prop) (u : D → O → ℝ) (Δ : ℝ) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → ∀ o, |u d₁ o - u d₂ o| ≤ Δ

end Sensitivity

end DPlean4
