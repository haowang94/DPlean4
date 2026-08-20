/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

open scoped NNReal

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
- L1 sensitivity 1 under `ListHeadAddRemove` adjacency
- L1 sensitivity 2 under `ListReplace` adjacency (replace could remove + add)
-/

namespace DPlean4

section Sensitivity

variable {D : Type*}  -- Database type

/-- A real-valued query `q : D → ℝ` has L1 sensitivity at most `Δ` with respect to
    adjacency relation `adj` if for all adjacent databases, the query outputs differ
    by at most `Δ` in absolute value. -/
def HasL1Sensitivity (adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ≥0) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → |q d₁ - q d₂| ≤ ↑Δ

/-- A query with values in a normed space has L2 sensitivity at most `Δ` if the
    L2 norm of the difference is bounded by `Δ`. For real-valued queries, this
    coincides with L1 sensitivity. -/
def HasL2Sensitivity {E : Type*} [NormedAddCommGroup E] (adj : D → D → Prop)
    (q : D → E) (Δ : ℝ≥0) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → ‖q d₁ - q d₂‖ ≤ ↑Δ

/-- For real-valued queries, L1 and L2 sensitivity coincide. -/
theorem hasL1Sensitivity_iff_hasL2Sensitivity (adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ≥0) :
    HasL1Sensitivity adj q Δ ↔ HasL2Sensitivity adj q Δ := by
  simp only [HasL1Sensitivity, HasL2Sensitivity, Real.norm_eq_abs]

/-- Convert L1 sensitivity to L2 sensitivity for real-valued queries.
    Useful when feeding a scalar query into the Gaussian mechanism (which requires L2). -/
theorem HasL1Sensitivity.toL2 {adj : D → D → Prop} {q : D → ℝ} {Δ : ℝ≥0}
    (h : HasL1Sensitivity adj q Δ) : HasL2Sensitivity adj q Δ :=
  (hasL1Sensitivity_iff_hasL2Sensitivity adj q Δ).mp h

/-- Sensitivity is monotone: if a query has sensitivity Δ₁ and Δ₁ ≤ Δ₂, then it
    has sensitivity Δ₂. -/
theorem hasL1Sensitivity_mono (adj : D → D → Prop) (q : D → ℝ) {Δ₁ Δ₂ : ℝ≥0}
    (h : HasL1Sensitivity adj q Δ₁) (hle : Δ₁ ≤ Δ₂) : HasL1Sensitivity adj q Δ₂ := by
  intro d₁ d₂ hadj
  exact le_trans (h d₁ d₂ hadj) (by exact_mod_cast hle)

/-- Constant queries have zero sensitivity. -/
theorem constant_hasL1Sensitivity_zero (adj : D → D → Prop) (c : ℝ) :
    HasL1Sensitivity adj (fun _ => c) 0 := by
  intro d₁ d₂ _
  simp [abs_zero]

/-- The sum of two queries has sensitivity at most the sum of their sensitivities. -/
theorem hasL1Sensitivity_add (adj : D → D → Prop) (q₁ q₂ : D → ℝ) (Δ₁ Δ₂ : ℝ≥0)
    (h₁ : HasL1Sensitivity adj q₁ Δ₁) (h₂ : HasL1Sensitivity adj q₂ Δ₂) :
    HasL1Sensitivity adj (fun d => q₁ d + q₂ d) (Δ₁ + Δ₂) := by
  intro d₁ d₂ hadj
  have hq₁ := h₁ d₁ d₂ hadj
  have hq₂ := h₂ d₁ d₂ hadj
  change |(q₁ d₁ + q₂ d₁) - (q₁ d₂ + q₂ d₂)| ≤ ↑(Δ₁ + Δ₂)
  push_cast
  calc |(q₁ d₁ + q₂ d₁) - (q₁ d₂ + q₂ d₂)|
      = |(q₁ d₁ - q₁ d₂) + (q₂ d₁ - q₂ d₂)| := by ring_nf
    _ ≤ |q₁ d₁ - q₁ d₂| + |q₂ d₁ - q₂ d₂| := abs_add_le _ _
    _ ≤ ↑Δ₁ + ↑Δ₂ := add_le_add hq₁ hq₂

/-- Scaling a query scales its sensitivity. -/
theorem hasL1Sensitivity_smul (adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ≥0) (c : ℝ)
    (h : HasL1Sensitivity adj q Δ) : HasL1Sensitivity adj (fun d => c * q d) (‖c‖₊ * Δ) := by
  intro d₁ d₂ hadj
  change |c * q d₁ - c * q d₂| ≤ ↑(‖c‖₊ * Δ)
  push_cast [NNReal.coe_mul, coe_nnnorm]
  rw [Real.norm_eq_abs]
  calc
    |c * q d₁ - c * q d₂|
      = |c * (q d₁ - q d₂)| := by ring_nf
    _ = |c| * |q d₁ - q d₂| := abs_mul c _
    _ ≤ |c| * ↑Δ := mul_le_mul_of_nonneg_left (h d₁ d₂ hadj) (abs_nonneg c)

/-- Negating a query preserves its sensitivity. -/
theorem hasL1Sensitivity_neg (adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ≥0)
    (h : HasL1Sensitivity adj q Δ) : HasL1Sensitivity adj (fun d => -q d) Δ := by
  intro d₁ d₂ hadj
  simp only [neg_sub_neg]
  rw [abs_sub_comm]
  exact h d₁ d₂ hadj

/-- Subtraction of queries: sensitivity is the sum of individual sensitivities. -/
theorem hasL1Sensitivity_sub (adj : D → D → Prop) (q₁ q₂ : D → ℝ) (Δ₁ Δ₂ : ℝ≥0)
    (h₁ : HasL1Sensitivity adj q₁ Δ₁) (h₂ : HasL1Sensitivity adj q₂ Δ₂) :
    HasL1Sensitivity adj (fun d => q₁ d - q₂ d) (Δ₁ + Δ₂) := by
  intro d₁ d₂ hadj
  have hq₁ := h₁ d₁ d₂ hadj
  have hq₂ := h₂ d₁ d₂ hadj
  change |q₁ d₁ - q₂ d₁ - (q₁ d₂ - q₂ d₂)| ≤ ↑(Δ₁ + Δ₂)
  push_cast
  rw [abs_le]
  constructor <;> linarith [abs_le.mp hq₁, abs_le.mp hq₂]

/-- Lipschitz postprocessing of a query: if `f` is L-Lipschitz and `q` has sensitivity Δ,
    then `f ∘ q` has sensitivity `L * Δ`. -/
theorem hasL1Sensitivity_lipschitz (adj : D → D → Prop) (q : D → ℝ) (f : ℝ → ℝ) (Δ L : ℝ≥0)
    (hq : HasL1Sensitivity adj q Δ)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ ↑L * |x - y|) :
    HasL1Sensitivity adj (fun d => f (q d)) (L * Δ) := by
  intro d₁ d₂ hadj
  change |f (q d₁) - f (q d₂)| ≤ ↑(L * Δ)
  push_cast
  calc |f (q d₁) - f (q d₂)| ≤ ↑L * |q d₁ - q d₂| := hf _ _
    _ ≤ ↑L * ↑Δ := mul_le_mul_of_nonneg_left (hq d₁ d₂ hadj) (NNReal.coe_nonneg L)

/-- Max of two queries has sensitivity at most the max of their sensitivities. -/
theorem hasL1Sensitivity_max (adj : D → D → Prop) (q₁ q₂ : D → ℝ) (Δ₁ Δ₂ : ℝ≥0)
    (h₁ : HasL1Sensitivity adj q₁ Δ₁) (h₂ : HasL1Sensitivity adj q₂ Δ₂) :
    HasL1Sensitivity adj (fun d => max (q₁ d) (q₂ d)) (max Δ₁ Δ₂) := by
  intro d₁ d₂ hadj
  have hq₁ := h₁ d₁ d₂ hadj
  have hq₂ := h₂ d₁ d₂ hadj
  have hle₁ : (↑Δ₁ : ℝ) ≤ ↑(max Δ₁ Δ₂) := by exact_mod_cast le_max_left Δ₁ Δ₂
  have hle₂ : (↑Δ₂ : ℝ) ≤ ↑(max Δ₁ Δ₂) := by exact_mod_cast le_max_right Δ₁ Δ₂
  simp only [max_def]
  split_ifs <;> rw [abs_le] <;> constructor <;>
    linarith [abs_le.mp hq₁, abs_le.mp hq₂]

/-- Min of two queries has sensitivity at most the max of their sensitivities. -/
theorem hasL1Sensitivity_min (adj : D → D → Prop) (q₁ q₂ : D → ℝ) (Δ₁ Δ₂ : ℝ≥0)
    (h₁ : HasL1Sensitivity adj q₁ Δ₁) (h₂ : HasL1Sensitivity adj q₂ Δ₂) :
    HasL1Sensitivity adj (fun d => min (q₁ d) (q₂ d)) (max Δ₁ Δ₂) := by
  intro d₁ d₂ hadj
  have hq₁ := h₁ d₁ d₂ hadj
  have hq₂ := h₂ d₁ d₂ hadj
  have hle₁ : (↑Δ₁ : ℝ) ≤ ↑(max Δ₁ Δ₂) := by exact_mod_cast le_max_left Δ₁ Δ₂
  have hle₂ : (↑Δ₂ : ℝ) ≤ ↑(max Δ₁ Δ₂) := by exact_mod_cast le_max_right Δ₁ Δ₂
  simp only [min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;>
    linarith [abs_le.mp hq₁, abs_le.mp hq₂]

/-- A utility function `u : D → O → ℝ` has sensitivity at most `Δ` if changing
    the database changes the utility of any output by at most `Δ`.
    This is the sensitivity notion used by the Exponential mechanism. -/
def HasUtilitySensitivity {O : Type*} (adj : D → D → Prop) (u : D → O → ℝ) (Δ : ℝ≥0) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → ∀ o, |u d₁ o - u d₂ o| ≤ ↑Δ

-- ============================================================================
-- Vector Sensitivity
-- ============================================================================

/-- A vector-valued query has L1 vector sensitivity at most `Δ` if the sum of
    absolute coordinate differences is bounded. This is the sensitivity notion
    for the vector Laplace mechanism. -/
def HasL1VectorSensitivity {ι : Type*} [Fintype ι] (adj : D → D → Prop)
    (q : D → ι → ℝ) (Δ : ℝ≥0) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → ∑ i, |q d₁ i - q d₂ i| ≤ ↑Δ

/-- A vector-valued query has L2 vector sensitivity at most `Δ` if the sum of
    squared coordinate differences is bounded by `Δ²`. This is the sensitivity
    notion for the vector Gaussian mechanism.
    Equivalent to `HasL2Sensitivity` on `EuclideanSpace ℝ ι`. -/
def HasL2VectorSensitivity {ι : Type*} [Fintype ι] (adj : D → D → Prop)
    (q : D → ι → ℝ) (Δ : ℝ≥0) : Prop :=
  ∀ d₁ d₂, adj d₁ d₂ → ∑ i, (q d₁ i - q d₂ i) ^ 2 ≤ (↑Δ : ℝ) ^ 2

theorem HasL1VectorSensitivity.mono {ι : Type*} [Fintype ι] {adj : D → D → Prop}
    {q : D → ι → ℝ} {Δ₁ Δ₂ : ℝ≥0} (h : HasL1VectorSensitivity adj q Δ₁) (hle : Δ₁ ≤ Δ₂) :
    HasL1VectorSensitivity adj q Δ₂ :=
  fun d₁ d₂ hadj => le_trans (h d₁ d₂ hadj) (by exact_mod_cast hle)

theorem HasL2VectorSensitivity.mono {ι : Type*} [Fintype ι] {adj : D → D → Prop}
    {q : D → ι → ℝ} {Δ₁ Δ₂ : ℝ≥0} (h : HasL2VectorSensitivity adj q Δ₁)
    (hle : Δ₁ ≤ Δ₂) :
    HasL2VectorSensitivity adj q Δ₂ :=
  fun d₁ d₂ hadj => le_trans (h d₁ d₂ hadj)
    (pow_le_pow_left₀ (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hle) 2)

/-- L1 vector sensitivity implies L2 vector sensitivity:
    ‖x‖₂² = ∑ᵢ xᵢ² ≤ (∑ᵢ |xᵢ|)² ≤ Δ². -/
theorem HasL1VectorSensitivity.toL2 {ι : Type*} [Fintype ι] {adj : D → D → Prop}
    {q : D → ι → ℝ} {Δ : ℝ≥0} (h : HasL1VectorSensitivity adj q Δ) :
    HasL2VectorSensitivity adj q Δ := by
  intro d₁ d₂ hadj
  have h1 := h d₁ d₂ hadj
  calc ∑ i : ι, (q d₁ i - q d₂ i) ^ 2
      = ∑ i : ι, |q d₁ i - q d₂ i| ^ 2 := by
        congr 1; ext i; rw [sq_abs]
    _ ≤ (∑ i : ι, |q d₁ i - q d₂ i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ (↑Δ : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => abs_nonneg _)) h1 2

end Sensitivity

end DPlean4
