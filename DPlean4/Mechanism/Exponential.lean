/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Pure
import DPlean4.Basic.Sensitivity
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Exponential Mechanism

The Exponential mechanism (McSherry & Talwar, 2007) is the fundamental DP mechanism
for discrete/finite output spaces. Given a utility function `u : D → O → ℝ` with
sensitivity `Δ`, it samples output `o` with probability proportional to
`exp(ε · u(d,o) / (2Δ))`.

## Main Results

* `expMech_isPureDP`: The exponential mechanism satisfies ε-DP.

## Proof Strategy

For databases d₁ ~ d₂ and any output o, the PMF ratio satisfies:

  p(o|d₁) / p(o|d₂) = [f₁(o)/Z₁] / [f₂(o)/Z₂]

where f_d(o) = exp(ε·u(d,o)/(2Δ)) and Z_d = Σ_o f_d(o).

Two key bounds (from sensitivity |u(d₁,o)-u(d₂,o)| ≤ Δ):
1. f₁(o) ≤ exp(ε/2) · f₂(o)    (pointwise weight bound)
2. Z₂ ≤ exp(ε/2) · Z₁          (partition function bound)

Combined: p(o|d₁) ≤ exp(ε) · p(o|d₂), giving ε-DP.
-/

noncomputable section

namespace DPlean4

open MeasureTheory ENNReal Real Finset PMF

open scoped NNReal ENNReal

variable {D O : Type*}

-- ============================================================================
-- Exponential Mechanism Weights
-- ============================================================================

/-- Unnormalized weight for the exponential mechanism. -/
def expWeight (u : D → O → ℝ) (ε Δ : ℝ) (d : D) (o : O) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ε * u d o / (2 * Δ)))

theorem expWeight_pos (u : D → O → ℝ) (ε Δ : ℝ) (d : D) (o : O) :
    0 < expWeight u ε Δ d o :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem expWeight_ne_top (u : D → O → ℝ) (ε Δ : ℝ) (d : D) (o : O) :
    expWeight u ε Δ d o ≠ ⊤ :=
  ENNReal.ofReal_ne_top

section Fintype

variable [Fintype O] [Nonempty O]

theorem tsum_expWeight_ne_zero (u : D → O → ℝ) (ε Δ : ℝ) (d : D) :
    ∑' o, expWeight u ε Δ d o ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (expWeight_pos u ε Δ d (Classical.arbitrary O))
    (ENNReal.le_tsum _))

theorem tsum_expWeight_ne_top (u : D → O → ℝ) (ε Δ : ℝ) (d : D) :
    ∑' o, expWeight u ε Δ d o ≠ ⊤ := by
  rw [tsum_fintype]
  exact (sum_lt_top.mpr fun o _ =>
    lt_top_iff_ne_top.mpr (expWeight_ne_top u ε Δ d o)).ne

/-- Key exponent inequality: ε·u(d₁,o)/(2Δ) ≤ ε/2 + ε·u(d₂,o)/(2Δ)
    when u(d₁,o) - u(d₂,o) ≤ Δ and ε ≥ 0 and Δ > 0. -/
private theorem exp_exponent_le {ε Δ : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    {a b : ℝ} (hab : a - b ≤ Δ) :
    ε * a / (2 * Δ) ≤ ε / 2 + ε * b / (2 * Δ) := by
  have h2Δ_pos : (0 : ℝ) < 2 * Δ := by linarith
  suffices h : ε * a ≤ ε * Δ + ε * b by
    calc ε * a / (2 * Δ)
        ≤ (ε * Δ + ε * b) / (2 * Δ) := div_le_div_of_nonneg_right h h2Δ_pos.le
      _ = ε * Δ / (2 * Δ) + ε * b / (2 * Δ) := add_div _ _ _
      _ = ε / 2 + ε * b / (2 * Δ) := by congr 1; field_simp
  nlinarith

/-- Sensitivity gives a pointwise weight bound: changing the database scales
    each weight by at most `exp(ε/2)`. -/
theorem expWeight_le {u : D → O → ℝ} {ε Δ : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    {adj : D → D → Prop} (hsens : HasUtilitySensitivity adj u Δ)
    {d₁ d₂ : D} (hadj : adj d₁ d₂) (o : O) :
    expWeight u ε Δ d₁ o ≤ ENNReal.ofReal (Real.exp (ε / 2)) * expWeight u ε Δ d₂ o := by
  simp only [expWeight]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (exp_exponent_le hΔ hε ((abs_le.mp (hsens d₁ d₂ hadj o)).2)))

/-- Reverse weight bound for the partition function sum. -/
theorem expWeight_le_reverse {u : D → O → ℝ} {ε Δ : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    {adj : D → D → Prop} (hsens : HasUtilitySensitivity adj u Δ)
    {d₁ d₂ : D} (hadj : adj d₁ d₂) (o : O) :
    expWeight u ε Δ d₂ o ≤ ENNReal.ofReal (Real.exp (ε / 2)) * expWeight u ε Δ d₁ o := by
  simp only [expWeight]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (exp_exponent_le hΔ hε (by linarith [(abs_le.mp (hsens d₁ d₂ hadj o)).1])))

/-- Partition function bound: Z(d₂) ≤ exp(ε/2) · Z(d₁). -/
theorem tsum_expWeight_le {u : D → O → ℝ} {ε Δ : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    {adj : D → D → Prop} (hsens : HasUtilitySensitivity adj u Δ)
    {d₁ d₂ : D} (hadj : adj d₁ d₂) :
    ∑' o, expWeight u ε Δ d₂ o ≤
    ENNReal.ofReal (Real.exp (ε / 2)) * ∑' o, expWeight u ε Δ d₁ o := by
  calc ∑' o, expWeight u ε Δ d₂ o
      ≤ ∑' o, ENNReal.ofReal (Real.exp (ε / 2)) * expWeight u ε Δ d₁ o :=
        ENNReal.tsum_le_tsum (fun o => expWeight_le_reverse hΔ hε hsens hadj o)
    _ = ENNReal.ofReal (Real.exp (ε / 2)) * ∑' o, expWeight u ε Δ d₁ o :=
        ENNReal.tsum_mul_left

-- ============================================================================
-- Exponential Mechanism Definition
-- ============================================================================

variable [MeasurableSpace O] [MeasurableSingletonClass O]

/-- The exponential mechanism PMF: samples o with probability proportional to
    `exp(ε · u(d,o) / (2Δ))`. -/
def expMechPMF (u : D → O → ℝ) (ε Δ : ℝ) (d : D) : PMF O :=
  PMF.normalize (expWeight u ε Δ d)
    (tsum_expWeight_ne_zero u ε Δ d)
    (tsum_expWeight_ne_top u ε Δ d)

/-- The exponential mechanism as a `Mechanism D O`. -/
def expMech (u : D → O → ℝ) (ε Δ : ℝ) : Mechanism D O :=
  fun d => ⟨(expMechPMF u ε Δ d).toMeasure, inferInstance⟩

omit [MeasurableSingletonClass O] in
@[simp]
theorem expMech_toMeasure (u : D → O → ℝ) (ε Δ : ℝ) (d : D) :
    (expMech u ε Δ d).toMeasure = (expMechPMF u ε Δ d).toMeasure :=
  rfl

-- ============================================================================
-- Exponential Mechanism is Pure DP
-- ============================================================================

/-- Pointwise PMF bound: for any output o, p(o|d₁) ≤ exp(ε) · p(o|d₂).
    Follows from weight bound (f₁(o) ≤ e·f₂(o)) and partition function
    bound (Z₂ ≤ e·Z₁) combined via cross-multiplication. -/
theorem expMechPMF_le {u : D → O → ℝ} {ε Δ : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    {adj : D → D → Prop} (hsens : HasUtilitySensitivity adj u Δ)
    {d₁ d₂ : D} (hadj : adj d₁ d₂) (o : O) :
    expMechPMF u ε Δ d₁ o ≤ ENNReal.ofReal (Real.exp ε) * expMechPMF u ε Δ d₂ o := by
  simp only [expMechPMF, PMF.normalize_apply]
  set f₁ := expWeight u ε Δ d₁
  set f₂ := expWeight u ε Δ d₂
  set Z₁ := ∑' o, f₁ o
  set Z₂ := ∑' o, f₂ o
  set e := ENNReal.ofReal (Real.exp (ε / 2))
  have hexp : ENNReal.ofReal (Real.exp ε) = e * e := by
    simp only [e, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring
  rw [hexp]
  have hZ₁_ne : Z₁ ≠ 0 := tsum_expWeight_ne_zero u ε Δ d₁
  have hZ₁_fin : Z₁ ≠ ⊤ := tsum_expWeight_ne_top u ε Δ d₁
  have hZ₂_ne : Z₂ ≠ 0 := tsum_expWeight_ne_zero u ε Δ d₂
  have hZ₂_fin : Z₂ ≠ ⊤ := tsum_expWeight_ne_top u ε Δ d₂
  have hweight := expWeight_le hΔ hε hsens hadj o
  have hpart := tsum_expWeight_le hΔ hε hsens hadj
  have he_ne : e ≠ 0 := ENNReal.ofReal_pos.mpr (Real.exp_pos _) |>.ne'
  have he_fin : e ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Key subgoal: Z₁⁻¹ ≤ e * Z₂⁻¹
  have hinv : Z₁⁻¹ ≤ e * Z₂⁻¹ := by
    rw [show e * Z₂⁻¹ = e / Z₂ from rfl]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hZ₂_ne) (Or.inl hZ₂_fin)]
    calc Z₁⁻¹ * Z₂
        ≤ Z₁⁻¹ * (e * Z₁) := by gcongr
      _ = e * (Z₁⁻¹ * Z₁) := by rw [← mul_assoc, mul_comm Z₁⁻¹ e, mul_assoc]
      _ = e := by rw [ENNReal.inv_mul_cancel hZ₁_ne hZ₁_fin, mul_one]
  calc f₁ o * Z₁⁻¹
      ≤ (e * f₂ o) * Z₁⁻¹ := by gcongr
    _ ≤ (e * f₂ o) * (e * Z₂⁻¹) := by gcongr
    _ = (e * e) * (f₂ o * Z₂⁻¹) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]

/-- **The Exponential Mechanism satisfies ε-DP.**

    Given utility function u with sensitivity Δ > 0,
    the mechanism sampling proportional to exp(ε·u(d,o)/(2Δ))
    satisfies ε-DP. (McSherry & Talwar, 2007) -/
theorem expMech_isPureDP {adj : D → D → Prop} {u : D → O → ℝ} {Δ : ℝ}
    (hΔ : 0 < Δ) {ε : NNReal}
    (hsens : HasUtilitySensitivity adj u Δ) :
    IsPureDP adj (expMech u ε Δ) ε := by
  intro d₁ d₂ hadj s hs
  simp only [expMech_toMeasure, ENNReal.coe_zero, add_zero]
  rw [PMF.toMeasure_apply_eq_tsum, PMF.toMeasure_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  simp only [Set.indicator]
  split_ifs
  · exact expMechPMF_le hΔ (by positivity) hsens hadj x
  · exact bot_le

-- ============================================================================
-- Examples
-- ============================================================================

section Examples

variable {α : Type*} [DecidableEq α]

/-- Private argmax over Bool: select True/False privately based on utility. -/
example (adj : List α → List α → Prop)
    (u : List α → Bool → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hsens : HasUtilitySensitivity adj u Δ) (ε : NNReal) :
    IsPureDP adj (expMech u (ε : ℝ) Δ) ε :=
  expMech_isPureDP hΔ hsens

end Examples

end Fintype

end DPlean4

end -- noncomputable section
