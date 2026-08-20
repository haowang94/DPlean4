/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Pure
import DPlean4.Privacy.RenyiDP
import DPlean4.Privacy.TightZCDP
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
def expWeight (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) (o : O) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ε * u d o / (2 * ↑Δ)))

theorem expWeight_pos (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) (o : O) :
    0 < expWeight u ε Δ d o :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem expWeight_ne_top (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) (o : O) :
    expWeight u ε Δ d o ≠ ⊤ :=
  ENNReal.ofReal_ne_top

section Fintype

variable [Fintype O] [Nonempty O]

omit [Fintype O] in
theorem tsum_expWeight_ne_zero (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) :
    ∑' o, expWeight u ε Δ d o ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (expWeight_pos u ε Δ d (Classical.arbitrary O))
    (ENNReal.le_tsum _))

omit [Fintype O] [Nonempty O] in
theorem tsum_expWeight_ne_top [Finite O] (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) :
    ∑' o, expWeight u ε Δ d o ≠ ⊤ := by
  cases nonempty_fintype O
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

omit [Fintype O] [Nonempty O] in
/-- Sensitivity gives a pointwise weight bound: changing the database scales
    each weight by at most `exp(ε/2)`. -/
theorem expWeight_le {u : D → O → ℝ} {ε : ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0) (hε : 0 ≤ ε)
    {adj : D → D → Prop} (hsens : HasUtilitySensitivity adj u Δ)
    {d₁ d₂ : D} (hadj : adj d₁ d₂) (o : O) :
    expWeight u ε Δ d₁ o ≤ ENNReal.ofReal (Real.exp (ε / 2)) * expWeight u ε Δ d₂ o := by
  have hΔ_pos : (0 : ℝ) < ↑Δ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hΔ)
  simp only [expWeight]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (exp_exponent_le hΔ_pos hε ((abs_le.mp (hsens d₁ d₂ hadj o)).2)))

omit [Fintype O] [Nonempty O] in
/-- Reverse weight bound for the partition function sum. -/
theorem expWeight_le_reverse {u : D → O → ℝ} {ε : ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0) (hε : 0 ≤ ε)
    {adj : D → D → Prop} (hsens : HasUtilitySensitivity adj u Δ)
    {d₁ d₂ : D} (hadj : adj d₁ d₂) (o : O) :
    expWeight u ε Δ d₂ o ≤ ENNReal.ofReal (Real.exp (ε / 2)) * expWeight u ε Δ d₁ o := by
  have hΔ_pos : (0 : ℝ) < ↑Δ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hΔ)
  simp only [expWeight]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (exp_exponent_le hΔ_pos hε (by linarith [(abs_le.mp (hsens d₁ d₂ hadj o)).1])))

omit [Fintype O] [Nonempty O] in
/-- Partition function bound: Z(d₂) ≤ exp(ε/2) · Z(d₁). -/
theorem tsum_expWeight_le {u : D → O → ℝ} {ε : ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0) (hε : 0 ≤ ε)
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
def expMechPMF (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) : PMF O :=
  PMF.normalize (expWeight u ε Δ d)
    (tsum_expWeight_ne_zero u ε Δ d)
    (tsum_expWeight_ne_top u ε Δ d)

/-- The exponential mechanism as a `Mechanism D O`. -/
def expMech (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) : Mechanism D O :=
  fun d => ⟨(expMechPMF u ε Δ d).toMeasure, inferInstance⟩

omit [MeasurableSingletonClass O] in
@[simp]
theorem expMech_toMeasure (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) :
    (expMech u ε Δ d).toMeasure = (expMechPMF u ε Δ d).toMeasure :=
  rfl

-- ============================================================================
-- Exponential Mechanism is Pure DP
-- ============================================================================

omit [MeasurableSpace O] [MeasurableSingletonClass O] in
/-- Pointwise PMF bound: for any output o, p(o|d₁) ≤ exp(ε) · p(o|d₂).
    Follows from weight bound (f₁(o) ≤ e·f₂(o)) and partition function
    bound (Z₂ ≤ e·Z₁) combined via cross-multiplication. -/
theorem expMechPMF_le {u : D → O → ℝ} {ε : ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0) (hε : 0 ≤ ε)
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
    simp only [e, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring_nf
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
theorem expMech_isPureDP {adj : D → D → Prop} {u : D → O → ℝ} {Δ : ℝ≥0}
    (hΔ : Δ ≠ 0) {ε : NNReal}
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
-- Exponential Mechanism → zCDP (via full support)
-- ============================================================================

omit [MeasurableSpace O] [MeasurableSingletonClass O] in
/-- The exponential mechanism PMF assigns positive probability to every outcome.
    This is because the unnormalized weights are positive (exp is always positive). -/
theorem expMechPMF_pos (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d : D) (o : O) :
    0 < expMechPMF u ε Δ d o := by
  simp only [expMechPMF, PMF.normalize_apply]
  exact ENNReal.div_pos (expWeight_pos u ε Δ d o).ne' (tsum_expWeight_ne_top u ε Δ d)

/-- The exponential mechanism has mutually absolutely continuous output
    distributions for any two databases. -/
theorem expMech_absolutelyContinuous (u : D → O → ℝ) (ε : ℝ) (Δ : ℝ≥0) (d₁ d₂ : D) :
    (expMech u ε Δ d₁).toMeasure ≪ (expMech u ε Δ d₂).toMeasure := by
  intro s hs
  simp only [expMech_toMeasure] at hs ⊢
  rw [PMF.toMeasure_apply_eq_tsum] at hs ⊢
  rw [ENNReal.tsum_eq_zero] at hs ⊢
  intro x
  by_cases hx : x ∈ s
  · exfalso
    have h := hs x
    simp only [Set.indicator_of_mem hx] at h
    exact (expMechPMF_pos u ε Δ d₂ x).ne' h
  · exact Set.indicator_of_notMem hx _

/-- The Rényi moment of the exponential mechanism is finite on a finite type. -/
theorem expMech_renyiMoment_ne_top (u : D → O → ℝ) {ε : NNReal} (Δ : ℝ≥0) (hΔ : Δ ≠ 0)
    {adj : D → D → Prop} (hsens : HasUtilitySensitivity adj u Δ)
    {d₁ d₂ : D} (hadj : adj d₁ d₂)
    {α : ℝ} (hα : 1 < α) :
    renyiMoment α (expMech u ε Δ d₁).toMeasure (expMech u ε Δ d₂).toMeasure ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (renyiMoment_le_of_pureMeasureClose' (expMech_isPureDP hΔ hsens d₁ d₂ hadj) hα
      (expMech_absolutelyContinuous u ε Δ d₁ d₂))

/-- **The Exponential Mechanism satisfies ε-zCDP** on finite output types.

    This follows from:
    1. ε-pure DP (from `expMech_isPureDP`)
    2. Absolute continuity (from full support — every outcome has positive probability)
    3. Rényi moment finiteness (from the pure DP bound + absolute continuity)

    Combined via `isZCDP_of_isPureDP`.

    Note: the conversion gives ε-zCDP from ε-DP. The tight bound is
    (ε²/2)-zCDP; see `expMech_isZCDP_tight` below. -/
theorem expMech_isZCDP {adj : D → D → Prop} {u : D → O → ℝ} {Δ : ℝ≥0}
    (hΔ : Δ ≠ 0) {ε : NNReal}
    (hsens : HasUtilitySensitivity adj u Δ) :
    IsZCDP adj (expMech u ε Δ) ε :=
  isZCDP_of_isPureDP (expMech_isPureDP hΔ hsens)
    (fun _d₁ _d₂ _ => expMech_absolutelyContinuous u ε Δ _d₁ _d₂)
    (fun _ _ hadj _ hα => expMech_renyiMoment_ne_top u Δ hΔ hsens hadj hα)

/-- **The Exponential Mechanism satisfies (ε²/2)-zCDP** (tight bound).

    This improves `expMech_isZCDP` by using the tight pure-DP to zCDP conversion.
    Requires symmetric adjacency (adj d₁ d₂ → adj d₂ d₁).

    For ε = 0.1, this gives 0.005-zCDP instead of 0.1-zCDP (20× tighter). -/
theorem expMech_isZCDP_tight {adj : D → D → Prop} {u : D → O → ℝ} {Δ : ℝ≥0}
    (hΔ : Δ ≠ 0) {ε : NNReal}
    (hsens : HasUtilitySensitivity adj u Δ)
    (h_symm : ∀ d₁ d₂, adj d₁ d₂ → adj d₂ d₁) :
    IsZCDP adj (expMech u ε Δ) (ε ^ 2 / 2) :=
  isZCDP_tight_of_isPureDP h_symm (expMech_isPureDP hΔ hsens)
    (fun _d₁ _d₂ _ => expMech_absolutelyContinuous u ε Δ _d₁ _d₂)
    (fun _ _ hadj _ hα => expMech_renyiMoment_ne_top u Δ hΔ hsens hadj hα)

-- ============================================================================
-- Examples
-- ============================================================================

section Examples

variable {α : Type*} [DecidableEq α]

/-- Private argmax over Bool: select True/False privately based on utility. -/
example (adj : List α → List α → Prop)
    (u : List α → Bool → ℝ) (Δ : ℝ≥0) (hΔ : Δ ≠ 0)
    (hsens : HasUtilitySensitivity adj u Δ) (ε : NNReal) :
    IsPureDP adj (expMech u (ε : ℝ) Δ) ε :=
  expMech_isPureDP hΔ hsens

end Examples

end Fintype

end DPlean4

end -- noncomputable section
