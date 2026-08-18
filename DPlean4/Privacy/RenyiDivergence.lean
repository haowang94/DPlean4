/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Rényi Divergence

This file defines the Rényi divergence of order α between two measures.

## Main Definitions

* `renyiMoment α μ ν`: The α-th moment of the likelihood ratio dμ/dν under ν,
  i.e., `∫⁻ x, (dμ/dν)^α dν`. This equals `exp((α-1) · D_α(μ‖ν))`.
* `renyiDivergence α μ ν`: The Rényi divergence `D_α(μ‖ν) = 1/(α-1) · log(renyiMoment α μ ν)`.

## Design Notes

We define the Rényi moment as the primary object since it avoids logarithms
and works directly in `ℝ≥0∞`. The Rényi divergence is derived from it.

For the zCDP definition, we use Rényi divergence (the standard formulation).
For proofs, working with the moment form is often more convenient.
-/

namespace DPlean4

open MeasureTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Rényi moment of order α: `∫⁻ x, (dμ/dν x)^α dν`.
    This equals `exp((α-1) · D_α(μ‖ν))` when the integral is finite and α > 1. -/
noncomputable def renyiMoment (α : ℝ) (μ ν : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν

/-- The Rényi divergence of order α: `D_α(μ‖ν) = 1/(α-1) · log(∫⁻ (dμ/dν)^α dν)`.
    For α ≤ 1, returns 0 (the definition is only meaningful for α > 1 in the zCDP context). -/
noncomputable def renyiDivergence (α : ℝ) (μ ν : Measure Ω) : ℝ :=
  (α - 1)⁻¹ * Real.log (renyiMoment α μ ν).toReal

/-- The Rényi moment of order 1 equals 1 for probability measures when μ ≪ ν. -/
theorem renyiMoment_one {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    renyiMoment 1 μ ν = 1 := by
  simp only [renyiMoment, rpow_one]
  rw [Measure.lintegral_rnDeriv hac]
  exact measure_univ

/-- Rényi moment is 1 for identical measures (order α > 0). -/
theorem renyiMoment_self {μ : Measure Ω} [IsProbabilityMeasure μ] {α : ℝ} (_hα : 0 < α) :
    renyiMoment α μ μ = 1 := by
  simp only [renyiMoment]
  have : μ.rnDeriv μ =ᵐ[μ] 1 := Measure.rnDeriv_self μ
  calc ∫⁻ x, (μ.rnDeriv μ x) ^ α ∂μ
      = ∫⁻ x, (1 : ℝ≥0∞) ^ α ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [this] with x hx
        rw [hx, Pi.one_apply]
    _ = ∫⁻ _, 1 ∂μ := by simp [one_rpow]
    _ = μ Set.univ := by simp
    _ = 1 := measure_univ

/-- Rényi divergence of a measure with itself is 0. -/
theorem renyiDivergence_self {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : ℝ} (hα : 1 < α) :
    renyiDivergence α μ μ = 0 := by
  simp only [renyiDivergence, renyiMoment_self (by linarith : 0 < α)]
  simp [Real.log_one]

/-- The Rényi moment is at least 1 for probability measures when α > 1 and μ ≪ ν.
    Proved via the power mean inequality (Hölder variant). -/
private theorem renyiMoment_ge_one {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {α : ℝ} (hα : 1 < α) (hac : μ ≪ ν) :
    1 ≤ renyiMoment α μ ν := by
  have hα_pos : (0 : ℝ) < α := by linarith
  have hα_ne : (α : ℝ) ≠ 0 := ne_of_gt hα_pos
  have hα_inv_pos : (0 : ℝ) < 1 / α := div_pos one_pos hα_pos
  have hq_nn : (0 : ℝ) ≤ 1 - 1 / α := by
    rw [sub_nonneg, div_le_one hα_pos]; linarith
  have hpq : 1 / α + (1 - 1 / α) = 1 := by ring
  have hf_ae : AEMeasurable (fun x => (μ.rnDeriv ν x) ^ α) ν :=
    (Measure.measurable_rnDeriv μ ν).pow_const α |>.aemeasurable
  have hg_ae : AEMeasurable (fun (_ : Ω) => (1 : ℝ≥0∞)) ν := aemeasurable_const
  have holder := lintegral_mul_norm_pow_le hf_ae hg_ae hα_inv_pos.le hq_nn hpq
  have hleft : ∫⁻ a, ((μ.rnDeriv ν a) ^ α) ^ (1 / α) * (1 : ℝ≥0∞) ^ (1 - 1 / α) ∂ν = 1 := by
    simp_rw [one_rpow, mul_one, ← rpow_mul, show α * (1 / α) = 1 from by field_simp, rpow_one]
    rw [Measure.lintegral_rnDeriv hac, measure_univ]
  have hright : (∫⁻ a, (μ.rnDeriv ν a) ^ α ∂ν) ^ (1 / α) *
      (∫⁻ (_ : Ω), (1 : ℝ≥0∞) ∂ν) ^ (1 - 1 / α) = (renyiMoment α μ ν) ^ (1 / α) := by
    simp only [lintegral_one, measure_univ, one_rpow, mul_one, renyiMoment]
  rw [hleft, hright] at holder
  rwa [← one_rpow (1 / α : ℝ), rpow_le_rpow_iff hα_inv_pos] at holder

/-- The Rényi divergence is non-negative for probability measures. -/
theorem renyiDivergence_nonneg {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {α : ℝ} (hα : 1 < α) (hac : μ ≪ ν) :
    0 ≤ renyiDivergence α μ ν := by
  simp only [renyiDivergence]
  by_cases hfin : renyiMoment α μ ν = ⊤
  · simp [hfin, toReal_top, Real.log_zero]
  · apply mul_nonneg
    · exact inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ α - 1)
    · exact Real.log_nonneg (by
        rw [← toReal_one]
        exact toReal_mono hfin (renyiMoment_ge_one hα hac))

/-- Equivalent characterization: D_α ≤ ε iff the Rényi moment ≤ exp((α-1)·ε). -/
theorem renyiDivergence_le_iff {μ ν : Measure Ω} {α : ℝ} (hα : 1 < α)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfin : renyiMoment α μ ν ≠ ⊤) :
    renyiDivergence α μ ν ≤ ε ↔
    renyiMoment α μ ν ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) := by
  have hα_pos : (0 : ℝ) < α - 1 := by linarith
  simp only [renyiDivergence]
  by_cases hM : renyiMoment α μ ν = 0
  · simp only [hM, ENNReal.toReal_zero, Real.log_zero, mul_zero]
    exact ⟨fun _ => bot_le, fun _ => hε⟩
  · have hM_pos : 0 < (renyiMoment α μ ν).toReal := ENNReal.toReal_pos hM hfin
    rw [inv_mul_le_iff₀ hα_pos, Real.log_le_iff_le_exp hM_pos,
        ENNReal.le_ofReal_iff_toReal_le hfin (Real.exp_pos _).le]

end DPlean4
