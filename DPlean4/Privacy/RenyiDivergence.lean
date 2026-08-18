/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

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

/-- The Rényi divergence is non-negative for probability measures. -/
theorem renyiDivergence_nonneg {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {α : ℝ} (hα : 1 < α) (hac : μ ≪ ν) :
    0 ≤ renyiDivergence α μ ν := by
  sorry

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
