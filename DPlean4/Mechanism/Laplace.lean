/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Distribution.Laplace
import DPlean4.Privacy.Pure
import DPlean4.Basic.Sensitivity

/-!
# The Laplace Mechanism

This file defines the Laplace mechanism and proves it satisfies pure ε-differential privacy.

## Main Definitions

* `laplaceMech q Δ ε`: The Laplace mechanism that adds `Lap(0, Δ/ε)` noise to query `q`

## Main Results

* `laplaceMech_isPureDP`: The Laplace mechanism satisfies ε-DP when the query has
  L1 sensitivity at most `Δ` (Dwork, McSherry, Nissim, Smith, 2006)

## Proof Strategy

The key step is the pointwise density ratio bound from `Distribution/Laplace.lean`:

  `f(x; q(d₁), b) ≤ exp(|q(d₁) - q(d₂)| / b) · f(x; q(d₂), b)`

Integrating both sides over any measurable set gives the measure-level bound.
The sensitivity bound `|q(d₁) - q(d₂)| ≤ Δ` and scale calibration `b = Δ/ε`
yield `exp(Δ/b) = exp(ε)`.
-/

noncomputable section

namespace DPlean4

open MeasureTheory
open scoped ENNReal NNReal Real

variable {D : Type*}

-- ============================================================================
-- ENNReal density bound
-- ============================================================================

/-- The Laplace density ratio bound lifted to ENNReal. -/
theorem laplacePDF_le_exp_mul (μ₁ μ₂ : ℝ) {b : ℝ≥0} (hb : b ≠ 0) (x : ℝ) :
    laplacePDF μ₁ b x ≤ ENNReal.ofReal (rexp (|μ₁ - μ₂| / ↑b)) * laplacePDF μ₂ b x := by
  simp only [laplacePDF]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (laplacePDFReal_le_exp_mul μ₁ μ₂ hb x)

-- ============================================================================
-- The Laplace Mechanism
-- ============================================================================

/-- The Laplace mechanism: given a query `q : D → ℝ`, sensitivity bound `Δ`, and
    privacy parameter `ε`, returns a mechanism that adds Laplace noise with
    scale `b = Δ / ε` to the query output.

    When `Δ = 0` or `ε = 0`, the scale is 0 and the mechanism degenerates to
    a Dirac measure at `q d` (deterministic output). -/
def laplaceMech (q : D → ℝ) (Δ ε : ℝ≥0) : Mechanism D ℝ :=
  fun d => ⟨laplaceMeasure (q d) (Δ / ε), inferInstance⟩

@[simp]
theorem laplaceMech_toMeasure (q : D → ℝ) (Δ ε : ℝ≥0) (d : D) :
    (laplaceMech q Δ ε d).toMeasure = laplaceMeasure (q d) (Δ / ε) := rfl

-- ============================================================================
-- Privacy Proof
-- ============================================================================

/-- **The Laplace mechanism satisfies pure ε-differential privacy.**

    If `q : D → ℝ` has L1 sensitivity at most `Δ` under adjacency `adj`,
    then the Laplace mechanism with noise scale `Δ/ε` satisfies ε-DP.

    This is the fundamental privacy theorem for the Laplace mechanism
    (Dwork, McSherry, Nissim, Smith, 2006). -/
theorem laplaceMech_isPureDP {adj : D → D → Prop} {q : D → ℝ} {Δ ε : ℝ≥0}
    (hε : ε ≠ 0)
    (hsens : HasL1Sensitivity adj q ↑Δ) :
    IsPureDP adj (laplaceMech q Δ ε) ε := by
  intro d₁ d₂ hadj s hs
  simp only [laplaceMech_toMeasure, ENNReal.coe_zero, add_zero]
  by_cases hΔ : Δ = 0
  · -- Zero sensitivity: mechanism is Dirac, q constant on adjacent pairs
    subst hΔ
    simp only [zero_div, laplaceMeasure_of_scale_zero]
    have hq : q d₁ = q d₂ := by
      have h := hsens d₁ d₂ hadj
      simp only [NNReal.coe_zero] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    rw [hq]
    exact le_mul_of_one_le_left' (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (NNReal.coe_nonneg ε)))
  · -- Main case: positive sensitivity, use density ratio bound
    have hb : Δ / ε ≠ 0 := div_ne_zero hΔ hε
    rw [laplaceMeasure_of_scale_ne_zero _ hb, laplaceMeasure_of_scale_ne_zero _ hb]
    rw [withDensity_apply _ hs, withDensity_apply _ hs]
    set b := Δ / ε with hb_def
    have hb_pos : (0 : ℝ) < ↑b := by positivity
    have scale_cancel : (↑ε : ℝ) * (↑b : ℝ) = ↑Δ := by
      change (↑ε : ℝ) * (↑(Δ / ε : ℝ≥0) : ℝ) = ↑Δ
      rw [← NNReal.coe_mul, mul_comm, div_mul_cancel₀ Δ hε]
    calc ∫⁻ x in s, laplacePDF (q d₁) b x
        ≤ ∫⁻ x in s, ENNReal.ofReal (rexp (|q d₁ - q d₂| / ↑b)) *
            laplacePDF (q d₂) b x := by
          apply lintegral_mono
          exact fun x => laplacePDF_le_exp_mul (q d₁) (q d₂) hb x
      _ = ENNReal.ofReal (rexp (|q d₁ - q d₂| / ↑b)) *
            ∫⁻ x in s, laplacePDF (q d₂) b x := by
          rw [lintegral_const_mul _ (measurable_laplacePDF _ _)]
      _ ≤ ENNReal.ofReal (rexp ↑ε) * ∫⁻ x in s, laplacePDF (q d₂) b x := by
          have hb_ne : (↑b : ℝ) ≠ 0 := ne_of_gt hb_pos
          have exp_bound : rexp (|q d₁ - q d₂| / ↑b) ≤ rexp ↑ε := by
            apply Real.exp_le_exp_of_le
            calc |q d₁ - q d₂| / ↑b
                ≤ ↑Δ / ↑b :=
                  div_le_div_of_nonneg_right (hsens d₁ d₂ hadj) hb_pos.le
              _ = ↑ε := by
                  rw [show (↑Δ : ℝ) = ↑ε * ↑b from scale_cancel.symm,
                      mul_div_cancel_right₀ _ hb_ne]
          gcongr

end DPlean4

end -- noncomputable section
