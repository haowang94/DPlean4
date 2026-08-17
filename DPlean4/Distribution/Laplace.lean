/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Density

/-!
# Laplace Distribution

This file defines the Laplace (double exponential) distribution on ℝ, which is
not available in Mathlib.

## Main Definitions

* `laplacePDFReal μ b x` : Real-valued Laplace density `(2b)⁻¹ exp(-|x-μ|/b)`
* `laplacePDF μ b x` : ENNReal-valued Laplace density
* `laplaceMeasure μ b` : The Laplace measure on ℝ

## Properties

* Nonnegativity, measurability, integrability
* Normalization: integrates to 1
* Translation law, symmetry
* **Density ratio bound**: `f(x;μ₁,b) / f(x;μ₂,b) ≤ exp(|μ₁-μ₂|/b)`
  This is the key lemma for proving the Laplace mechanism satisfies ε-DP.

## Design Notes

Follows the Mathlib `gaussianPDFReal`/`gaussianPDF`/`gaussianReal` three-layer pattern.
-/

noncomputable section

namespace DPlean4

open MeasureTheory
open scoped ENNReal NNReal Real

-- ============================================================================
-- Layer 1: Real-valued Laplace PDF
-- ============================================================================

/-- The real-valued Laplace probability density function.
    `laplacePDFReal μ b x = (2b)⁻¹ * exp(-|x - μ| / b)` -/
def laplacePDFReal (μ : ℝ) (b : ℝ≥0) (x : ℝ) : ℝ :=
  (2 * (b : ℝ))⁻¹ * rexp (-(|x - μ|) / (b : ℝ))

/-- The Laplace density is nonneg everywhere. -/
theorem laplacePDFReal_nonneg (μ : ℝ) (b : ℝ≥0) (x : ℝ) :
    0 ≤ laplacePDFReal μ b x := by
  unfold laplacePDFReal
  apply mul_nonneg
  · apply inv_nonneg.mpr; positivity
  · exact Real.exp_nonneg _

/-- The Laplace density is strictly positive when b > 0. -/
theorem laplacePDFReal_pos (μ : ℝ) {b : ℝ≥0} (hb : b ≠ 0) (x : ℝ) :
    0 < laplacePDFReal μ b x := by
  unfold laplacePDFReal
  apply _root_.mul_pos
  · apply inv_pos.mpr; positivity
  · exact Real.exp_pos _

/-- When b = 0, the Laplace density is 0 everywhere. -/
theorem laplacePDFReal_zero_scale (μ : ℝ) (x : ℝ) :
    laplacePDFReal μ 0 x = 0 := by
  simp [laplacePDFReal]

/-- The Laplace density is measurable in x. -/
@[fun_prop]
theorem measurable_laplacePDFReal (μ : ℝ) (b : ℝ≥0) :
    Measurable (laplacePDFReal μ b) := by
  unfold laplacePDFReal
  fun_prop

/-- The Laplace density is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable_laplacePDFReal (μ : ℝ) (b : ℝ≥0) :
    StronglyMeasurable (laplacePDFReal μ b) :=
  (measurable_laplacePDFReal μ b).stronglyMeasurable

-- ============================================================================
-- Layer 2: ENNReal-valued Laplace PDF
-- ============================================================================

/-- The ENNReal-valued Laplace density, suitable for `Measure.withDensity`. -/
def laplacePDF (μ : ℝ) (b : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (laplacePDFReal μ b x)

/-- The ENNReal Laplace density is measurable. -/
@[fun_prop]
theorem measurable_laplacePDF (μ : ℝ) (b : ℝ≥0) :
    Measurable (laplacePDF μ b) := by
  unfold laplacePDF
  fun_prop

/-- The Lebesgue integral of the Laplace density equals 1 (when b > 0). -/
@[simp]
theorem lintegral_laplacePDF_eq_one (μ : ℝ) {b : ℝ≥0} (hb : b ≠ 0) :
    ∫⁻ x, laplacePDF μ b x = 1 := by
  sorry -- TODO: Integration proof via translation + splitting + exponential integral

-- ============================================================================
-- Layer 3: The Laplace Measure
-- ============================================================================

/-- The Laplace measure on ℝ with location μ and scale b.
    Degenerates to a Dirac mass at μ when b = 0. -/
def laplaceMeasure (μ : ℝ) (b : ℝ≥0) : Measure ℝ :=
  if b = 0 then Measure.dirac μ else volume.withDensity (laplacePDF μ b)

theorem laplaceMeasure_of_scale_ne_zero (μ : ℝ) {b : ℝ≥0} (hb : b ≠ 0) :
    laplaceMeasure μ b = volume.withDensity (laplacePDF μ b) := by
  simp [laplaceMeasure, hb]

theorem laplaceMeasure_of_scale_zero (μ : ℝ) :
    laplaceMeasure μ 0 = Measure.dirac μ := by
  simp [laplaceMeasure]

/-- The Laplace measure is a probability measure. -/
instance instIsProbabilityMeasureLaplace (μ : ℝ) (b : ℝ≥0) :
    IsProbabilityMeasure (laplaceMeasure μ b) where
  measure_univ := by
    by_cases hb : b = 0
    · simp [laplaceMeasure, hb, Measure.dirac_apply_of_mem (Set.mem_univ μ)]
    · rw [laplaceMeasure_of_scale_ne_zero μ hb]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact lintegral_laplacePDF_eq_one μ hb

-- ============================================================================
-- Density Ratio Bound (key lemma for DP)
-- ============================================================================

/-- The pointwise density ratio of two Laplace distributions with the same scale
    but different locations is bounded by exp(|μ₁ - μ₂| / b).

    This is the core calculation behind the Laplace mechanism's ε-DP proof. -/
theorem laplacePDFReal_ratio_le (μ₁ μ₂ : ℝ) {b : ℝ≥0} (hb : b ≠ 0) (x : ℝ) :
    laplacePDFReal μ₁ b x / laplacePDFReal μ₂ b x ≤
      rexp (|μ₁ - μ₂| / (b : ℝ)) := by
  rw [div_le_iff (laplacePDFReal_pos μ₂ hb x)]
  exact laplacePDFReal_le_exp_mul μ₁ μ₂ hb x

/-- Equivalent formulation: the density at x under μ₁ is at most
    exp(|μ₁-μ₂|/b) times the density at x under μ₂. -/
theorem laplacePDFReal_le_exp_mul (μ₁ μ₂ : ℝ) {b : ℝ≥0} (hb : b ≠ 0) (x : ℝ) :
    laplacePDFReal μ₁ b x ≤
      rexp (|μ₁ - μ₂| / (b : ℝ)) * laplacePDFReal μ₂ b x := by
  have hb_pos : (0 : ℝ) < b := by positivity
  have key : |x - μ₂| - |x - μ₁| ≤ |μ₁ - μ₂| := by
    have h := abs_sub_abs_le_abs_sub (x - μ₂) (x - μ₁)
    have : (x - μ₂) - (x - μ₁) = μ₁ - μ₂ := by ring
    rw [this] at h; exact h
  unfold laplacePDFReal
  rw [mul_comm (rexp (|μ₁ - μ₂| / ↑b)) _, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * ↑b))
  rw [← Real.exp_add]
  apply Real.exp_le_exp_of_le
  simp only [div_eq_mul_inv]
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (le_of_lt hb_pos))
  linarith

-- ============================================================================
-- Translation Law
-- ============================================================================

/-- Shifting the location parameter shifts the distribution. -/
theorem laplacePDFReal_translate (μ c : ℝ) (b : ℝ≥0) (x : ℝ) :
    laplacePDFReal (μ + c) b x = laplacePDFReal μ b (x - c) := by
  unfold laplacePDFReal
  ring_nf

-- ============================================================================
-- Symmetry
-- ============================================================================

/-- The Laplace density is symmetric about its location parameter. -/
theorem laplacePDFReal_symm (μ : ℝ) (b : ℝ≥0) (x : ℝ) :
    laplacePDFReal μ b (μ + x) = laplacePDFReal μ b (μ - x) := by
  unfold laplacePDFReal
  congr 1
  congr 1
  congr 1
  rw [show μ + x - μ = x from by ring, show μ - x - μ = -x from by ring, abs_neg]

end DPlean4

end -- noncomputable section
