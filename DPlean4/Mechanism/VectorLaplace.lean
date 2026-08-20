/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Pure
import DPlean4.Privacy.Composition
import DPlean4.Basic.Sensitivity
import DPlean4.Mechanism.Laplace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Vector Laplace Mechanism

This file defines the vector Laplace mechanism for differential privacy, which adds
independent Laplace noise to each coordinate of a vector-valued query.

## Main Definitions

* `vectorLaplaceMech q Δ ε`: adds independent Lap(0, Δ/ε) noise to each coordinate

## Main Results

* `vectorLaplaceMech_isPureDP`: the mechanism satisfies ε-pure DP when the query
  has L1 vector sensitivity at most Δ.

## Design Notes

Uses `[Fintype ι]` so the same definition handles vectors, matrices, and tensors.

The mechanism adds independent Laplace noise with scale b = Δ/ε to each coordinate.
The privacy budget decomposes as:
  total ε = ∑ᵢ |q d₁ i - q d₂ i| / b ≤ Δ / b = ε

This uses **L1 sensitivity** (∑ᵢ |q d₁ i - q d₂ i| ≤ Δ), in contrast to the
vector Gaussian mechanism which uses L2 sensitivity.

## References

* Dwork, McSherry, Nissim, Smith (2006), "Calibrating Noise to Sensitivity"
* Dwork & Roth (2014), "The Algorithmic Foundations of Differential Privacy"
-/

noncomputable section

namespace DPlean4

open MeasureTheory Measure

open scoped NNReal ENNReal Real

variable {D : Type*}

-- ============================================================================
-- Vector Laplace Mechanism Definition
-- ============================================================================

/-- The vector Laplace mechanism: given a query `q : D → ι → ℝ`, add
    independent Lap(0, Δ/ε) noise to each coordinate.
    The output for database d is the product measure ∏ᵢ Lap(q(d)(i), Δ/ε). -/
def vectorLaplaceMech {ι : Type*} [Fintype ι]
    (q : D → ι → ℝ) (Δ ε : ℝ≥0) : Mechanism D (ι → ℝ) :=
  fun d => ⟨Measure.pi (fun i => laplaceMeasure (q d i) (Δ / ε)), inferInstance⟩

@[simp]
theorem vectorLaplaceMech_toMeasure {ι : Type*} [Fintype ι]
    (q : D → ι → ℝ) (Δ ε : ℝ≥0) (d : D) :
    (vectorLaplaceMech q Δ ε d).toMeasure =
      Measure.pi (fun i => laplaceMeasure (q d i) (Δ / ε)) :=
  rfl

-- ============================================================================
-- Privacy Proof
-- ============================================================================

/-- **The vector Laplace mechanism satisfies pure ε-differential privacy.**

    Given a vector-valued query with L1 sensitivity Δ (meaning
    ∑ᵢ |q d₁ i - q d₂ i| ≤ Δ for all adjacent d₁, d₂) and independent
    Laplace noise with scale b = Δ/ε, the mechanism satisfies ε-DP.

    Proof sketch: each coordinate i contributes εᵢ = |q d₁ i - q d₂ i| / b
    to the privacy budget via the scalar Laplace density ratio bound.
    By composition of independent mechanisms, the total budget is
    ∑ᵢ εᵢ = (∑ᵢ |q d₁ i - q d₂ i|) / b ≤ Δ / b = ε. -/
theorem vectorLaplaceMech_isPureDP {ι : Type*} [Fintype ι]
    {adj : D → D → Prop} {q : D → ι → ℝ} {Δ ε : ℝ≥0}
    (hε : ε ≠ 0)
    (hsens : HasL1VectorSensitivity adj q Δ) :
    IsPureDP adj (vectorLaplaceMech q Δ ε) ε := by
  intro d₁ d₂ hadj
  set b := Δ / ε with hb_def
  have h_eq : ∀ d, vectorLaplaceMech q Δ ε d =
      ProbabilityMeasure.pi (fun i => ⟨laplaceMeasure (q d i) b, inferInstance⟩) :=
    fun d => ProbabilityMeasure.toMeasure_injective rfl
  rw [h_eq, h_eq]
  by_cases hΔ : Δ = 0
  · subst hΔ
    have hq : q d₁ = q d₂ := by
      ext i
      have h_sum := hsens d₁ d₂ hadj
      simp only [NNReal.coe_zero] at h_sum
      have h_nonneg : ∀ j, 0 ≤ |q d₁ j - q d₂ j| := fun j => abs_nonneg _
      have h_zero := le_antisymm h_sum (Finset.sum_nonneg (fun j _ => h_nonneg j))
      exact sub_eq_zero.mp (abs_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j)).mp h_zero i
          (Finset.mem_univ i)))
    simp_rw [hq]
    exact measureClose_epsilon_mono (pureMeasureClose_refl _) (by positivity)
  · have hb : b ≠ 0 := div_ne_zero hΔ hε
    have hb_pos : (0 : ℝ) < ↑b := by positivity
    have hb_ne : (↑b : ℝ) ≠ 0 := ne_of_gt hb_pos
    have scale_cancel : (↑ε : ℝ) * (↑b : ℝ) = ↑Δ := by
      change (↑ε : ℝ) * (↑(Δ / ε : ℝ≥0) : ℝ) = ↑Δ
      rw [← NNReal.coe_mul, mul_comm, div_mul_cancel₀ Δ hε]
    let ε_i : ι → NNReal := fun i => ⟨|q d₁ i - q d₂ i| / ↑b, by positivity⟩
    have h_coord : ∀ i, PureMeasureClose (ε_i i)
        (⟨laplaceMeasure (q d₁ i) b, inferInstance⟩ : ProbabilityMeasure ℝ)
        (⟨laplaceMeasure (q d₂ i) b, inferInstance⟩ : ProbabilityMeasure ℝ) := by
      intro i s hs
      simp only [ENNReal.coe_zero, add_zero]
      change laplaceMeasure (q d₁ i) b s ≤
          ENNReal.ofReal (rexp (|q d₁ i - q d₂ i| / ↑b)) * laplaceMeasure (q d₂ i) b s
      rw [laplaceMeasure_of_scale_ne_zero _ hb, laplaceMeasure_of_scale_ne_zero _ hb,
          withDensity_apply _ hs, withDensity_apply _ hs]
      calc ∫⁻ x in s, laplacePDF (q d₁ i) b x
          ≤ ∫⁻ x in s, ENNReal.ofReal (rexp (|q d₁ i - q d₂ i| / ↑b)) *
              laplacePDF (q d₂ i) b x :=
            lintegral_mono (fun x => laplacePDF_le_exp_mul (q d₁ i) (q d₂ i) hb x)
        _ = ENNReal.ofReal (rexp (|q d₁ i - q d₂ i| / ↑b)) *
              ∫⁻ x in s, laplacePDF (q d₂ i) b x :=
            lintegral_const_mul _ (measurable_laplacePDF _ _)
    apply measureClose_epsilon_mono (pureMeasureClose_pi h_coord)
    show ∑ i, ε_i i ≤ ε
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_sum]
    calc ∑ i, ↑(ε_i i)
        = ∑ i, |q d₁ i - q d₂ i| / ↑b := by rfl
      _ = (∑ i, |q d₁ i - q d₂ i|) / ↑b := by rw [Finset.sum_div]
      _ ≤ ↑Δ / ↑b :=
          div_le_div_of_nonneg_right (hsens d₁ d₂ hadj) hb_pos.le
      _ = ↑ε := by
          rw [show (↑Δ : ℝ) = ↑ε * ↑b from scale_cancel.symm,
              mul_div_cancel_right₀ _ hb_ne]

-- ============================================================================
-- Approximate DP from pure DP
-- ============================================================================

/-- The vector Laplace mechanism satisfies (ε',δ)-approximate DP for any ε' ≥ ε,
    by relaxing pure DP to approximate DP. -/
theorem vectorLaplaceMech_isApproxDP {ι : Type*} [Fintype ι]
    {adj : D → D → Prop} {q : D → ι → ℝ} {Δ ε : ℝ≥0}
    (hε : ε ≠ 0)
    (hsens : HasL1VectorSensitivity adj q Δ)
    {ε' δ : NNReal} (hle : ε ≤ ε') :
    IsApproxDP adj (vectorLaplaceMech q Δ ε) ε' δ :=
  isApproxDP_of_isPureDP δ (isPureDP_mono (vectorLaplaceMech_isPureDP hε hsens) hle)

end DPlean4

end -- noncomputable section
