/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Gaussian
import DPlean4.Privacy.ZCDP
import DPlean4.Basic.Adjacency

/-!
# Independent Scalar Gaussian Releases Inspired by DP-SGD

This file demonstrates fixed, independent releases of scalar clipped sums.
It is an accounting illustration inspired by DP-SGD, not a formalization of
adaptive optimization, minibatch sampling, or a training algorithm.

## Algorithm (simplified, one step)

Given a dataset of records, each contributing a gradient:
1. **Clip** each per-example gradient to bound its L2 norm by C
2. **Sum** the clipped gradients
3. **Add** Gaussian noise calibrated to the clipping bound

## Privacy Analysis

- Each person's clipped gradient has L2 norm ≤ C, so adding/removing one person
  changes the sum by at most C. This gives L2 sensitivity Δ = C.
- One step of noisy gradient descent with variance v is ρ-zCDP with ρ = C²/(2v).
- After k steps, zCDP composes linearly: k·ρ-zCDP (Bun & Dwork 2016).
- Convert to (ε,δ)-DP via the zCDP→approxDP theorem.

## References

* Abadi et al. (2016), "Deep Learning with Differential Privacy"
* Bun & Dwork (2016), "Concentrated Differential Privacy" (zCDP composition)
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*}

-- ============================================================================
-- Clipped gradient sum: sensitivity analysis
-- ============================================================================

/-- Clip a real value to [-C, C]. -/
def clipGrad (C : ℝ) (x : ℝ) : ℝ := max (-C) (min C x)

/-- Clipping to [-C, C] bounds the absolute value. -/
theorem abs_clipGrad_le {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clipGrad C x| ≤ C := by
  simp only [clipGrad]
  rw [abs_le]
  constructor
  · linarith [le_max_left (-C) (min C x)]
  · exact le_trans (max_le (by linarith) (min_le_left C x)) (le_refl C)

/-- Clipped sum: sum of per-example values, each clipped to [-C, C]. -/
def clippedSum (f : α → ℝ) (C : ℝ) (l : List α) : ℝ :=
  (l.map (fun a => clipGrad C (f a))).sum

/-- Clipped sum has L1 sensitivity C under add/remove adjacency.
    Adding one record changes the sum by at most C (the clipping bound). -/
theorem clippedSum_sensitivity (f : α → ℝ) (C : ℝ≥0) :
    HasL1Sensitivity ListHeadAddRemove (clippedSum f C) C := by
  intro l₁ l₂ hadj
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]
    simp only [clippedSum, List.map_cons, List.sum_cons]
    rw [show (clipGrad C (f a) + (s.map fun a => clipGrad C (f a)).sum) -
      (s.map fun a => clipGrad C (f a)).sum = clipGrad C (f a) by ring]
    exact abs_clipGrad_le C.2 (f a)
  · rw [h.1, h.2]
    simp only [clippedSum, List.map_cons, List.sum_cons]
    rw [show (s.map fun a => clipGrad C (f a)).sum -
      (clipGrad C (f a) + (s.map fun a => clipGrad C (f a)).sum) =
      -(clipGrad C (f a)) by ring, abs_neg]
    exact abs_clipGrad_le C.2 (f a)

-- ============================================================================
-- DP-SGD: One Step
-- ============================================================================

/-- One fixed scalar release: compute a clipped gradient sum and add Gaussian noise.
    Parameters:
    - f : α → ℝ — per-example gradient function (scalar for simplicity)
    - C : ℝ≥0 — clipping bound
    - v : ℝ≥0 — noise variance -/
def dpsgdStep (f : α → ℝ) (C v : ℝ≥0) : Mechanism (List α) ℝ :=
  gaussianMech (clippedSum f C) v

/-- **One scalar Gaussian release is ρ-zCDP** with ρ = C²/(2v).

    This follows from:
    1. Clipped sum has sensitivity C (per `clippedSum_sensitivity`)
    2. Gaussian mechanism with sensitivity Δ and variance v is Δ²/(2v)-zCDP -/
theorem dpsgdStep_isZCDP (f : α → ℝ) {C v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP ListHeadAddRemove (dpsgdStep f C v)
      (C ^ 2 / (2 * v)) :=
  gaussianMech_isZCDP hv (clippedSum_sensitivity f C).toL2

-- ============================================================================
-- DP-SGD: Composition over k steps
-- ============================================================================

/-- The product of two fixed independent noisy scalar releases is (2ρ)-zCDP. -/
theorem dpsgd_two_steps_zCDP (f₁ f₂ : α → ℝ) {C v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP ListHeadAddRemove
      ((dpsgdStep f₁ C v).prod (dpsgdStep f₂ C v))
      (C ^ 2 / (2 * v) + C ^ 2 / (2 * v)) :=
  isZCDP_prod (dpsgdStep_isZCDP f₁ hv) (dpsgdStep_isZCDP f₂ hv)

-- ============================================================================
-- Concrete example: DP-SGD with specific parameters
-- ============================================================================

/-- Concrete DP-SGD example: clipping bound C=1, noise variance v=2.

    ρ = C²/(2v) = 1/4 per step, so 2 steps → 2ρ = 1/2.
    This demonstrates the fixed independent-release accounting pipeline. -/
theorem dpsgd_concrete_two_steps (f₁ f₂ : α → ℝ) :
    IsZCDP ListHeadAddRemove
      ((dpsgdStep f₁ (1 : ℝ≥0) (2 : ℝ≥0)).prod (dpsgdStep f₂ (1 : ℝ≥0) (2 : ℝ≥0)))
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) + (1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) :=
  dpsgd_two_steps_zCDP f₁ f₂ (by norm_num)

/-- DP-SGD postprocessing: applying a learning rate scaling to the noisy
    gradient preserves zCDP, since postprocessing can only decrease privacy loss. -/
theorem dpsgd_postprocess (f : α → ℝ) {C v : ℝ≥0} (hv : v ≠ 0)
    {η : ℝ} (hη : Measurable (fun x : ℝ => η * x)) :
    IsZCDP ListHeadAddRemove
      (fun d => ProbabilityMeasure.map (dpsgdStep f C v d) hη.aemeasurable)
      (C ^ 2 / (2 * v)) := by
  exact isZCDP_postprocess (dpsgdStep_isZCDP f hv) hη

end DPlean4.Examples

end -- noncomputable section
