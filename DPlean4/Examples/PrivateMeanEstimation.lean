/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Postprocessing
import DPlean4.Basic.Adjacency

/-!
# Private Mean Estimation

This file demonstrates private mean estimation using the Laplace mechanism
and postprocessing. This is a fundamental DP algorithm appearing in nearly
every DP textbook.

## Algorithm (Dwork & Roth 2014, Section 3.5.2)

Given a database of real values in [0, 1]:
1. Sum all values (sensitivity 1 under add/remove)
2. Add Laplace(1/ε) noise to the sum
3. Divide by the (public) database size n

The last step is measurable postprocessing, so privacy is preserved.

## Main Results

* `private_sum_pureDP`: Summing values in [0,1] + Laplace noise is ε-DP
* `private_mean_pureDP`: Dividing by n preserves ε-DP (postprocessing)

## References

* Dwork & Roth, "The Algorithmic Foundations of Differential Privacy" (2014),
  Section 3.5.2
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open scoped NNReal

-- ============================================================================
-- Clamped sum sensitivity
-- ============================================================================

/-- Clamp a real number to the interval [lo, hi]. -/
def clamp (lo hi : ℝ) (x : ℝ) : ℝ := max lo (min hi x)

/-- The clamped sum of a list of values. -/
def clampedSum (f : α → ℝ) (lo hi : ℝ) (l : List α) : ℝ :=
  (l.map (fun a => clamp lo hi (f a))).sum

/-- Clamped values lie in [lo, hi]. -/
private theorem clamp_le_hi {lo hi x : ℝ} (hle : lo ≤ hi) : clamp lo hi x ≤ hi := by
  simp only [clamp]; exact max_le hle (min_le_left hi x)

private theorem lo_le_clamp {lo hi x : ℝ} : lo ≤ clamp lo hi x := by
  simp only [clamp]; exact le_max_left lo _

/-- The clamped sum over [0, B] has sensitivity B under add/remove adjacency.
    Adding one element changes the sum by at most B (the element's clamped value). -/
theorem clampedSum_sensitivity {B : ℝ} (hB : 0 ≤ B) (f : α → ℝ) :
    HasL1Sensitivity ListHeadAddRemove (clampedSum f 0 B) B := by
  intro l₁ l₂ hadj
  simp only [clampedSum]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]
    simp only [List.map_cons, List.sum_cons]
    have hclamp_nn : 0 ≤ clamp 0 B (f a) := lo_le_clamp
    have hclamp_le : clamp 0 B (f a) ≤ B := clamp_le_hi hB
    rw [show clamp 0 B (f a) + (List.map (fun a => clamp 0 B (f a)) s).sum -
        (List.map (fun a => clamp 0 B (f a)) s).sum = clamp 0 B (f a) by ring]
    rw [abs_of_nonneg hclamp_nn]
    exact hclamp_le
  · rw [h.1, h.2]
    simp only [List.map_cons, List.sum_cons]
    have hclamp_nn : 0 ≤ clamp 0 B (f a) := lo_le_clamp
    have hclamp_le : clamp 0 B (f a) ≤ B := clamp_le_hi hB
    rw [show (List.map (fun a => clamp 0 B (f a)) s).sum -
        (clamp 0 B (f a) + (List.map (fun a => clamp 0 B (f a)) s).sum) =
        -(clamp 0 B (f a)) by ring]
    rw [abs_neg, abs_of_nonneg hclamp_nn]
    exact hclamp_le

-- ============================================================================
-- Special case: sum of [0, 1]-bounded values (sensitivity 1)
-- ============================================================================

/-- Sum of [0,1]-clamped values has sensitivity 1. -/
theorem clampedSum01_sensitivity (f : α → ℝ) :
    HasL1Sensitivity ListHeadAddRemove (clampedSum f 0 1) (↑(1 : ℝ≥0)) := by
  simp only [NNReal.coe_one]
  exact clampedSum_sensitivity (by norm_num) f

-- ============================================================================
-- Example 1: Private sum via Laplace mechanism
-- ============================================================================

/-- **Private sum of bounded values is ε-DP.**

    Given a value function f : α → ℝ, clamp to [0, 1] and add Laplace(1/ε) noise.
    The result is ε-DP by the Laplace mechanism theorem.

    This is the first step of private mean estimation. -/
theorem private_sum_pureDP (f : α → ℝ) {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      (laplaceMech (clampedSum f 0 1) (1 : ℝ≥0) ε) ε :=
  laplaceMech_isPureDP hε (clampedSum01_sensitivity f)

-- ============================================================================
-- Example 2: Private mean via postprocessing
-- ============================================================================

/-- **Private mean estimation is ε-DP.**

    Pipeline: clamp values to [0,1] → sum → add Laplace(1/ε) → divide by n.
    The division step is measurable postprocessing, so privacy is preserved.

    This is the canonical private mean estimation algorithm from
    Dwork & Roth (2014), Section 3.5.2. -/
theorem private_mean_pureDP (f : α → ℝ) (n : ℕ) (_hn : (n : ℝ) ≠ 0) {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      (fun (d : List α) =>
        (laplaceMech (clampedSum f 0 1) (1 : ℝ≥0) ε d).map
          (measurable_const_mul (n : ℝ)⁻¹).aemeasurable)
      ε :=
  isPureDP_postprocess (private_sum_pureDP f hε) (measurable_const_mul (n : ℝ)⁻¹)

-- ============================================================================
-- Example 3: Private sum with larger bound
-- ============================================================================

/-- **Private sum with clamp [0, B] and sensitivity B.**

    Generalizes to arbitrary upper bound B > 0. The Laplace noise scale
    is B/ε, giving ε-DP. -/
theorem private_sum_general {B : NNReal} (_hB : B ≠ 0) (f : α → ℝ)
    {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      (laplaceMech (clampedSum f 0 (↑B)) B ε) ε := by
  apply laplaceMech_isPureDP hε
  exact clampedSum_sensitivity (NNReal.coe_nonneg B) f

end DPlean4.Examples

end -- noncomputable section
