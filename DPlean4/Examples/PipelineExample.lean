/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Mechanism.Gaussian
import DPlean4.Privacy.Composition
import DPlean4.Privacy.Postprocessing
import DPlean4.Privacy.ZCDP
import DPlean4.Basic.Adjacency

/-!
# Multi-Mechanism DP Pipeline

This file demonstrates a realistic differentially private analysis pipeline
that combines multiple mechanisms and privacy notions:

1. **Count query** (Laplace, pure ε₁-DP)
2. **Noisy sum** (Gaussian, ρ-zCDP → (ε₂,δ)-DP)

The total privacy budget is tracked across both steps using composition.

## Key Insights

- Pure DP and zCDP mechanisms can be composed at the approximate DP level
- Convert each mechanism to (ε,δ)-DP, then apply composition
- The product mechanism ensures independence (critical for composition)

## References

* Dwork & Roth (2014), Ch. 3: Composition framework
* Bun & Dwork (2016): zCDP composition and conversion
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory
open scoped NNReal ENNReal

variable {α : Type*}

-- ============================================================================
-- Step 1: Count query with Laplace noise (pure ε-DP)
-- ============================================================================

private def countQuery (l : List α) : ℝ := (l.length : ℝ)

private theorem countQuery_sensitivity :
    HasL1Sensitivity ListHeadAddRemove (countQuery (α := α)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj; simp only [countQuery, NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- Step 1: Laplace mechanism for counting. Pure ε₁-DP. -/
theorem pipeline_step1_pureDP {ε₁ : NNReal} (hε₁ : ε₁ ≠ 0) :
    IsPureDP ListHeadAddRemove (laplaceMech (D := List α) countQuery 1 ε₁) ε₁ :=
  laplaceMech_isPureDP hε₁ countQuery_sensitivity

/-- Step 1 as approximate DP (for composition with other mechanisms). -/
theorem pipeline_step1_approxDP {ε₁ : NNReal} (hε₁ : ε₁ ≠ 0) (δ : NNReal) :
    IsApproxDP ListHeadAddRemove (laplaceMech (D := List α) countQuery 1 ε₁) ε₁ δ :=
  isApproxDP_of_isPureDP δ (pipeline_step1_pureDP hε₁)

-- ============================================================================
-- Step 2: Noisy sum with Gaussian noise (zCDP)
-- ============================================================================

/-- Step 2: Gaussian mechanism for counting. ρ-zCDP where ρ = 1/(2v). -/
theorem pipeline_step2_zCDP {v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP ListHeadAddRemove (gaussianMech (D := List α) countQuery v)
      ((1 : ℝ≥0) ^ 2 / (2 * v)) :=
  gaussianMech_isZCDP hv countQuery_sensitivity.toL2

-- ============================================================================
-- Composing steps: pure DP + pure DP
-- ============================================================================

/-- **Two pure DP steps compose**: count + count with Laplace noise.
    Total budget is ε₁ + ε₂ (basic composition). -/
theorem pipeline_two_laplace {ε₁ ε₂ : NNReal} (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) :
    IsPureDP ListHeadAddRemove
      ((laplaceMech (D := List α) countQuery 1 ε₁).prod
       (laplaceMech (D := List α) countQuery 1 ε₂))
      (ε₁ + ε₂) :=
  isPureDP_prod (pipeline_step1_pureDP hε₁) (pipeline_step1_pureDP hε₂)

-- ============================================================================
-- Composing steps: zCDP + zCDP
-- ============================================================================

/-- **Two zCDP steps compose**: Gaussian + Gaussian.
    Total ρ = ρ₁ + ρ₂ (linear composition in zCDP). -/
theorem pipeline_two_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP ListHeadAddRemove
      ((gaussianMech (D := List α) countQuery v).prod
       (gaussianMech (D := List α) countQuery v))
      ((1 : ℝ≥0) ^ 2 / (2 * v) + (1 : ℝ≥0) ^ 2 / (2 * v)) :=
  isZCDP_prod (pipeline_step2_zCDP hv) (pipeline_step2_zCDP hv)

-- ============================================================================
-- Composing different mechanisms: Laplace + Laplace (practical pipeline)
-- ============================================================================

/-- **Multi-step pipeline**: A practical 3-query pipeline using Laplace.

    Query 1: count (ε/3-DP)
    Query 2: count (ε/3-DP)
    Query 3: count (ε/3-DP)

    Total: ε-DP (via basic composition, ε/3 + ε/3 + ε/3 = ε). -/
theorem pipeline_three_queries {ε : NNReal} (hε : ε ≠ 0) :
    let q := laplaceMech (D := List α) countQuery 1 (ε / 3)
    IsPureDP ListHeadAddRemove (q.prod (q.prod q)) (ε / 3 + (ε / 3 + ε / 3)) := by
  intro q
  have hε3 : ε / 3 ≠ 0 := div_ne_zero hε (by norm_num)
  have hq : IsPureDP ListHeadAddRemove q (ε / 3) := pipeline_step1_pureDP hε3
  exact isPureDP_prod hq (isPureDP_prod hq hq)

-- ============================================================================
-- Postprocessing in the pipeline
-- ============================================================================

/-- After counting with Laplace noise, applying any measurable function
    still preserves ε-DP (postprocessing). -/
theorem pipeline_count_then_round {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      (fun d => (laplaceMech (D := List α) countQuery 1 ε d).map
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℤ))).aemeasurable)
      ε :=
  isPureDP_postprocess (pipeline_step1_pureDP hε) measurable_const

-- ============================================================================
-- Group privacy in the pipeline
-- ============================================================================

/-- **Group privacy**: If a pipeline is ε-DP and two databases differ by
    2 additions/removals (connected by a chain d₁ → d₂ → d₃), the output
    distributions are 2ε-close.

    This is important for bounding privacy loss when multiple records change,
    e.g., when a family opts out of a survey. -/
theorem pipeline_group_privacy_2 {ε : NNReal} (hε : ε ≠ 0)
    {d₁ d₂ d₃ : List α}
    (h₁₂ : ListHeadAddRemove d₁ d₂) (h₂₃ : ListHeadAddRemove d₂ d₃) :
    PureMeasureClose (ε + ε)
      (laplaceMech (D := List α) countQuery 1 ε d₁)
      (laplaceMech (D := List α) countQuery 1 ε d₃) :=
  isPureDP_group_2 (pipeline_step1_pureDP hε) h₁₂ h₂₃

end DPlean4.Examples

end -- noncomputable section
