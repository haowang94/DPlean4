/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Gaussian
import DPlean4.Basic.Adjacency

/-!
# End-to-End Tests for the Gaussian Mechanism

This file exercises the full Gaussian mechanism pipeline:
1. zCDP proof via Rényi divergence closed form
2. zCDP composition (linear budget)
3. zCDP → (ε,δ)-approximate DP conversion
4. Existence of (ε,δ)-DP parameters

These tests verify that Milestone 4 (Gaussian + zCDP) works end-to-end.
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*}

-- ============================================================================
-- Sensitivity
-- ============================================================================

private theorem countQuery_sens :
    HasL1Sensitivity ListAddRemove (fun (l : List α) => (l.length : ℝ)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj
  simp only [NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj <;> rw [h.1, h.2] <;>
    simp [List.length_cons, Nat.cast_add, Nat.cast_one]

-- ============================================================================
-- Test 1: Gaussian mechanism is zCDP
-- ============================================================================

/-- Counting query + Gaussian noise (v=2) satisfies (1/4)-zCDP.
    ρ = Δ²/(2v) = 1²/(2·2) = 1/4. -/
theorem gaussian_count_zcdp :
    IsZCDP ListAddRemove
      (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0))
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) :=
  gaussianMech_isZCDP (by norm_num : (2 : ℝ≥0) ≠ 0) countQuery_sens

-- ============================================================================
-- Test 2: zCDP composition (two independent Gaussian queries)
-- ============================================================================

/-- Two independent count queries with Gaussian noise (v=2) compose to (1/2)-zCDP.
    Demonstrates the power of zCDP composition: ρ₁ + ρ₂ = 1/4 + 1/4 = 1/2. -/
theorem gaussian_count_compose_zcdp :
    IsZCDP ListAddRemove
      ((gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)).prod
       (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)))
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) + (1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) := by
  have hv : (2 : ℝ≥0) ≠ 0 := by norm_num
  apply isZCDP_prod (gaussian_count_zcdp (α := α)) (gaussian_count_zcdp (α := α)) <;>
  · intro d₁ d₂ _; simp only [gaussianMech_toMeasure]
    exact (gaussianReal_absolutelyContinuous _ hv).trans
      (gaussianReal_absolutelyContinuous' _ hv)

-- ============================================================================
-- Test 3: zCDP → (ε,δ)-DP conversion (existential form)
-- ============================================================================

/-- For any δ ∈ (0,1), there exists ε such that the Gaussian counting mechanism
    satisfies (ε,δ)-approximate DP. This is the zCDP → approx DP conversion. -/
theorem gaussian_count_exists_approxDP {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) :
    ∃ ε : NNReal, IsApproxDP ListAddRemove
      (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)) ε δ := by
  have hv : (2 : ℝ≥0) ≠ 0 := by norm_num
  apply isZCDP_to_isApproxDP' (gaussian_count_zcdp (α := α)) (by positivity)
  · intro d₁ d₂ _; simp only [gaussianMech_toMeasure]
    exact (gaussianReal_absolutelyContinuous _ hv).trans
      (gaussianReal_absolutelyContinuous' _ hv)
  · intro d₁ d₂ _ α hα; simp only [gaussianMech_toMeasure]
    rw [renyiMoment_gaussianReal_same_var hv hα]
    exact ENNReal.ofReal_ne_top
  · exact hδ
  · exact hδ1

-- ============================================================================
-- Test 4: For any ε > ρ, there exists δ giving (ε,δ)-DP
-- ============================================================================

/-- For any ε > 1/4 (= ρ), there exists δ such that the Gaussian counting mechanism
    satisfies (ε,δ)-approximate DP. The δ decreases exponentially as ε grows. -/
theorem gaussian_count_any_eps {ε : NNReal}
    (hε : (ε : ℝ) > ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) : ℝ≥0)) :
    ∃ δ : NNReal, IsApproxDP ListAddRemove
      (gaussianMech (D := List α) (fun l => (l.length : ℝ)) (2 : ℝ≥0)) ε δ := by
  have hv : (2 : ℝ≥0) ≠ 0 := by norm_num
  refine isZCDP_to_isPureDP_trivial (gaussian_count_zcdp (α := α)) (by positivity) ?_ ?_ ε hε
  · intro d₁ d₂ _; simp only [gaussianMech_toMeasure]
    exact (gaussianReal_absolutelyContinuous _ hv).trans
      (gaussianReal_absolutelyContinuous' _ hv)
  · intro d₁ d₂ _ α hα; simp only [gaussianMech_toMeasure]
    rw [renyiMoment_gaussianReal_same_var hv hα]
    exact ENNReal.ofReal_ne_top

-- ============================================================================
-- Test 5: zCDP postprocessing
-- ============================================================================

/-- Postprocessing a Gaussian mechanism (e.g., rounding) preserves zCDP. -/
theorem gaussian_count_postprocess_zcdp :
    IsZCDP ListAddRemove
      (fun (d : List α) =>
        (gaussianMech (fun l => (l.length : ℝ)) (2 : ℝ≥0) d).map
          (measurable_const (a := (0 : ℝ)) |>.max measurable_id).aemeasurable)
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))) := by
  have hv : (2 : ℝ≥0) ≠ 0 := by norm_num
  apply isZCDP_postprocess (gaussian_count_zcdp (α := α))
    (measurable_const (a := (0 : ℝ)) |>.max measurable_id)
  · intro d₁ d₂ _; simp only [gaussianMech_toMeasure]
    exact (gaussianReal_absolutelyContinuous _ hv).trans
      (gaussianReal_absolutelyContinuous' _ hv)
  · intro d₁ d₂ _ α hα; simp only [gaussianMech_toMeasure]
    rw [renyiMoment_gaussianReal_same_var hv hα]
    exact ENNReal.ofReal_ne_top

end DPlean4.Examples

end -- noncomputable section
