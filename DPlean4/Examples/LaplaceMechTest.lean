/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Postprocessing
import DPlean4.Privacy.Composition
import DPlean4.Privacy.Approximate
import DPlean4.Basic.Adjacency

/-!
# End-to-End Tests for the Laplace Mechanism

This file exercises the full library pipeline:
1. Define concrete queries with sensitivity proofs
2. Instantiate the Laplace mechanism
3. Verify ε-DP bounds
4. Test postprocessing and composition integration
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open scoped NNReal ENNReal

variable {α : Type*}

-- ============================================================================
-- Sensitivity proofs
-- ============================================================================

/-- The counting query `|l|` has L1 sensitivity 1 under add/remove,
    stated directly in the NNReal coercion form needed by `laplaceMech_isPureDP`. -/
theorem countQuery_sens :
    HasL1Sensitivity ListHeadAddRemove (fun (l : List α) => (l.length : ℝ)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj
  simp only [NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- A constant function has L1 sensitivity 0. -/
theorem const_sens (c : ℝ) :
    HasL1Sensitivity ListHeadAddRemove (fun (_ : List α) => c) 0 :=
  constant_hasL1Sensitivity_zero ListHeadAddRemove c

-- ============================================================================
-- Test 1: Basic Laplace mechanism — 1-DP for count query
-- ============================================================================

/-- The Laplace mechanism with Δ=1, ε=1 satisfies 1-DP for the count query. -/
theorem laplace_count_1dp :
    IsPureDP ListHeadAddRemove
      (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0))
      (1 : ℝ≥0) :=
  laplaceMech_isPureDP one_ne_zero countQuery_sens

-- ============================================================================
-- Test 2: Constant query — Dirac degeneration
-- ============================================================================

/-- Constant query with ε gives ε-DP (mechanism is a Dirac mass at the constant). -/
theorem laplace_const_dp (c : ℝ) {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsPureDP ListHeadAddRemove
      (laplaceMech (D := List α) (fun _ => c) (0 : ℝ≥0) ε) ε :=
  laplaceMech_isPureDP hε (const_sens c)

-- ============================================================================
-- Test 3: Pure DP → Approximate DP conversion
-- ============================================================================

/-- 1-DP implies (1, δ)-approximate DP for any δ. -/
theorem laplace_count_approx_dp (δ : NNReal) :
    IsApproxDP ListHeadAddRemove
      (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0))
      (1 : ℝ≥0) δ :=
  isApproxDP_of_isPureDP δ laplace_count_1dp

-- ============================================================================
-- Test 4: Monotonicity — ε-DP implies ε'-DP for ε' ≥ ε
-- ============================================================================

/-- 1-DP implies 2-DP. -/
theorem laplace_count_relaxed :
    IsPureDP ListHeadAddRemove
      (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0))
      (2 : ℝ≥0) :=
  isPureDP_mono laplace_count_1dp (by norm_num)

-- ============================================================================
-- Test 5: Composition
-- ============================================================================

/-- Two independent 1-DP Laplace mechanisms compose to a 2-DP product mechanism.
    This is genuine composition: the result is about the joint mechanism `(M₁, M₂)`,
    not a monotonicity relaxation of a single mechanism. -/
theorem laplace_compose_product :
    IsPureDP ListHeadAddRemove
      ((laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0)).prod
       (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0)))
      ((1 : ℝ≥0) + (1 : ℝ≥0)) :=
  isPureDP_prod
    (laplace_count_1dp (α := α))
    (laplace_count_1dp (α := α))

-- ============================================================================
-- Test 6: Approximate DP product composition
-- ============================================================================

/-- Two independent (1,δ)-DP Laplace mechanisms compose to (2, exp(1)·δ+δ)-DP.
    Exercises the new `isApproxDP_prod` theorem. -/
theorem laplace_compose_approxDP (δ : NNReal) :
    IsApproxDP ListHeadAddRemove
      ((laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0)).prod
       (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0)))
      ((1 : ℝ≥0) + (1 : ℝ≥0))
      (⟨Real.exp ↑(1 : ℝ≥0), Real.exp_nonneg _⟩ * δ + δ) :=
  isApproxDP_prod
    (laplace_count_approx_dp (α := α) δ)
    (laplace_count_approx_dp (α := α) δ)

-- ============================================================================
-- Test 7: Postprocessing
-- ============================================================================

/-- Clamping to nonneg preserves DP. -/
theorem laplace_postprocess :
    IsPureDP ListHeadAddRemove
      (fun (d : List α) =>
        (laplaceMech (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0) d).map
          (measurable_const (a := (0 : ℝ)) |>.max measurable_id).aemeasurable)
      (1 : ℝ≥0) :=
  isPureDP_postprocess laplace_count_1dp
    (measurable_const (a := (0 : ℝ)) |>.max measurable_id)

-- ============================================================================
-- Test 8: Group privacy
-- ============================================================================

/-- 2-hop adjacency chain gives (1+1)-close bound. -/
theorem laplace_group_2hop {l₁ l₂ l₃ : List α}
    (h₁₂ : ListHeadAddRemove l₁ l₂) (h₂₃ : ListHeadAddRemove l₂ l₃) :
    PureMeasureClose ((1 : ℝ≥0) + (1 : ℝ≥0))
      (laplaceMech (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0) l₁)
      (laplaceMech (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0) l₃) :=
  isPureDP_group_2 laplace_count_1dp h₁₂ h₂₃

end DPlean4.Examples

end -- noncomputable section
