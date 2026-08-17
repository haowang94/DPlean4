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
    HasL1Sensitivity ListAddRemove (fun (l : List α) => (l.length : ℝ)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj
  simp only [NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- A constant function has L1 sensitivity 0. -/
theorem const_sens (c : ℝ) :
    HasL1Sensitivity ListAddRemove (fun (_ : List α) => c) (↑(0 : ℝ≥0)) := by
  simp only [NNReal.coe_zero]
  exact constant_hasL1Sensitivity_zero ListAddRemove c

-- ============================================================================
-- Test 1: Basic Laplace mechanism — 1-DP for count query
-- ============================================================================

/-- The Laplace mechanism with Δ=1, ε=1 satisfies 1-DP for the count query. -/
theorem laplace_count_1dp :
    IsPureDP ListAddRemove
      (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0))
      (1 : ℝ≥0) :=
  laplaceMech_isPureDP one_ne_zero countQuery_sens

-- ============================================================================
-- Test 2: Constant query — Dirac degeneration
-- ============================================================================

/-- Constant query with ε gives ε-DP (mechanism is a Dirac mass at the constant). -/
theorem laplace_const_dp (c : ℝ) {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsPureDP ListAddRemove
      (laplaceMech (D := List α) (fun _ => c) (0 : ℝ≥0) ε) ε :=
  laplaceMech_isPureDP hε (const_sens c)

-- ============================================================================
-- Test 3: Pure DP → Approximate DP conversion
-- ============================================================================

/-- 1-DP implies (1, δ)-approximate DP for any δ. -/
theorem laplace_count_approx_dp (δ : NNReal) :
    IsApproxDP ListAddRemove
      (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0))
      (1 : ℝ≥0) δ :=
  isPureDP_to_isApproxDP δ laplace_count_1dp

-- ============================================================================
-- Test 4: Monotonicity — ε-DP implies ε'-DP for ε' ≥ ε
-- ============================================================================

/-- 1-DP implies 2-DP. -/
theorem laplace_count_relaxed :
    IsPureDP ListAddRemove
      (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0))
      (2 : ℝ≥0) :=
  isPureDP_mono laplace_count_1dp (by norm_num)

-- ============================================================================
-- Test 5: Composition
-- ============================================================================

/-- Two independent 1-DP mechanisms compose to 2-DP. -/
theorem laplace_compose_2dp :
    IsPureDP ListAddRemove
      (laplaceMech (D := List α) (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0))
      ((1 : ℝ≥0) + (1 : ℝ≥0)) :=
  isPureDP_compose_simple
    (laplace_count_1dp (α := α))
    (laplace_count_1dp (α := α))

-- ============================================================================
-- Test 6: Postprocessing
-- ============================================================================

/-- Clamping to nonneg preserves DP. -/
theorem laplace_postprocess :
    IsPureDP ListAddRemove
      (fun (d : List α) =>
        (laplaceMech (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0) d).map
          (measurable_const (a := (0 : ℝ)) |>.max measurable_id).aemeasurable)
      (1 : ℝ≥0) :=
  isPureDP_postprocess laplace_count_1dp
    (measurable_const (a := (0 : ℝ)) |>.max measurable_id)

-- ============================================================================
-- Test 7: Group privacy
-- ============================================================================

/-- 2-hop adjacency chain gives (1+1)-close bound. -/
theorem laplace_group_2hop {l₁ l₂ l₃ : List α}
    (h₁₂ : ListAddRemove l₁ l₂) (h₂₃ : ListAddRemove l₂ l₃) :
    PureMeasureClose ((1 : ℝ≥0) + (1 : ℝ≥0))
      (laplaceMech (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0) l₁)
      (laplaceMech (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0) l₃) :=
  isPureDP_group_2 laplace_count_1dp h₁₂ h₂₃

end DPlean4.Examples

end -- noncomputable section
