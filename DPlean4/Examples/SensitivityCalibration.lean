/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Mechanism.Gaussian
import DPlean4.Privacy.Composition
import DPlean4.Privacy.ZCDP
import DPlean4.Basic.Adjacency
import DPlean4.Basic.Sensitivity

/-!
# Sensitivity Calibration: Fundamental DP Principle

This file demonstrates the fundamental principle that **noise scale must be
calibrated to query sensitivity** for differential privacy.

## Key Points

1. **Higher sensitivity → more noise**: A query with sensitivity Δ needs noise
   proportional to Δ to achieve ε-DP.

2. **Sensitivity reduction via clamping**: Clamping query outputs to [lo, hi]
   bounds the sensitivity, enabling DP with bounded noise.

3. **The sensitivity toolkit**: Combining queries (add, sub, max, min, Lipschitz
   postprocessing) has predictable sensitivity, enabling modular DP design.

## Examples

* Counting query: Δ = 1 (one record changes count by at most 1)
* Sum query with clamp: Δ = B (clamped to [0, B])
* Difference of queries: Δ = Δ₁ + Δ₂ (triangle inequality)
* Negation: Δ unchanged (sensitivity is symmetric)
* Max/min of queries: Δ = max(Δ₁, Δ₂)

## References

* Dwork & Roth (2014), §3.3: "Calibrating Noise to Sensitivity"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory
open scoped NNReal

variable {α : Type*}

-- ============================================================================
-- Basic sensitivity examples
-- ============================================================================

/-- Counting query: sensitivity 1 under add/remove adjacency. -/
private def count (l : List α) : ℝ := (l.length : ℝ)

private theorem count_sens :
    HasL1Sensitivity ListAddRemove (count (α := α)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj; simp only [count, NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- **Noise calibration for counting**: sensitivity 1, so Laplace(1/ε) gives ε-DP. -/
theorem counting_dp {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListAddRemove (laplaceMech (D := List α) count 1 ε) ε :=
  laplaceMech_isPureDP hε count_sens

-- ============================================================================
-- Sensitivity composition via the toolkit
-- ============================================================================

/-- Query q₁(l) = l.length (count of all items). -/
private def q₁ (l : List ℕ) : ℝ := (l.length : ℝ)
/-- Query q₂(l) = (l.filter (· > 5)).length (count of items > 5). -/
private def q₂ (l : List ℕ) : ℝ := ((l.filter (· > 5)).length : ℝ)

private theorem q₁_sens : HasL1Sensitivity ListAddRemove q₁ 1 := by
  intro l₁ l₂ hadj; simp only [q₁]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

private theorem q₂_sens : HasL1Sensitivity ListAddRemove q₂ 1 := by
  intro l₁ l₂ hadj; simp only [q₂]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, List.filter_cons]
    split <;> simp [Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, List.filter_cons]
    split <;> simp [Nat.cast_add, Nat.cast_one]

/-- **Negation preserves sensitivity**: if q has sensitivity Δ,
    then -q also has sensitivity Δ. -/
theorem negation_sensitivity_example :
    HasL1Sensitivity ListAddRemove (fun l => -q₁ l) 1 :=
  hasL1Sensitivity_neg ListAddRemove q₁ 1 q₁_sens

/-- **Subtraction has additive sensitivity**: if q₁ has sensitivity Δ₁ and
    q₂ has sensitivity Δ₂, then q₁ - q₂ has sensitivity Δ₁ + Δ₂.

    Here: count_all - count_above_5 has sensitivity 1 + 1 = 2.
    (This equals count_below_or_equal_5, which also has sensitivity 1,
    so the triangle inequality bound is not always tight.) -/
theorem subtraction_sensitivity_example :
    HasL1Sensitivity ListAddRemove (fun l => q₁ l - q₂ l) (1 + 1) :=
  hasL1Sensitivity_sub ListAddRemove q₁ q₂ 1 1 q₁_sens q₂_sens

/-- **Max of queries has max sensitivity**. -/
theorem max_sensitivity_example :
    HasL1Sensitivity ListAddRemove (fun l => max (q₁ l) (q₂ l)) (max 1 1) :=
  hasL1Sensitivity_max ListAddRemove q₁ q₂ 1 1 q₁_sens q₂_sens (by norm_num) (by norm_num)

-- ============================================================================
-- Calibrating noise to sensitivity
-- ============================================================================

/-- **Sensitivity determines noise**: the Laplace mechanism requires scale
    proportional to Δ. Here, the difference query has Δ=2, so it needs
    twice the noise of a count query to achieve the same ε-DP.

    This is formalized via `laplaceMech_isPureDP`, which requires the
    sensitivity bound as a hypothesis. -/
theorem higher_sensitivity_more_noise {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP ListAddRemove
      (laplaceMech (D := List ℕ) (fun l => q₁ l - q₂ l) (1 + 1) ε) ε :=
  laplaceMech_isPureDP hε (subtraction_sensitivity_example)

/-- **Two independent count queries** compose with additive privacy cost.
    Each uses Laplace with Δ=1, and the composition is (ε₁+ε₂)-DP. -/
theorem two_queries_independent {ε₁ ε₂ : NNReal} (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) :
    IsPureDP ListAddRemove
      ((laplaceMech (D := List ℕ) q₁ 1 ε₁).prod (laplaceMech (D := List ℕ) q₂ 1 ε₂))
      (ε₁ + ε₂) :=
  isPureDP_prod (laplaceMech_isPureDP hε₁ q₁_sens) (laplaceMech_isPureDP hε₂ q₂_sens)

-- ============================================================================
-- Gaussian calibration via zCDP
-- ============================================================================

/-- **Gaussian noise calibration**: with sensitivity 1 and variance v,
    the Gaussian mechanism is (1/(2v))-zCDP.

    Doubling the variance halves the privacy cost ρ.
    For (ε, δ)-DP, the conversion gives ε ≈ 1/(2v) + √(ln(1/δ)/v). -/
theorem gaussian_calibration {v : ℝ≥0} (hv : v ≠ 0) :
    IsZCDP ListAddRemove (gaussianMech (D := List α) count v)
      ((1 : ℝ≥0) ^ 2 / (2 * v)) :=
  gaussianMech_isZCDP hv count_sens

end DPlean4.Examples

end -- noncomputable section
