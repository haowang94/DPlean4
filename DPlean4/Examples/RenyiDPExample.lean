/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.RenyiDP
import DPlean4.Mechanism.Gaussian
import DPlean4.Mechanism.Laplace
import DPlean4.Basic.Adjacency
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Rényi DP Workflow Examples

This file demonstrates the Rényi DP (RDP) workflow:
1. Prove a mechanism satisfies (α, ε_α)-RDP
2. Compose mechanisms via RDP (linear addition of ε at each order)
3. Convert to (ε, δ)-DP by optimizing over α

## Key Advantages of RDP over Basic Composition

For k queries each with Gaussian noise variance v:
- **Basic composition**: (ε₁+...+εₖ, kδ)-DP (linear in k)
- **zCDP/RDP**: kρ-zCDP → (ε', δ)-DP with
  ε' = kρ + 2√(kρ·ln(1/δ))

The RDP framework tracks Rényi-divergence bounds at each order α > 1 and
optimizes the (ε, δ) conversion at the end.

## References

* Mironov (2017), "Rényi Differential Privacy"
* Mironov et al. (2019), "Rényi DP of the Sampled Gaussian Mechanism"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*}

-- ============================================================================
-- Gaussian mechanism satisfies RDP at each order
-- ============================================================================

private def countQ (l : List α) : ℝ := (l.length : ℝ)

private theorem countQ_sens :
    HasL1Sensitivity ListHeadAddRemove (countQ (α := α)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj; simp only [countQ, NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- **Gaussian mechanism is (α, ρα)-RDP at each order α > 1.**

    For counting query with Gaussian noise v=2: ρ = 1/(4), so at order α = 2
    the RDP bound is ρ·α = 1/2. At order α = 10 the bound is 10/4 = 2.5.

    The (ε, δ)-DP conversion optimizes over α, choosing the order that gives
    the tightest overall bound. This is the key idea behind practical RDP
    accountants (TensorFlow Privacy, Opacus). -/
theorem gaussian_count_isRenyiDP {a : ℝ} (ha : 1 < a) :
    IsRenyiDP ListHeadAddRemove
      (gaussianMech (D := List α) countQ (2 : ℝ≥0))
      a
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) * a) :=
  isRenyiDP_of_isZCDP
    (gaussianMech_isZCDP (by norm_num : (2 : ℝ≥0) ≠ 0) countQ_sens.toL2)
    ha

-- ============================================================================
-- RDP composition: two Gaussian queries
-- ============================================================================

private theorem gaussian_count_ac {v : ℝ≥0} (hv : v ≠ 0) :
    ∀ d₁ d₂ : List α, ListHeadAddRemove d₁ d₂ →
      (gaussianMech countQ v d₁).toMeasure ≪ (gaussianMech countQ v d₂).toMeasure := by
  intro d₁ d₂ _; simp only [gaussianMech_toMeasure]
  exact (gaussianReal_absolutelyContinuous _ hv).trans
    (gaussianReal_absolutelyContinuous' _ hv)

/-- **Two Gaussian queries compose under RDP**: at each order α, the RDP bound
    adds linearly: ε₁(α) + ε₂(α).

    This is the same as zCDP composition, but stated in the RDP framework to
    show how the accounting works order by order. -/
theorem two_gaussian_queries_isRenyiDP {a : ℝ} (ha : 1 < a) :
    IsRenyiDP ListHeadAddRemove
      ((gaussianMech (D := List α) countQ (2 : ℝ≥0)).prod
       (gaussianMech (D := List α) countQ (2 : ℝ≥0)))
      a
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) * a + (1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) * a) :=
  isRenyiDP_prod ha
    (gaussian_count_isRenyiDP ha)
    (gaussian_count_isRenyiDP ha)
    (gaussian_count_ac (by norm_num))
    (gaussian_count_ac (by norm_num))

-- ============================================================================
-- RDP postprocessing
-- ============================================================================

private theorem gaussian_count_fin (hv : (v : ℝ≥0) ≠ 0) :
    ∀ d₁ d₂ : List α, ListHeadAddRemove d₁ d₂ → ∀ a : ℝ, 1 < a →
      renyiMoment a (gaussianMech countQ v d₁).toMeasure
        (gaussianMech countQ v d₂).toMeasure ≠ ⊤ := by
  intro d₁ d₂ _ a ha; simp only [gaussianMech_toMeasure]
  rw [renyiMoment_gaussianReal_same_var hv ha]
  exact ENNReal.ofReal_ne_top

/-- Postprocessing a Gaussian query (e.g., rounding) preserves its RDP guarantee. -/
theorem gaussian_postprocess_isRenyiDP {a : ℝ} (ha : 1 < a) :
    IsRenyiDP ListHeadAddRemove
      (fun d => (gaussianMech (D := List α) countQ (2 : ℝ≥0) d).map
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℤ))).aemeasurable)
      a
      ((1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0)) * a) :=
  isRenyiDP_postprocess ha (gaussian_count_isRenyiDP ha)
    measurable_const
    (gaussian_count_ac (by norm_num))
    (fun d₁ d₂ hadj => gaussian_count_fin (by norm_num) d₁ d₂ hadj a ha)

-- ============================================================================
-- RDP → (ε, δ)-DP conversion via zCDP
-- ============================================================================

/-- **End-to-end RDP pipeline**: Two Gaussian counting queries compose to
    (1/2)-zCDP, which converts to (ε, δ)-DP for any δ ∈ (0, 1).

    This shows the full workflow:
    1. Each query is (α, α/4)-RDP (equivalently, (1/4)-zCDP)
    2. Two queries compose to (α, α/2)-RDP (equivalently, (1/2)-zCDP)
    3. Convert to (ε, δ)-DP with ε ≈ 1/2 + √(ln(1/δ))

    The RDP/zCDP framework gives the same result here because both queries
    use the same Gaussian mechanism. In general, RDP is more flexible when
    different mechanisms have different Rényi profiles. -/
theorem two_gaussian_queries_approxDP {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) :
    ∃ ε : NNReal, IsApproxDP ListHeadAddRemove
      ((gaussianMech (D := List α) countQ (2 : ℝ≥0)).prod
       (gaussianMech (D := List α) countQ (2 : ℝ≥0)))
      ε δ := by
  have hv : (2 : ℝ≥0) ≠ 0 := by norm_num
  exact isApproxDP_of_isZCDP'
    (isZCDP_prod
      (gaussianMech_isZCDP hv countQ_sens.toL2)
      (gaussianMech_isZCDP hv countQ_sens.toL2))
    (by positivity) hδ hδ1

-- ============================================================================
-- Pure DP → zCDP conversion
-- ============================================================================

/-- **Pure DP implies zCDP**: a 1-DP Laplace mechanism is also 1-zCDP.
    This uses the change-of-measure bound: D_α(P‖Q) ≤ ε for all α > 1,
    which gives ε-zCDP since ε ≤ ε·α for α > 1.

    This is weaker than the optimal (ε²/2)-zCDP bound from Hoeffding's lemma
    but is correct and already useful for connecting pure DP to the zCDP/RDP
    framework. -/
theorem laplace_count_isZCDP
    (hac : ∀ d₁ d₂ : List α, ListHeadAddRemove d₁ d₂ →
      (laplaceMech countQ 1 (1 : ℝ≥0) d₁).toMeasure ≪
      (laplaceMech countQ 1 (1 : ℝ≥0) d₂).toMeasure)
    (hfin : ∀ d₁ d₂ : List α, ListHeadAddRemove d₁ d₂ → ∀ a : ℝ, 1 < a →
      renyiMoment a (laplaceMech countQ 1 (1 : ℝ≥0) d₁).toMeasure
        (laplaceMech countQ 1 (1 : ℝ≥0) d₂).toMeasure ≠ ⊤) :
    IsZCDP ListHeadAddRemove
      (laplaceMech (D := List α) countQ 1 (1 : ℝ≥0))
      (1 : ℝ≥0) :=
  isZCDP_of_isPureDP
    (laplaceMech_isPureDP (by norm_num) countQ_sens)
    hac hfin

end DPlean4.Examples

end -- noncomputable section
