/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Approximate
import DPlean4.Distribution.Laplace

/-!
# Counterexample: Noise Reuse Breaks Differential Privacy

This file demonstrates that **reusing the same noise** for multiple queries
breaks differential privacy, even when each individual noisy answer would
satisfy ε-DP.

## The Bug

A common implementation error: draw a single noise sample η and use it for
multiple queries. For queries q₁(d) = d and q₂(d) = -d:

  M(d) = (d + η, -d + η)

Each coordinate is marginally ε-DP (just Laplace noise), but the joint
output reveals d exactly via (output₁ - output₂)/2 = d.

## Formal Proof

For d₁ = 1, d₂ = 0, the event S = {(x,y) : x - y > 3/2}:
- M(1)(S) = P(2 > 3/2) = 1    (difference is always 2d₁ = 2)
- M(0)(S) = P(0 > 3/2) = 0    (difference is always 2d₂ = 0)

So P(S|d₁) = 1 > exp(ε)·0 = P(S|d₂), violating DP for any ε.

## Significance

This formalizes the folklore result that noise reuse is unsafe.
The correct approach is independent noise per query (as in `isPureDP_prod`),
giving (ε₁+ε₂)-DP via composition. Our product composition theorem
guarantees this because `Mechanism.prod` draws independent samples.

## References

* Dwork & Roth (2014), §3.5: "each invocation of a [mechanism] must use
  its own, freshly generated random bits"
-/

noncomputable section

namespace DPlean4

open MeasureTheory
open scoped NNReal ENNReal

-- ============================================================================
-- The Noise-Reuse Mechanism
-- ============================================================================

/-- The noise-reuse map: given database value d ∈ ℝ, maps noise η to (d+η, -d+η).
    This "answers" q₁(d) = d and q₂(d) = -d using the SAME noise η. -/
private def noiseReuseMap (d : ℝ) : ℝ → ℝ × ℝ :=
  fun η => (d + η, -d + η)

private theorem measurable_noiseReuseMap (d : ℝ) : Measurable (noiseReuseMap d) := by
  apply Measurable.prod
  · exact measurable_const.add measurable_id
  · exact measurable_const.add measurable_id

/-- The noise-reuse mechanism: draw one Laplace noise sample and use it for both
    queries q₁(d) = d and q₂(d) = -d. -/
private def noiseReuseMech (b : NNReal) : Mechanism ℝ (ℝ × ℝ) :=
  fun d => ProbabilityMeasure.map
    (⟨laplaceMeasure 0 b, inferInstance⟩ : ProbabilityMeasure ℝ)
    (measurable_noiseReuseMap d).aemeasurable

/-- All pairs are adjacent (worst-case adjacency for ℝ databases). -/
private def RealAllAdj : ℝ → ℝ → Prop := fun _ _ => True

-- ============================================================================
-- The Discriminating Event
-- ============================================================================

/-- The event S = {(x, y) : x - y > 3/2}. Under noise reuse:
    x - y = (d + η) - (-d + η) = 2d, which is deterministic.
    So d=1 gives x-y=2 (always in S), and d=0 gives x-y=0 (never in S). -/
private def discriminatingEvent : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 - p.2 > 3/2}

private theorem measurableSet_discriminatingEvent : MeasurableSet discriminatingEvent := by
  apply measurableSet_lt measurable_const
  exact (measurable_fst.sub measurable_snd)

-- ============================================================================
-- Preimage computations
-- ============================================================================

/-- Under d=1: the preimage of S is all of ℝ (since 2·1 = 2 > 3/2 always). -/
private lemma noiseReuse_d1_preimage :
    noiseReuseMap 1 ⁻¹' discriminatingEvent = Set.univ := by
  ext η
  simp only [Set.mem_preimage, noiseReuseMap, discriminatingEvent, Set.mem_setOf_eq,
             Set.mem_univ, iff_true]
  linarith

/-- Under d=0: the preimage of S is empty (since 2·0 = 0 < 3/2 always). -/
private lemma noiseReuse_d0_preimage :
    noiseReuseMap 0 ⁻¹' discriminatingEvent = ∅ := by
  ext η
  simp only [Set.mem_preimage, noiseReuseMap, discriminatingEvent, Set.mem_setOf_eq,
             Set.mem_empty_iff_false, iff_false, not_lt]
  linarith

private lemma noiseReuseMech_toMeasure (b : NNReal) (d : ℝ) :
    (noiseReuseMech b d).toMeasure = Measure.map (noiseReuseMap d) (laplaceMeasure 0 b) := by
  exact ProbabilityMeasure.toMeasure_map _ _

-- ============================================================================
-- Main Theorem
-- ============================================================================

/-- **Noise reuse is NOT ε-DP for any ε.**

    The mechanism that reuses Laplace noise for queries d and -d reveals the
    database value deterministically through the output difference.
    This counterexample formalizes why each mechanism invocation must use
    independent noise (Dwork & Roth 2014, §3.5). -/
theorem noiseReuse_not_pureDP {b : NNReal} (hb : b ≠ 0) (ε : NNReal) :
    ¬ IsPureDP RealAllAdj (noiseReuseMech b) ε := by
  intro h
  have hS := measurableSet_discriminatingEvent
  have h_dp := h 1 0 trivial discriminatingEvent hS
  -- M(0)(S) = 0: preimage is empty
  have h_d0_zero : (noiseReuseMech b 0).toMeasure discriminatingEvent = 0 := by
    rw [noiseReuseMech_toMeasure,
        Measure.map_apply (measurable_noiseReuseMap 0) hS,
        noiseReuse_d0_preimage, measure_empty]
  -- M(1)(S) = 1: preimage is univ
  have h_d1_one : (noiseReuseMech b 1).toMeasure discriminatingEvent = 1 := by
    rw [noiseReuseMech_toMeasure,
        Measure.map_apply (measurable_noiseReuseMap 1) hS,
        noiseReuse_d1_preimage, measure_univ]
  rw [h_d0_zero, mul_zero, ENNReal.coe_zero, add_zero] at h_dp
  rw [h_d1_one] at h_dp
  exact absurd h_dp (by simp)

/-- **Noise reuse is NOT (ε, δ)-DP for any ε and δ < 1.**

    Even approximate DP fails: the mechanism produces a probability-1 event
    under one database that has probability 0 under the other, so δ ≥ 1
    would be required. -/
theorem noiseReuse_not_approxDP {b : NNReal} (hb : b ≠ 0) (ε : NNReal)
    {δ : NNReal} (hδ : (δ : ℝ) < 1) :
    ¬ IsApproxDP RealAllAdj (noiseReuseMech b) ε δ := by
  intro h
  have hS := measurableSet_discriminatingEvent
  have h_dp := h 1 0 trivial discriminatingEvent hS
  have h_d0_zero : (noiseReuseMech b 0).toMeasure discriminatingEvent = 0 := by
    rw [noiseReuseMech_toMeasure,
        Measure.map_apply (measurable_noiseReuseMap 0) hS,
        noiseReuse_d0_preimage, measure_empty]
  have h_d1_one : (noiseReuseMech b 1).toMeasure discriminatingEvent = 1 := by
    rw [noiseReuseMech_toMeasure,
        Measure.map_apply (measurable_noiseReuseMap 1) hS,
        noiseReuse_d1_preimage, measure_univ]
  rw [h_d0_zero, mul_zero, zero_add] at h_dp
  rw [h_d1_one] at h_dp
  have h4 : (δ : ENNReal) < 1 := by
    rw [ENNReal.coe_lt_one_iff]; exact_mod_cast hδ
  exact absurd (le_trans h_dp (le_refl _)) (not_le.mpr h4)

end DPlean4

end -- noncomputable section
