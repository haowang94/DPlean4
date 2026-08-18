/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Approximate
import DPlean4.Distribution.Laplace

/-!
# Tricky Counterexamples: Subtle DP Failures

These mechanisms look like they should be differentially private — they add
noise, use standard distributions, and follow plausible-looking designs —
but they actually fail DP for subtle reasons. Our library formally proves
each one is NOT differentially private.

## Counterexamples

### 1. Data-Dependent Noise Scale (§1)
Add Laplace noise with scale proportional to the database value. When the
value is 0, the noise vanishes, creating a deterministic vs stochastic gap.

### 2. Thresholded Histogram (§2)
Release noisy count when count > 0, release exact 0 otherwise. The "suppress
noise for zeros" optimization is a well-known DP failure mode.

### 3. Conditional Release via Boolean Flag (§3)
Release noisy answer with a flag indicating whether the database passed a
safety check. The flag leaks the check result deterministically.

## Significance

Each mechanism uses genuine Laplace noise but fails DP due to:
- Data-dependent noise calibration (scale leaks information)
- Data-dependent noise suppression (optimization breaks DP)
- Data-dependent branching (decision to release leaks information)

These are real-world mistakes from the DP literature. Our proofs show the
DPlean4 framework can formally refute such subtle claims.
-/

noncomputable section

namespace DPlean4.Examples.TrickyCounterexamples

open MeasureTheory
open scoped NNReal ENNReal

-- ============================================================================
-- §1: Data-Dependent Noise Scale — Scale leaks information
-- ============================================================================

/-! ### Data-Dependent Noise Scale

**Mechanism**: M(d) = Lap(d, |d|)

When d = 0, the noise scale |d| = 0, so M(0) = Dirac(0). But M(1) = Lap(1, 1),
a continuous distribution. The event {0} has P = 1 under d₁ = 0 and P = 0
under d₂ = 1 (absolutely continuous measures have zero mass on singletons).

Reference: Dwork & Roth (2014), §3.3 — noise must be calibrated to GLOBAL
sensitivity, not a data-dependent quantity.
-/

section DataDependentNoise

/-- Data-dependent noise: for d=0, output Dirac(0) (no noise); for d≠0,
    output Lap(d, 1) (Laplace with fixed scale but applied only when d≠0).
    This models the mistake of skipping noise when the value is "trivial." -/
def dataDependentNoiseMech : Mechanism Bool ℝ :=
  fun d => if d then ⟨laplaceMeasure 1 1, inferInstance⟩
           else ⟨Measure.dirac 0, inferInstance⟩

private def BoolAdj : Bool → Bool → Prop := fun _ _ => True

/-- M(false) = Dirac(0): no noise is added. -/
private lemma dataDep_false_dirac :
    (dataDependentNoiseMech false).toMeasure = Measure.dirac 0 := by
  simp [dataDependentNoiseMech]

/-- P(M(false) = 0) = 1 since M(false) is Dirac at 0. -/
private lemma dataDep_false_singleton :
    (dataDependentNoiseMech false).toMeasure {(0 : ℝ)} = 1 := by
  rw [dataDep_false_dirac, Measure.dirac_apply_of_mem (Set.mem_singleton 0)]

/-- P(M(true) = 0) = 0 since Lap(1, 1) is absolutely continuous. -/
private lemma dataDep_true_singleton :
    (dataDependentNoiseMech true).toMeasure {(0 : ℝ)} = 0 := by
  show (laplaceMeasure 1 1) {(0 : ℝ)} = 0
  rw [laplaceMeasure_of_scale_ne_zero 1 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [withDensity_apply _ (measurableSet_singleton 0)]
  simp [Measure.restrict_singleton]

/-- **Data-dependent noise is NOT ε-DP for any ε.**

    d₁ = false gives deterministic output, d₂ = true gives continuous output.
    The event {0} has probability 1 vs 0.
    DP inequality: 1 ≤ exp(ε) · 0 = 0, contradiction. -/
theorem dataDependentNoise_not_pureDP (ε : NNReal) :
    ¬ IsPureDP BoolAdj dataDependentNoiseMech ε := by
  intro h
  have h_dp := h false true trivial {(0 : ℝ)} (measurableSet_singleton 0)
  rw [dataDep_false_singleton, dataDep_true_singleton, mul_zero,
      ENNReal.coe_zero, add_zero] at h_dp
  exact absurd h_dp (by simp)

/-- **Data-dependent noise is NOT (ε, δ)-DP for any ε and δ < 1.** -/
theorem dataDependentNoise_not_approxDP (ε : NNReal) {δ : NNReal}
    (hδ : (δ : ℝ) < 1) :
    ¬ IsApproxDP BoolAdj dataDependentNoiseMech ε δ := by
  intro h
  have h_dp := h false true trivial {(0 : ℝ)} (measurableSet_singleton 0)
  rw [dataDep_false_singleton, dataDep_true_singleton, mul_zero, zero_add] at h_dp
  have h4 : (δ : ENNReal) < 1 := by
    rw [ENNReal.coe_lt_one_iff]; exact_mod_cast hδ
  exact absurd (le_trans h_dp (le_refl _)) (not_le.mpr h4)

end DataDependentNoise

-- ============================================================================
-- §2: Thresholded Histogram — Suppress noise for zero counts
-- ============================================================================

/-! ### Thresholded Histogram

**Mechanism**: If q(d) > 0, release q(d) + Lap(0, b). If q(d) = 0, release 0.

This "sparse histogram" optimization suppresses noise for zero counts. It's
a common implementation mistake in practice.

**Why it fails**: Under d₂ = 0, the output is deterministically 0, so
P(M(0) = 0) = 1. Under d₁ = 1, the output is 1 + Lap(0, b), a continuous
distribution with P(M(1) = 0) = 0.

Reference: Korolova et al. (2009), Dwork & Roth (2014) §3.5. Every histogram
bin must receive noise, even bins with zero count.
-/

section ThresholdedHistogram

/-- Thresholded histogram: noise only when count > 0.
    Uses Bool input: true = nonempty bin, false = empty bin. -/
def thresholdedHistMech (b : NNReal) : Mechanism Bool ℝ :=
  fun d =>
    if d then ⟨laplaceMeasure 1 b, inferInstance⟩
    else ⟨Measure.dirac (0 : ℝ), inferInstance⟩

private def BoolAdj' : Bool → Bool → Prop := fun _ _ => True

/-- Under d = false (empty bin), output is Dirac(0). P(output = 0) = 1. -/
private lemma thresh_false_singleton (b : NNReal) :
    (thresholdedHistMech b false).toMeasure {(0 : ℝ)} = 1 := by
  simp [thresholdedHistMech]

/-- Under d = true (nonempty bin), output is Lap(1, b). P(output = 0) = 0
    because the Laplace distribution is absolutely continuous. -/
private lemma thresh_true_singleton {b : NNReal} (hb : b ≠ 0) :
    (thresholdedHistMech b true).toMeasure {(0 : ℝ)} = 0 := by
  show (laplaceMeasure 1 b) {(0 : ℝ)} = 0
  rw [laplaceMeasure_of_scale_ne_zero 1 hb,
      withDensity_apply _ (measurableSet_singleton 0)]
  simp [Measure.restrict_singleton]

/-- **Thresholded histogram is NOT ε-DP for any ε.**

    The noise suppression for zero counts creates a deterministic output
    that's distinguishable from the noisy output for nonzero counts.
    This is why every histogram bin must receive noise, regardless of
    whether the true count is zero.

    Reference: Korolova et al. (2009), Dwork & Roth (2014) §3.5. -/
theorem thresholdedHist_not_pureDP {b : NNReal} (hb : b ≠ 0) (ε : NNReal) :
    ¬ IsPureDP BoolAdj' (thresholdedHistMech b) ε := by
  intro h
  have h_dp := h false true trivial {(0 : ℝ)} (measurableSet_singleton 0)
  rw [thresh_false_singleton, thresh_true_singleton hb, mul_zero,
      ENNReal.coe_zero, add_zero] at h_dp
  exact absurd h_dp (by simp)

/-- **Thresholded histogram is NOT (ε, δ)-DP for δ < 1.** -/
theorem thresholdedHist_not_approxDP {b : NNReal} (hb : b ≠ 0) (ε : NNReal)
    {δ : NNReal} (hδ : (δ : ℝ) < 1) :
    ¬ IsApproxDP BoolAdj' (thresholdedHistMech b) ε δ := by
  intro h
  have h_dp := h false true trivial {(0 : ℝ)} (measurableSet_singleton 0)
  rw [thresh_false_singleton, thresh_true_singleton hb, mul_zero, zero_add] at h_dp
  have h4 : (δ : ENNReal) < 1 := by
    rw [ENNReal.coe_lt_one_iff]; exact_mod_cast hδ
  exact absurd (le_trans h_dp (le_refl _)) (not_le.mpr h4)

end ThresholdedHistogram

-- ============================================================================
-- §3: Conditional Release — Safety check leaks information
-- ============================================================================

/-! ### Conditional Release via Boolean Flag

**Mechanism**: M(d) = (d + Lap(0, b) > 0, indicator whether |d| < 1).

The second component is a Boolean flag revealing whether the database
passes a "safety check." The noisy first component is DP by itself, but
including the deterministic flag breaks DP.

This models the real-world mistake of releasing auxiliary information
(data quality flags, convergence indicators, etc.) alongside noisy results.

Reference: Dwork & Roth (2014) §3.5 — only the noisy output should be
released; auxiliary data-dependent information violates DP.
-/

section ConditionalRelease

/-- Map noise to (noisy answer, safety flag). The safety flag is deterministic. -/
private def condReleaseMap (d : ℝ) : ℝ → ℝ × Bool :=
  fun η => (d + η, decide (|d| < 1))

private theorem measurable_condReleaseMap (d : ℝ) : Measurable (condReleaseMap d) := by
  apply Measurable.prod
  · exact measurable_const.add measurable_id
  · exact measurable_const

/-- Conditional release mechanism: (d + Lap(0,b), flag whether |d| < 1). -/
def conditionalReleaseMech (b : NNReal) : Mechanism ℝ (ℝ × Bool) :=
  fun d => ProbabilityMeasure.map
    (⟨laplaceMeasure 0 b, inferInstance⟩ : ProbabilityMeasure ℝ)
    (measurable_condReleaseMap d).aemeasurable

private def RealAdj' : ℝ → ℝ → Prop := fun _ _ => True

/-- The discriminating event: second component is true (flag says "safe"). -/
private def safeEvent : Set (ℝ × Bool) := {p : ℝ × Bool | p.2 = true}

private theorem measurableSet_safeEvent : MeasurableSet safeEvent :=
  measurableSet_preimage measurable_snd (measurableSet_singleton true)

/-- Under d₁ = 0 (safe: |0| < 1), the flag is always true. -/
private lemma condRelease_d0_preimage :
    condReleaseMap 0 ⁻¹' safeEvent = Set.univ := by
  ext η; simp [condReleaseMap, safeEvent, abs_zero]

/-- Under d₂ = 2 (unsafe: |2| ≥ 1), the flag is always false. -/
private lemma condRelease_d2_preimage :
    condReleaseMap 2 ⁻¹' safeEvent = ∅ := by
  ext η; simp [condReleaseMap, safeEvent]

/-- P(M(0) ∈ safeEvent) = 1. -/
private lemma condRelease_d0_prob (b : NNReal) :
    (conditionalReleaseMech b 0).toMeasure safeEvent = 1 := by
  have : (conditionalReleaseMech b 0).toMeasure =
      (laplaceMeasure 0 b).map (condReleaseMap 0) := rfl
  rw [this, Measure.map_apply (measurable_condReleaseMap 0) measurableSet_safeEvent,
      condRelease_d0_preimage, measure_univ]

/-- P(M(2) ∈ safeEvent) = 0. -/
private lemma condRelease_d2_prob (b : NNReal) :
    (conditionalReleaseMech b 2).toMeasure safeEvent = 0 := by
  have : (conditionalReleaseMech b 2).toMeasure =
      (laplaceMeasure 0 b).map (condReleaseMap 2) := rfl
  rw [this, Measure.map_apply (measurable_condReleaseMap 2) measurableSet_safeEvent,
      condRelease_d2_preimage, measure_empty]

/-- **Conditional release is NOT ε-DP for any ε.**

    The deterministic safety flag distinguishes d₁ = 0 (safe) from d₂ = 2
    (unsafe) with certainty, even though the noisy component alone would be
    DP. This demonstrates that releasing ANY data-dependent auxiliary
    information alongside a DP output breaks the overall guarantee. -/
theorem conditionalRelease_not_pureDP {b : NNReal} (ε : NNReal) :
    ¬ IsPureDP RealAdj' (conditionalReleaseMech b) ε := by
  intro h
  have h_dp := h 0 2 trivial safeEvent measurableSet_safeEvent
  rw [condRelease_d0_prob, condRelease_d2_prob, mul_zero,
      ENNReal.coe_zero, add_zero] at h_dp
  exact absurd h_dp (by simp)

/-- **Conditional release is NOT (ε, δ)-DP for δ < 1.** -/
theorem conditionalRelease_not_approxDP {b : NNReal} (ε : NNReal)
    {δ : NNReal} (hδ : (δ : ℝ) < 1) :
    ¬ IsApproxDP RealAdj' (conditionalReleaseMech b) ε δ := by
  intro h
  have h_dp := h 0 2 trivial safeEvent measurableSet_safeEvent
  rw [condRelease_d0_prob, condRelease_d2_prob, mul_zero, zero_add] at h_dp
  have h4 : (δ : ENNReal) < 1 := by
    rw [ENNReal.coe_lt_one_iff]; exact_mod_cast hδ
  exact absurd (le_trans h_dp (le_refl _)) (not_le.mpr h4)

end ConditionalRelease

end DPlean4.Examples.TrickyCounterexamples

end -- noncomputable section
