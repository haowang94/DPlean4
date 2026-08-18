/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Approximate
import DPlean4.Distribution.Laplace

/-!
# Counterexamples: Mechanisms That Fail Differential Privacy

This file collects formal proofs that certain mechanisms do NOT satisfy
differential privacy, demonstrating that our framework can refute DP claims.

## Results

* `identityMech_not_pureDP`: The identity mechanism (output = input) is not ε-DP
  for any ε. Deterministic non-trivial mechanisms cannot be differentially private.
* `identityMech_not_approxDP`: The identity mechanism is not (ε,δ)-DP for any
  ε and δ < 1.

## Significance

These results demonstrate that:
1. The DP definitions are non-trivial (not everything satisfies them)
2. The framework can formally refute incorrect DP claims
3. Noise is essential: deterministic mechanisms leak exact information

## Methodology

To show ¬ IsPureDP, we exhibit specific adjacent databases d₁, d₂ and a
measurable event S where the DP inequality P(M(d₁)∈S) ≤ exp(ε)·P(M(d₂)∈S)
fails. For the identity mechanism, M(d) = Dirac(d), so M(d₁)({d₁}) = 1
but M(d₂)({d₁}) = 0, giving 1 ≤ 0 — a contradiction.
-/

noncomputable section

namespace DPlean4

open MeasureTheory

/-- The identity mechanism outputs the database value directly, with no noise. -/
def identityMech : Mechanism Bool Bool :=
  fun d => ⟨Measure.dirac d, inferInstance⟩

/-- All pairs of `Bool` values are adjacent (worst-case single-bit adjacency). -/
private def AllAdj : Bool → Bool → Prop := fun _ _ => True

/-- **The identity mechanism is not ε-DP for any ε.**

    The identity mechanism M(d) = Dirac(d) reveals the exact database value.
    For d₁ = true, d₂ = false, the event S = {true} gives:
      P(M(true) ∈ S) = 1,  P(M(false) ∈ S) = 0
    so 1 ≤ exp(ε) · 0 = 0 fails for all ε. -/
theorem identityMech_not_pureDP (ε : NNReal) :
    ¬ IsPureDP AllAdj identityMech ε := by
  intro h
  have h1 : (identityMech true).toMeasure {true} = 1 := by simp [identityMech]
  have h2 : (identityMech false).toMeasure {true} = 0 := by simp [identityMech]
  have h3 := h true false trivial {true} (measurableSet_singleton true)
  rw [h1, h2] at h3
  simp at h3

/-- **The identity mechanism is not (ε,δ)-DP for any ε and δ < 1.**

    Even allowing a failure probability δ, the identity mechanism still fails:
      1 = P(M(true) ∈ {true}) ≤ exp(ε) · 0 + δ = δ
    requires δ ≥ 1, contradicting δ < 1. -/
theorem identityMech_not_approxDP (ε : NNReal) {δ : NNReal} (hδ : (δ : ℝ) < 1) :
    ¬ IsApproxDP AllAdj identityMech ε δ := by
  intro h
  have h1 : (identityMech true).toMeasure {true} = 1 := by simp [identityMech]
  have h2 : (identityMech false).toMeasure {true} = 0 := by simp [identityMech]
  have h3 := h true false trivial {true} (measurableSet_singleton true)
  rw [h1, h2] at h3
  simp only [mul_zero, zero_add] at h3
  have h4 : (δ : ENNReal) < 1 := by
    rw [ENNReal.coe_lt_one_iff]; exact_mod_cast hδ
  exact absurd (le_trans h3 (le_refl _)) (not_le.mpr h4)

-- ============================================================================
-- Buggy SVT5: No query noise (Lyu et al. 2017)
-- ============================================================================

/-! ### Buggy SVT without query noise is NOT ε-DP

This formalizes the counterexample from Algorithm 5 in Lyu et al. (2017),
"Understanding the Sparse Vector Technique for Differential Privacy."

**The bug**: SVT5 adds Laplace noise only to the threshold, not to query answers.
Correct SVT adds noise to both.

**Setup**:
- Two databases d₁ = true, d₂ = false
- Two queries: q₁(true) = 0, q₁(false) = 1; q₂(true) = 1, q₂(false) = 0
- Threshold T = 0, threshold noise ρ ~ Laplace(0, b)
- Output: (q₁(d) ≥ ρ, q₂(d) ≥ ρ) — compare raw query values to noisy threshold

**Counterexample**: Event S = {(false, true)} (q₁ below, q₂ above)
- Under d₁ (q₁=0, q₂=1): S requires 0 < ρ ≤ 1, which has positive probability
- Under d₂ (q₁=1, q₂=0): S requires 1 < ρ ≤ 0, which is IMPOSSIBLE

So P(S | d₁) > 0 but P(S | d₂) = 0, violating pure DP for any ε. -/

section BuggySVT

open MeasureTheory

/-- Measurability lemma for comparing two real numbers to a threshold. -/
private theorem measurable_compare_to_threshold (q₁_val q₂_val : ℝ) :
    Measurable (fun ρ : ℝ => (decide (q₁_val ≥ ρ), decide (q₂_val ≥ ρ))) := by
  apply Measurable.prod
  · exact Measurable.ite measurableSet_Iic measurable_const measurable_const
  · exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- Helper: create a probability measure from the Laplace measure. -/
private def laplacePM (b : NNReal) : ProbabilityMeasure ℝ :=
  ⟨laplaceMeasure 0 b, inferInstance⟩

/-- Buggy SVT5: compare raw query values to a single noisy threshold.
    This mechanism adds Laplace noise only to the threshold, NOT to queries. -/
private def buggySVT5 (q₁ q₂ : Bool → ℝ) (b : NNReal) : Mechanism Bool (Bool × Bool) :=
  fun d => ProbabilityMeasure.map (laplacePM b)
    (measurable_compare_to_threshold (q₁ d) (q₂ d)).aemeasurable

private def q₁_svt : Bool → ℝ := fun d => if d then 0 else 1
private def q₂_svt : Bool → ℝ := fun d => if d then 1 else 0

/-- The preimage of {(false, true)} under d₂'s SVT5 map is empty.
    Under d₂ = false: q₁=1, q₂=0, so {(false,true)} requires ρ > 1 ∧ ρ ≤ 0. -/
private lemma svt5_d2_preimage_empty :
    (fun ρ : ℝ => (decide (q₁_svt false ≥ ρ), decide (q₂_svt false ≥ ρ))) ⁻¹'
      {(false, true)} = ∅ := by
  ext ρ; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, q₁_svt, q₂_svt,
    ite_false, Set.mem_empty_iff_false, iff_false, not_and]
  intro h₁ h₂
  simp [decide_eq_false_iff_not, not_le] at h₁
  simp [decide_eq_true_eq] at h₂
  linarith

/-- The preimage of {(false, true)} under d₁'s SVT5 map is Ioc 0 1.
    Under d₁ = true: q₁=0, q₂=1, so {(false,true)} requires ρ > 0 ∧ ρ ≤ 1. -/
private lemma svt5_d1_preimage_eq :
    (fun ρ : ℝ => (decide (q₁_svt true ≥ ρ), decide (q₂_svt true ≥ ρ))) ⁻¹'
      {(false, true)} = Set.Ioc 0 1 := by
  ext ρ; simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, q₁_svt, q₂_svt,
    ite_true, Set.mem_Ioc]
  constructor
  · rintro ⟨h₁, h₂⟩
    simp only [decide_eq_false_iff_not, not_le] at h₁
    simp only [decide_eq_true_eq] at h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by simp [decide_eq_false_iff_not, not_le, h₁],
           by simp [decide_eq_true_eq, h₂]⟩

/-- **Buggy SVT5 is NOT ε-DP for any ε** (Lyu et al. 2017, Algorithm 5).

    The mechanism without query noise has an output event with positive probability
    under one database but zero probability under the other, making the privacy
    loss infinite. This demonstrates that noise on queries (not just the threshold)
    is essential for SVT's privacy guarantee. -/
theorem buggySVT5_not_pureDP {b : NNReal} (hb : b ≠ 0) (ε : NNReal) :
    ¬ IsPureDP AllAdj (buggySVT5 q₁_svt q₂_svt b) ε := by
  intro h
  set S : Set (Bool × Bool) := {(false, true)}
  have hS : MeasurableSet S := measurableSet_singleton _
  have h_dp := h true false trivial S hS
  -- M(d₂)(S) = 0 because the preimage is empty
  have h_d2_zero : (buggySVT5 q₁_svt q₂_svt b false).toMeasure S = 0 := by
    unfold buggySVT5
    rw [ProbabilityMeasure.toMeasure_map, laplacePM, ProbabilityMeasure.toMeasure]
    rw [Measure.map_apply (measurable_compare_to_threshold (q₁_svt false) (q₂_svt false)) hS,
        svt5_d2_preimage_empty]
    simp
  -- M(d₁)(S) > 0 because the preimage is Ioc 0 1
  have h_d1_pos : 0 < (buggySVT5 q₁_svt q₂_svt b true).toMeasure S := by
    unfold buggySVT5
    rw [ProbabilityMeasure.toMeasure_map, laplacePM, ProbabilityMeasure.toMeasure]
    rw [Measure.map_apply (measurable_compare_to_threshold (q₁_svt true) (q₂_svt true)) hS,
        svt5_d1_preimage_eq]
    exact laplaceMeasure_Ioc_pos hb (by norm_num : (0 : ℝ) < 1)
  -- Combine: h_dp says M(d₁)(S) ≤ exp(ε) * M(d₂)(S) = exp(ε) * 0 = 0
  rw [h_d2_zero, mul_zero, ENNReal.coe_zero, add_zero] at h_dp
  exact absurd h_dp (not_le.mpr h_d1_pos)

end BuggySVT

end DPlean4

end -- noncomputable section
