/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Exponential
import DPlean4.Mechanism.VectorLaplace
import DPlean4.Privacy.Postprocessing
import DPlean4.Basic.Sensitivity

/-!
# Report Noisy Max / Private Argmax Mechanisms

Given `n` queries `q₀,...,qₙ₋₁ : D → ℝ`, each with sensitivity `Δ`, we want to
privately return the index of the (approximately) largest query value. This file
provides two mechanisms.

## `exponentialArgmax` — sampling proportional to `exp(ε·qᵢ/(2Δ))`

This runs the exponential mechanism with utility `u(d,i) = qᵢ(d)`, sampling index
`i` with probability proportional to `exp(ε·qᵢ(d)/(2Δ))`. It satisfies ε-DP
directly from `expMech_isPureDP` (a tight ε bound, not `nε`). Note this is
*exactly* Report Noisy Max with **Gumbel** noise (the Gumbel-max trick), but it is
not the classical Laplace-noise construction below — the two have the same privacy
parameter but different output distributions and accuracy.

## `classicalReportNoisyMax` — add independent Laplace noise, then take argmax

This is the textbook "add noise then argmax" form (Dwork & Roth 2014, Alg. 2):
add independent `Lap(0, b)` noise to each score and return the argmax index. We
obtain it as measurable postprocessing (`argmax`) of the vector Laplace mechanism,
so ε-DP follows from `vectorLaplaceMech_isPureDP` + `isPureDP_postprocess`.

**Calibration caveat.** Releasing the *whole* noisy score vector and then taking
argmax charges the L1 vector sensitivity `n·Δ`, i.e. noise scale `b = n·Δ/ε` —
a factor of `n` looser than the textbook tight analysis (`b = 2Δ/ε`), which
instead reasons directly about `P[argmax = i]`. The tight bound needs a Laplace
survival-function ratio plus an argmax-threshold coupling argument and is left as
future work; the version here is faithful in *form* and correct, but loose in the
noise constant.

## Main Results

* `exponentialArgmax_isPureDP`: exponential-mechanism argmax satisfies ε-DP
* `classicalReportNoisyMax_isPureDP`: classical noise+argmax satisfies ε-DP

## References

* Dwork & Roth, "The Algorithmic Foundations of Differential Privacy" (2014),
  Section 3.3, Algorithm 2 (Report Noisy Max)
* McSherry & Talwar, "Mechanism Design via Differential Privacy" (2007)
-/

noncomputable section

namespace DPlean4

open MeasureTheory
open scoped NNReal ENNReal

variable {D : Type*} {n : ℕ}

-- ============================================================================
-- Query Utility (for the exponential-mechanism argmax)
-- ============================================================================

/-- Build an exponential mechanism utility from a collection of queries:
    `queryUtility qs d i = qᵢ(d)`. -/
def queryUtility (qs : Fin n → D → ℝ) : D → Fin n → ℝ :=
  fun d i => qs i d

/-- If each query has L1 sensitivity at most Δ, then the query-evaluation utility
    has utility sensitivity Δ: changing the database changes any query's value
    by at most Δ. -/
theorem queryUtility_sensitivity {adj : D → D → Prop} {qs : Fin n → D → ℝ} {Δ : ℝ≥0}
    (hsens : ∀ i, HasL1Sensitivity adj (qs i) Δ) :
    HasUtilitySensitivity adj (queryUtility qs) Δ := by
  intro d₁ d₂ hadj i
  exact hsens i d₁ d₂ hadj

-- ============================================================================
-- Exponential-mechanism argmax (Gumbel-noise Report Noisy Max)
-- ============================================================================

variable [Nonempty (Fin n)]

/-- The exponential-mechanism argmax: privately select the index with (roughly)
    the highest value by running the exponential mechanism with utility
    `u(d, i) = qᵢ(d)`.

    Samples index i with probability proportional to `exp(ε · qᵢ(d) / (2Δ))`.
    This is the Gumbel-noise form of Report Noisy Max. -/
def exponentialArgmax (qs : Fin n → D → ℝ) (ε : NNReal) (Δ : ℝ≥0) :
    Mechanism D (Fin n) :=
  expMech (queryUtility qs) ε Δ

/-- **The exponential-mechanism argmax satisfies ε-DP.**

    If each of the n queries has L1 sensitivity at most Δ > 0 under adjacency `adj`,
    the mechanism satisfies ε-DP (bound ε, not nε, via the exponential-mechanism
    analysis). -/
theorem exponentialArgmax_isPureDP {adj : D → D → Prop}
    {qs : Fin n → D → ℝ} {Δ : ℝ≥0} (hΔ : Δ ≠ 0) {ε : NNReal}
    (hsens : ∀ i, HasL1Sensitivity adj (qs i) Δ) :
    IsPureDP adj (exponentialArgmax qs ε Δ) ε :=
  expMech_isPureDP hΔ (queryUtility_sensitivity hsens)

-- ============================================================================
-- Measurable argmax
-- ============================================================================

/-- The least index achieving the maximum coordinate (ties broken by the smallest
    index). Total on nonempty `Fin n`. -/
noncomputable def argmaxFin {n : ℕ} [NeZero n] (x : Fin n → ℝ) : Fin n :=
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  (Finset.univ.filter (fun i => ∀ j, x j ≤ x i)).min'
    ⟨(Finite.exists_max x).choose,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finite.exists_max x).choose_spec⟩⟩

/-- Characterization of the least maximizer: `argmaxFin x = i` iff `i` maximizes
    `x` and every strictly smaller index is strictly below `x i`. -/
theorem argmaxFin_spec {n : ℕ} [NeZero n] (x : Fin n → ℝ) (i : Fin n) :
    argmaxFin x = i ↔ (∀ j, x j ≤ x i) ∧ (∀ k, k < i → x k < x i) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set S := Finset.univ.filter (fun i => ∀ j, x j ≤ x i) with hS
  have hne : S.Nonempty := by
    obtain ⟨m, hm⟩ := Finite.exists_max x
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩
  have hmem : ∀ a, a ∈ S ↔ ∀ j, x j ≤ x a := by
    intro a
    rw [hS, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ a, h⟩⟩
  have hval : argmaxFin x = S.min' hne := rfl
  rw [hval]
  constructor
  · intro hx
    have hi_mem : i ∈ S := hx ▸ S.min'_mem hne
    have hi_max : ∀ j, x j ≤ x i := (hmem i).mp hi_mem
    refine ⟨hi_max, ?_⟩
    intro k hk
    by_contra hcon
    push_neg at hcon
    have hk_max : ∀ j, x j ≤ x k := fun j => le_trans (hi_max j) hcon
    have hk_mem : k ∈ S := (hmem k).mpr hk_max
    have hle : S.min' hne ≤ k := S.min'_le k hk_mem
    rw [hx] at hle
    exact absurd (lt_of_lt_of_le hk hle) (lt_irrefl k)
  · rintro ⟨hi_max, hi_lt⟩
    have hi_mem : i ∈ S := (hmem i).mpr hi_max
    refine le_antisymm (S.min'_le i hi_mem) ?_
    by_contra hcon
    push_neg at hcon
    have hm_mem : S.min' hne ∈ S := S.min'_mem hne
    have hm_max : ∀ j, x j ≤ x (S.min' hne) := (hmem _).mp hm_mem
    exact absurd (hm_max i) (not_le.mpr (hi_lt _ hcon))

/-- The least-maximizer argmax is measurable. -/
theorem measurable_argmaxFin {n : ℕ} [NeZero n] : Measurable (argmaxFin (n := n)) := by
  apply measurable_to_countable'
  intro i
  have hset : argmaxFin ⁻¹' {i} =
      {x : Fin n → ℝ | ∀ j, x j ≤ x i} ∩ {x : Fin n → ℝ | ∀ k, k < i → x k < x i} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact argmaxFin_spec x i
  rw [hset]
  apply MeasurableSet.inter
  · have h1 : {x : Fin n → ℝ | ∀ j, x j ≤ x i} = ⋂ j, {x : Fin n → ℝ | x j ≤ x i} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [h1]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)
  · have h2 : {x : Fin n → ℝ | ∀ k, k < i → x k < x i}
        = ⋂ k, ⋂ (_ : k < i), {x : Fin n → ℝ | x k < x i} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [h2]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply k) (measurable_pi_apply i)

-- ============================================================================
-- Classical Report Noisy Max (add Laplace noise, then argmax)
-- ============================================================================

/-- The score vector query: `scoreVector qs d i = qᵢ(d)`. -/
def scoreVector (qs : Fin n → D → ℝ) : D → (Fin n → ℝ) := fun d i => qs i d

/-- If each of the `n` queries has L1 sensitivity `Δ`, the score vector has L1
    vector sensitivity `n·Δ` (the crude sum-over-coordinates bound). -/
theorem scoreVector_l1_sensitivity {adj : D → D → Prop} {qs : Fin n → D → ℝ} {Δ : ℝ≥0}
    (hsens : ∀ i, HasL1Sensitivity adj (qs i) Δ) :
    HasL1VectorSensitivity adj (scoreVector qs) (n • Δ) := by
  intro d₁ d₂ hadj
  calc ∑ i, |scoreVector qs d₁ i - scoreVector qs d₂ i|
      = ∑ i : Fin n, |qs i d₁ - qs i d₂| := rfl
    _ ≤ ∑ _i : Fin n, (↑Δ : ℝ) := Finset.sum_le_sum fun i _ => hsens i d₁ d₂ hadj
    _ = ↑(n • Δ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          NNReal.coe_mul, NNReal.coe_natCast]

/-- **Classical Report Noisy Max**: add independent `Lap(0, n·Δ/ε)` noise to each
    score, then return the argmax index. Realized as measurable argmax
    postprocessing of the vector Laplace mechanism. See the module docstring for
    the `n·Δ` (vs textbook `2Δ`) calibration caveat. -/
noncomputable def classicalReportNoisyMax [NeZero n]
    (qs : Fin n → D → ℝ) (Δ ε : ℝ≥0) : Mechanism D (Fin n) :=
  fun d => (vectorLaplaceMech (scoreVector qs) (n • Δ) ε d).map measurable_argmaxFin.aemeasurable

/-- **Classical Report Noisy Max satisfies ε-DP.**

    Postprocessing (the deterministic argmax) preserves the ε-DP of the vector
    Laplace mechanism calibrated to the score vector's L1 sensitivity `n·Δ`. -/
theorem classicalReportNoisyMax_isPureDP [NeZero n] {adj : D → D → Prop}
    {qs : Fin n → D → ℝ} {Δ ε : ℝ≥0} (hε : ε ≠ 0)
    (hsens : ∀ i, HasL1Sensitivity adj (qs i) Δ) :
    IsPureDP adj (classicalReportNoisyMax qs Δ ε) ε :=
  isPureDP_postprocess
    (vectorLaplaceMech_isPureDP hε (scoreVector_l1_sensitivity hsens))
    measurable_argmaxFin

end DPlean4

end -- noncomputable section
