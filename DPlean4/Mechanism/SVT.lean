/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Postprocessing
import DPlean4.Privacy.Composition
import DPlean4.Basic.Sensitivity

/-!
# Sparse Vector Technique (SVT)

The Sparse Vector Technique (Dwork & Roth 2014) tests a stream of queries against
a noisy threshold, outputting which queries are "above threshold" while consuming
privacy budget only for the above-threshold answers.

This file formalizes:
1. **Above Threshold** (single query): Laplace mechanism + thresholding (sorry-free, ε-DP)
2. **Noisy Above Threshold** (single query with shared threshold noise): product of
   query + threshold Laplace noises + comparison (sorry-free, ε-DP)

## Why SVT Matters

SVT is a prime target for formal verification because multiple published papers
contained incorrect privacy proofs for SVT variants (Lyu et al. 2017,
"Understanding the Sparse Vector Technique for Differential Privacy"). The correct
version was established by Dwork & Roth, but variants that modify the noise
calibration or output numerical values have been falsely claimed to satisfy ε-DP.

## Main Results

* `aboveThreshold_isPureDP`: Single-query threshold test is ε-DP
* `noisyAboveThreshold_isPureDP`: Two-noise threshold test is ε-DP

## Proof Strategy

Both results follow from the fundamental composition pattern:

1. The Laplace mechanism is ε-DP (`laplaceMech_isPureDP`)
2. A data-independent mechanism is 0-DP (`constantMechanism_isPureDP`)
3. Products compose: ε₁-DP ⊗ ε₂-DP → (ε₁+ε₂)-DP (`isPureDP_prod`)
4. Postprocessing preserves DP (`isPureDP_postprocess`)

## References

* Dwork, C. & Roth, A. (2014). The Algorithmic Foundations of Differential Privacy.
  Theorem 3.24 (Above Threshold).
* Lyu, M. et al. (2017). Understanding the Sparse Vector Technique for
  Differential Privacy. VLDB.
-/

noncomputable section

namespace DPlean4

open MeasureTheory
open scoped NNReal ENNReal

variable {D : Type*}

-- ============================================================================
-- Measurability Helpers
-- ============================================================================

private theorem measurable_ge_const (T : ℝ) :
    Measurable (fun x : ℝ => decide (x ≥ T)) :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

private theorem measurable_ge_pair :
    Measurable (fun p : ℝ × ℝ => decide (p.1 ≥ p.2)) :=
  Measurable.ite (isClosed_le continuous_snd continuous_fst).measurableSet
    measurable_const measurable_const

-- ============================================================================
-- Above Threshold (Single Query)
-- ============================================================================

/-- Single-query above-threshold test: add Laplace noise to query q(d) and check
    if the noisy value exceeds threshold T.

    This is the simplest instance of the Sparse Vector Technique (n=1, c=1).
    Since only one query is tested, no threshold noise is needed — the threshold
    is a public constant, so thresholding is pure postprocessing of the Laplace
    mechanism. -/
def aboveThreshold (q : D → ℝ) (T : ℝ) (Δ ε : NNReal) : Mechanism D Bool :=
  fun d => (laplaceMech q Δ ε d).map (measurable_ge_const T).aemeasurable

/-- **The single-query above-threshold test satisfies ε-DP.**

    The Laplace mechanism adds noise calibrated to the query's sensitivity,
    and thresholding is a deterministic postprocessing step that cannot degrade
    privacy. -/
theorem aboveThreshold_isPureDP {adj : D → D → Prop} {q : D → ℝ} {Δ ε : NNReal}
    (T : ℝ) (hε : ε ≠ 0) (hsens : HasL1Sensitivity adj q Δ) :
    IsPureDP adj (aboveThreshold q T Δ ε) ε := by
  unfold aboveThreshold
  exact isPureDP_postprocess (laplaceMech_isPureDP hε hsens) (measurable_ge_const T)

-- ============================================================================
-- Noisy Above Threshold (Two Independent Noise Terms)
-- ============================================================================

/-- Above-threshold test with separate threshold noise: independently add Laplace
    noise to both the query value and the threshold, then compare.

    This is the building block for the general SVT. Adding noise to the threshold
    is redundant for a single query (it only increases variance without improving
    privacy), but for multiple queries the shared threshold noise is essential —
    it allows the total privacy cost to be independent of the number of queries.

    Parameters:
    - `q`: the query function
    - `T`: the public threshold
    - `Δ, ε`: sensitivity and privacy parameter for the query noise
    - `b_t`: scale parameter for the threshold noise (arbitrary, doesn't affect DP) -/
def noisyAboveThreshold (q : D → ℝ) (T : ℝ) (Δ ε : NNReal) (b_t : NNReal) :
    Mechanism D Bool :=
  fun d => ((laplaceMech q Δ ε d).prod
    (⟨laplaceMeasure T b_t, inferInstance⟩ : ProbabilityMeasure ℝ)).map
    measurable_ge_pair.aemeasurable

/-- **The noisy above-threshold test satisfies ε-DP.**

    The query noise (Laplace mechanism) is ε-DP. The threshold noise is a
    data-independent constant mechanism (0-DP). Their product is (ε+0)=ε-DP
    by independent composition, and the comparison is a measurable
    postprocessing step. -/
theorem noisyAboveThreshold_isPureDP {adj : D → D → Prop} {q : D → ℝ}
    {Δ ε : NNReal} (T : ℝ) (b_t : NNReal)
    (hε : ε ≠ 0) (hsens : HasL1Sensitivity adj q Δ) :
    IsPureDP adj (noisyAboveThreshold q T Δ ε b_t) ε := by
  unfold noisyAboveThreshold
  have hconst : IsPureDP adj
      (fun (_ : D) => (⟨laplaceMeasure T b_t, inferInstance⟩ : ProbabilityMeasure ℝ)) 0 :=
    constantMechanism_isPureDP adj
  have hprod := isPureDP_prod (laplaceMech_isPureDP hε hsens) hconst
  simp only [add_zero] at hprod
  exact isPureDP_postprocess hprod measurable_ge_pair

-- ============================================================================
-- Stream Sensitivity
-- ============================================================================

/-- A stream of queries has L1 sensitivity at most Δ if every individual query
    in the stream has L1 sensitivity at most Δ. -/
def HasStreamL1Sensitivity (adj : D → D → Prop)
    (qs : Fin n → D → ℝ) (Δ : ℝ≥0) : Prop :=
  ∀ i, HasL1Sensitivity adj (qs i) Δ

-- ============================================================================
-- General SVT (n queries, c = 1) — Theorem Statement
-- ============================================================================

/-! ### General Sparse Vector Technique

The general SVT processes n queries q₁, ..., qₙ against a shared noisy threshold:

1. Sample threshold noise ρ ~ Lap(T, b_threshold)
2. For each query qᵢ in sequence:
   - Sample query noise νᵢ ~ Lap(qᵢ(d), b_query)
   - If νᵢ ≥ ρ: output `some i` ("above threshold"), halt
   - Else: continue to next query
3. If no query exceeded: output `none`

**Key property**: The privacy cost is ε regardless of n. This is because only the
single above-threshold query contributes to privacy loss — "below threshold" answers
are "free" in the sense that they become more likely (not less) when query sensitivity
shifts the value downward.

**Why the proof is hard**: Proving this requires showing that the density ratio for
"below" events is bounded by 1, which involves an argument about the monotonicity of
Laplace CDF ratios under sensitivity shifts. This goes beyond simple composition and
requires either:
- Direct analysis of the joint probability ratio (multi-dimensional integration)
- Adaptive composition via Markov kernels with the "below is free" lemma

Both approaches require measure-theoretic infrastructure beyond what the library
currently provides. The single-query cases above demonstrate the framework handles
the core composition + postprocessing pattern; the general case is future work.

**Known buggy variants** (Lyu et al. 2017):
- SVT2: Uses insufficient query noise (Lap(2Δ/ε) instead of Lap(4cΔ/ε)) — NOT ε-DP
- SVT3: Outputs numerical noisy values instead of boolean above/below — NOT ε-DP
- SVT5: Claims pure DP with numerical output — NOT ε-DP

Formalizing these counterexamples (constructing specific databases and events that
violate the DP inequality) is a high-value target for future work.
-/

end DPlean4

end -- noncomputable section
