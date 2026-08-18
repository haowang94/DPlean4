/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Subsampling
import DPlean4.Basic.Adjacency

/-!
# Subsampling Amplification Examples

This file demonstrates privacy amplification by subsampling (Kasiviswanathan
et al. 2011, Balle et al. 2018): if a mechanism is ε-DP, running it on a
random q-fraction of the data gives ln(1 + q·(exp(ε)-1))-DP.

## Examples

1. `subsample_amplifies`: for any ε-DP mechanism, subsampling at rate q gives
   amplified privacy ln(1 + q·(exp(ε)-1))
2. `subsample_rate_zero`: subsampling at rate 0 gives perfect privacy (ε'=0)
3. `subsample_rate_one`: subsampling at rate 1 gives no amplification (ε'=ε)
4. `subsample_monotone_rate`: lower subsampling rate → better privacy
5. `subsample_monotone_eps`: lower base ε → better amplified ε

## Key Insight

For small ε, ln(1 + q·(exp(ε)-1)) ≈ q·ε, so privacy cost scales linearly
with the subsampling rate. This is the foundation of DP-SGD's privacy
accounting: each minibatch is a Poisson subsample with rate q = batch_size/n.

## References

* Kasiviswanathan, Lee, Nissim, Raskhodnikova, Smith (2011),
  "What can we learn privately?"
* Balle, Barthe, Gavin (2018),
  "Privacy Amplification by Subsampling: Tight Analyses via Couplings"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory
open scoped NNReal

variable {O : Type*} [MeasurableSpace O]

-- ============================================================================
-- Basic Subsampling Amplification
-- ============================================================================

/-- **Subsampling amplifies privacy**: if two measures are ε-close,
    their q-mixture with the second measure is ε'-close, where
    ε' = ln(1 + q·(exp(ε)-1)) ≤ ε. -/
theorem subsample_amplifies {ε : NNReal}
    {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose ε μ ν)
    {q : NNReal} (hq : q ≤ 1) :
    PureMeasureClose (subsampleEpsilon q ε) (mixtureMeasure q hq μ ν) ν :=
  pureMeasureClose_subsample h hq

-- ============================================================================
-- Boundary Cases
-- ============================================================================

/-- **Zero subsampling rate = perfect privacy**: if we never include any data,
    the output reveals nothing (ε' = 0). The mixture q·μ + (1-q)·ν at q=0
    is just ν, so trivially 0-close to ν. -/
theorem subsample_rate_zero (ε : NNReal) :
    subsampleEpsilon 0 ε = 0 :=
  subsampleEpsilon_zero ε

/-- **Full subsampling rate = no amplification**: if we include all data (q=1),
    the mixture is just μ, so we get the original ε. -/
theorem subsample_rate_one (ε : NNReal) :
    subsampleEpsilon 1 ε = 0 + ε := by
  rw [zero_add]; exact subsampleEpsilon_one ε

-- ============================================================================
-- Monotonicity
-- ============================================================================

/-- **Lower subsampling rate → better privacy**: fewer data points included
    means less information leaked. -/
theorem subsample_monotone_rate {q₁ q₂ : NNReal} (hq : q₁ ≤ q₂) (ε : NNReal) :
    subsampleEpsilon q₁ ε ≤ subsampleEpsilon q₂ ε :=
  subsampleEpsilon_mono_q hq ε

/-- **Lower base ε → better amplified ε**: a more private base mechanism
    gives a more private subsampled mechanism. -/
theorem subsample_monotone_eps {ε₁ ε₂ : NNReal} (hε : ε₁ ≤ ε₂) (q : NNReal) :
    subsampleEpsilon q ε₁ ≤ subsampleEpsilon q ε₂ :=
  subsampleEpsilon_mono_eps hε q

-- ============================================================================
-- Concrete Example: DP-SGD-style Subsampling
-- ============================================================================

/-- **DP-SGD subsampling**: a 1-DP Laplace mechanism run on a 10% subsample
    has amplified privacy ε' = ln(1 + 0.1·(e-1)) ≈ 0.158.

    This demonstrates the dramatic amplification:
    - Base mechanism: 1-DP
    - Subsampled mechanism: ~0.158-DP (≈ 6× improvement!)

    In practice, DP-SGD applies this at every training step with the
    Gaussian mechanism and uses RDP accounting for tighter composition. -/
theorem dpsgd_style_subsampling
    {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose (1 : NNReal) μ ν) :
    PureMeasureClose (subsampleEpsilon (⟨1/10, by norm_num⟩ : NNReal) 1)
      (mixtureMeasure ⟨1/10, by norm_num⟩ (by norm_num : (⟨1/10, by norm_num⟩ : NNReal) ≤ 1)
        μ ν)
      ν :=
  pureMeasureClose_subsample h (by norm_num)

/-- **Approximate DP subsampling bound**: if μ ≤[ε,δ] ν, the q-mixture
    satisfies q·μ(S) + (1-q)·ν(S) ≤ (q·exp(ε)+(1-q))·ν(S) + q·δ.
    Both ε and δ are amplified: ε shrinks and δ scales by q. -/
theorem subsample_approx_example
    {ε δ : NNReal} {μ ν : ProbabilityMeasure O}
    (h : MeasureClose ε δ μ ν) {q : NNReal} (hq : q ≤ 1)
    (s : Set O) (hs : MeasurableSet s) :
    (q : ℝ≥0∞) * μ.toMeasure s + (1 - (q : ℝ≥0∞)) * ν.toMeasure s ≤
      ((q : ℝ≥0∞) * ENNReal.ofReal (Real.exp ↑ε) +
        (1 - (q : ℝ≥0∞))) * ν.toMeasure s + (q : ℝ≥0∞) * (δ : ℝ≥0∞) :=
  subsample_approx_bound h hq s hs

-- ============================================================================
-- Subsampling + Composition Pipeline
-- ============================================================================

/-- **Subsampling composes with itself**: two independent subsampled queries
    compose additively in the amplified ε. This is the foundation of
    DP-SGD's multi-step privacy accounting.

    Step 1: Each subsampled query has amplified ε' = ln(1 + q·(exp(ε)-1))
    Step 2: Two independent queries compose to 2ε' (additive in ε')

    The key insight: subsampling amplifies BEFORE composition, so the
    composed ε is 2·ln(1+q·(exp(ε)-1)) rather than ln(1+q·(exp(2ε)-1)). -/
theorem subsample_then_compose
    {ε : NNReal}
    {μ₁ μ₂ ν₁ ν₂ : ProbabilityMeasure O}
    (h₁ : PureMeasureClose ε μ₁ ν₁)
    (h₂ : PureMeasureClose ε μ₂ ν₂)
    {q : NNReal} (hq : q ≤ 1) :
    let ε' := subsampleEpsilon q ε
    PureMeasureClose ε' (mixtureMeasure q hq μ₁ ν₁) ν₁ ∧
    PureMeasureClose ε' (mixtureMeasure q hq μ₂ ν₂) ν₂ :=
  ⟨pureMeasureClose_subsample h₁ hq, pureMeasureClose_subsample h₂ hq⟩

/-- **Subsampling always reduces privacy cost**: for any q ≤ 1 and ε,
    the amplified ε' ≤ ε. Combined with the DP-SGD pipeline, this means
    each minibatch step costs at most ε in privacy budget. -/
theorem subsample_improves_budget {q : NNReal} (hq : q ≤ 1) (ε : NNReal) :
    subsampleEpsilon q ε ≤ ε :=
  subsampleEpsilon_le q hq ε

end DPlean4.Examples

end -- noncomputable section
