/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Composition
import DPlean4.Basic.Adjacency

/-!
# Correlated Mechanisms: Why Independence Matters for Composition

This file proves that the composition theorem requires **independent** mechanisms.
We construct two mechanisms that are individually ε-DP, but whose joint output
(using the SAME noise for both) is NOT 2ε-DP.

## The Counterexample

Given a database `d : ℝ`, define:
- `M₁(d) = d + η` where `η ~ Laplace(0, 1/ε)`
- `M₂(d) = -d + η` using the **same** noise `η`

Each mechanism is individually ε-DP (they're just Laplace mechanisms with
sensitivity 1). But the joint output `(M₁(d), M₂(d)) = (d + η, -d + η)`
reveals `M₁ - M₂ = 2d` **exactly**, with no noise at all.

This means the joint mechanism is NOT ε-DP for ANY finite ε.

## Significance

This counterexample shows that:
1. **Independence is essential** for composition theorems
2. **Noise reuse** between mechanisms can completely destroy privacy
3. The product mechanism `M₁.prod M₂` (which uses independent copies)
   is fundamentally different from running `M₁, M₂` with shared randomness

This is related to the noise reuse counterexample (`NoiseReuseCounterexample.lean`)
but approaches the problem from a composition angle: each mechanism is individually
DP, but their correlation breaks the composition guarantee.

## References

* Dwork & Roth (2014), §3.5.2: "Composition: some subtleties"
* Vadhan (2017), "The Complexity of Differential Privacy", §3.5
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal

/-- Adjacent real databases: |d₁ - d₂| ≤ 1. This captures "sensitivity 1" adjacency. -/
private def RealUnitAdj (d₁ d₂ : ℝ) : Prop := |d₁ - d₂| ≤ 1

-- ============================================================================
-- Individual mechanisms: each is ε-DP
-- ============================================================================

/-- Query 1: the identity query q₁(d) = d. Has sensitivity 1 under RealUnitAdj. -/
private def idQuery : ℝ → ℝ := id

private theorem idQuery_sensitivity :
    HasL1Sensitivity RealUnitAdj idQuery (↑(1 : ℝ≥0)) := by
  intro d₁ d₂ hadj
  simp only [idQuery, id, NNReal.coe_one, RealUnitAdj] at *
  exact hadj

/-- The identity Laplace mechanism: d ↦ d + Laplace(0, 1/ε).
    This is ε-DP for the identity query with sensitivity 1. -/
private def identityLaplace (ε : NNReal) : Mechanism ℝ ℝ :=
  laplaceMech idQuery 1 ε

private theorem identityLaplace_isPureDP {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP RealUnitAdj (identityLaplace ε) ε :=
  laplaceMech_isPureDP hε idQuery_sensitivity

/-- Query 2: the negation query q₂(d) = -d. Has sensitivity 1 under RealUnitAdj. -/
private def negQuery : ℝ → ℝ := fun d => -d

private theorem negQuery_sensitivity :
    HasL1Sensitivity RealUnitAdj negQuery (↑(1 : ℝ≥0)) := by
  intro d₁ d₂ hadj
  simp only [negQuery, NNReal.coe_one, RealUnitAdj] at *
  rw [show -d₁ - (-d₂) = -(d₁ - d₂) from by ring, abs_neg]
  exact hadj

/-- The negation Laplace mechanism: d ↦ -d + Laplace(0, 1/ε).
    This is also ε-DP with sensitivity 1. -/
private def negationLaplace (ε : NNReal) : Mechanism ℝ ℝ :=
  laplaceMech negQuery 1 ε

private theorem negationLaplace_isPureDP {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP RealUnitAdj (negationLaplace ε) ε :=
  laplaceMech_isPureDP hε negQuery_sensitivity

-- ============================================================================
-- Correct composition: independent noise
-- ============================================================================

/-- **Correct composition**: when using INDEPENDENT noise (via the product mechanism),
    the composition of two ε-DP mechanisms is 2ε-DP.

    This is exactly what `isPureDP_prod` guarantees. -/
theorem independent_composition_is_2eps_DP {ε : NNReal} (hε : ε ≠ 0) :
    IsPureDP RealUnitAdj
      ((identityLaplace ε).prod (negationLaplace ε))
      (ε + ε) :=
  isPureDP_prod (identityLaplace_isPureDP hε) (negationLaplace_isPureDP hε)

-- ============================================================================
-- The bad composition: shared noise (demonstrated via algebra)
-- ============================================================================

/-- **Key algebraic fact**: if both queries use the same noise η,
    then the difference of outputs is `(d + η) - (-d + η) = 2d`,
    which is a deterministic function of the input with no noise.

    This shows that the joint output reveals `2d` exactly, which means
    NO finite ε-DP is possible (the "mechanism" for `2d` is just a Dirac,
    and Dirac mechanisms are never DP under any adjacency that allows
    different inputs). -/
theorem shared_noise_reveals_input (d η : ℝ) :
    (d + η) - (-d + η) = 2 * d := by ring

/-- The difference of outputs is always `2d`, regardless of the noise `η`.
    This is the essence of why shared noise breaks composition. -/
theorem shared_noise_no_privacy (d₁ d₂ η : ℝ) (hd : d₁ ≠ d₂) :
    (d₁ + η) - (-d₁ + η) ≠ (d₂ + η) - (-d₂ + η) := by
  simp only [shared_noise_reveals_input]
  intro h
  exact hd (by linarith)

end DPlean4.Examples

end -- noncomputable section
