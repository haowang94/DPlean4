/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Composition
import DPlean4.Privacy.Postprocessing
import DPlean4.Basic.Adjacency

/-!
# Composition Examples from the DP Literature

This file demonstrates composing privacy mechanisms — a core pattern
in differential privacy deployments.

## Results

* `three_laplace_pipeline`: Three independent ε-DP mechanisms compose to 3ε-DP
* `compose_then_postprocess`: Product composition + measurable postprocessing
* `approxDP_compose_explicit_delta`: Approximate DP product composition with
  explicit δ bound (exp(ε₂)·δ₁ + δ₂)

## References

* Dwork & Roth, "The Algorithmic Foundations of Differential Privacy" (2014)
  — basic composition theorem (Theorem 3.16)
* Dwork, Rothblum, Vadhan, "Boosting and Differential Privacy" (2010)
  — advanced composition
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open scoped NNReal ENNReal

variable {α : Type*}

private theorem countQuery_sens'' :
    HasL1Sensitivity ListHeadAddRemove (fun (l : List α) => (l.length : ℝ)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj
  simp only [NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj <;> rw [h.1, h.2] <;>
    simp [List.length_cons, Nat.cast_add, Nat.cast_one]

private abbrev countLaplace : Mechanism (List α) ℝ :=
  laplaceMech (fun l => (l.length : ℝ)) (1 : ℝ≥0) (1 : ℝ≥0)

private theorem countLaplace_pureDP :
    IsPureDP ListHeadAddRemove (countLaplace (α := α)) (1 : ℝ≥0) :=
  laplaceMech_isPureDP one_ne_zero countQuery_sens''

-- ============================================================================
-- Example 1: Three-mechanism pipeline (Dwork & Roth 2014, Theorem 3.16)
-- ============================================================================

/-- **Three independent Laplace mechanisms composed via iterated products.**

    M₁ ⊗ M₂ ⊗ M₃ : D → (ℝ × ℝ) × ℝ

    Each mechanism is 1-DP (pure), so the triple product is 3-DP.
    Demonstrates that pure DP composition scales linearly. -/
theorem three_laplace_pipeline :
    IsPureDP ListHeadAddRemove
      ((countLaplace (α := α)).prod countLaplace |>.prod countLaplace)
      ((1 : ℝ≥0) + (1 : ℝ≥0) + (1 : ℝ≥0)) :=
  isPureDP_prod (isPureDP_prod countLaplace_pureDP countLaplace_pureDP) countLaplace_pureDP

-- ============================================================================
-- Example 2: Composition + postprocessing (Report Noisy Max pattern)
-- ============================================================================

/-- **Compose two Laplace mechanisms, then postprocess with max.**

    Pipeline: (M₁(d), M₂(d)) ↦ max(M₁(d), M₂(d))

    Takes the maximum of two noisy counts. The composition gives 2-DP,
    and postprocessing with max (measurable) preserves the 2-DP bound.

    This pattern appears in "report noisy max" algorithms
    (Dwork & Roth 2014, Algorithm 2). -/
theorem compose_then_postprocess :
    IsPureDP ListHeadAddRemove
      (fun (d : List α) =>
        (countLaplace.prod countLaplace d).map
          (Measurable.max measurable_fst measurable_snd).aemeasurable)
      ((1 : ℝ≥0) + (1 : ℝ≥0)) :=
  isPureDP_postprocess
    (isPureDP_prod countLaplace_pureDP countLaplace_pureDP)
    (Measurable.max measurable_fst measurable_snd)

-- ============================================================================
-- Example 3: Approximate DP product composition
-- ============================================================================

/-- **Two approximate DP mechanisms compose with explicit δ bound.**

    Two independent (1,δ)-DP Laplace mechanisms compose to
    (2, exp(1)·δ + δ)-DP via the Fubini-based composition proof.

    This exercises the `isApproxDP_prod` theorem from Composition.lean.
    The δ bound exp(ε₂)·δ₁+δ₂ tracks how privacy degradation accumulates
    through the Fubini integration steps. -/
theorem approxDP_compose_explicit_delta (δ : NNReal) :
    IsApproxDP ListHeadAddRemove
      ((countLaplace (α := α)).prod countLaplace)
      ((1 : ℝ≥0) + (1 : ℝ≥0))
      (⟨Real.exp ↑(1 : ℝ≥0), Real.exp_nonneg _⟩ * δ + δ) :=
  isApproxDP_prod
    (isApproxDP_of_isPureDP δ countLaplace_pureDP)
    (isApproxDP_of_isPureDP δ countLaplace_pureDP)

-- ============================================================================
-- Example 4: Composition preserves group privacy
-- ============================================================================

/-- **Group privacy for composed mechanisms.**

    If two databases are 2-hop apart (d₁ ~ d₂ ~ d₃), then the composed
    Laplace mechanism satisfies (2·(1+1))-close bound for d₁ vs d₃.

    Combines composition (ε₁+ε₂) and group privacy (k·ε). -/
theorem compose_group_privacy {l₁ l₂ l₃ : List α}
    (h₁₂ : ListHeadAddRemove l₁ l₂) (h₂₃ : ListHeadAddRemove l₂ l₃) :
    PureMeasureClose (((1 : ℝ≥0) + (1 : ℝ≥0)) + ((1 : ℝ≥0) + (1 : ℝ≥0)))
      (countLaplace.prod countLaplace l₁)
      (countLaplace.prod countLaplace l₃) :=
  isPureDP_group_2
    (isPureDP_prod countLaplace_pureDP countLaplace_pureDP)
    h₁₂ h₂₃

end DPlean4.Examples

end -- noncomputable section
