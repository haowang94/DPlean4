/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Probability.Mechanism

/-!
# Adaptive (Sequential) Composition of Mechanisms

This file defines the sequential composition combinator `Mechanism.seq`, where the
second mechanism is chosen based on the output of the first. This models adaptive
algorithms like AIM, where the measurement step depends on the selection step.

## Main Definitions

* `Mechanism.seq M₁ K`: run M₁, then use its output to choose and run a second
  mechanism from the family K. Returns the pair of both outputs.

## Design Notes

The construction uses `Measure.bind` from Mathlib's Giry monad. The
`AEMeasurable` condition on the continuation is required for `bind` to be
well-defined; it is trivially satisfied for finite output types (the main
use case in DP synthetic data algorithms).

## References

* Bun & Dwork (2016), "Concentrated Differential Privacy", Lemma 1.7
* Dwork & Roth (2014), "The Algorithmic Foundations of Differential Privacy"
-/

noncomputable section

namespace DPlean4

open MeasureTheory

variable {D O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]

/-- Sequential (adaptive) composition: run M₁ on database d, then use its
    output o₁ to choose and run K(o₁) on the same database d. The result
    is the pair (o₁, o₂).

    The measure on O₁ × O₂ is constructed via `Measure.bind`:
    ∫ over o₁ from M₁(d), place the product measure δ(o₁) ⊗ K(o₁)(d)

    The `hK` hypothesis ensures the continuation is AEMeasurable, which is
    needed for `Measure.bind`. For finite O₁ with `MeasurableSingletonClass`,
    this is always trivially satisfied (every function on a discrete space
    is measurable). -/
def Mechanism.seq (M₁ : Mechanism D O₁) (K : O₁ → Mechanism D O₂)
    (hK : ∀ d, AEMeasurable (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁)) (M₁ d).toMeasure) :
    Mechanism D (O₁ × O₂) :=
  fun d => ⟨(M₁ d).toMeasure.bind (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁)),
    isProbabilityMeasure_bind (hK d) (by
      filter_upwards with o₁
      exact Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable)⟩

/-- For finite output types with `MeasurableSingletonClass`, the AEMeasurable
    condition for `Mechanism.seq` is always satisfied. -/
theorem Mechanism.seq_aemeasurable_of_finite [Fintype O₁] [MeasurableSingletonClass O₁]
    (K : O₁ → Mechanism D O₂) (M₁ : Mechanism D O₁) :
    ∀ d, AEMeasurable (fun o₁ => ((K o₁ d).toMeasure).map (Prod.mk o₁)) (M₁ d).toMeasure :=
  fun _ => (measurable_of_finite _).aemeasurable

/-- Convenient version of `Mechanism.seq` for finite output types. -/
def Mechanism.seqFinite [Fintype O₁] [MeasurableSingletonClass O₁]
    (M₁ : Mechanism D O₁) (K : O₁ → Mechanism D O₂) :
    Mechanism D (O₁ × O₂) :=
  M₁.seq K (Mechanism.seq_aemeasurable_of_finite K M₁)

end DPlean4

end -- noncomputable section
