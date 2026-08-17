/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Privacy.Approximate
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Postprocessing Theorem for Differential Privacy

If a mechanism M satisfies (ε,δ)-DP and f is a measurable function, then f ∘ M
(applying f to the output of M) also satisfies (ε,δ)-DP.

This is a fundamental property: arbitrary data-independent postprocessing cannot
degrade privacy.

## Proof Strategy

For any measurable set S in the output of f, the preimage f⁻¹(S) is measurable.
The DP inequality for M on f⁻¹(S) gives the DP inequality for f ∘ M on S.
-/

namespace DPlean4

open MeasureTheory

variable {D O O' : Type*} [MeasurableSpace O] [MeasurableSpace O']

/-- Postprocessing at the measure level: if μ ≤[ε,δ] ν, then
    μ.map f ≤[ε,δ] ν.map f for any measurable f.

    ProbabilityMeasure.map takes an AEMeasurable proof; Measurable implies AEMeasurable. -/
theorem measureClose_map {ε δ : NNReal} {μ ν : ProbabilityMeasure O}
    (h : MeasureClose ε δ μ ν) {f : O → O'} (hf : Measurable f) :
    MeasureClose ε δ (μ.map hf.aemeasurable) (ν.map hf.aemeasurable) := by
  intro s hs
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
  exact h (f ⁻¹' s) (hf hs)

/-- Postprocessing for pure DP at the measure level. -/
theorem pureMeasureClose_map {ε : NNReal} {μ ν : ProbabilityMeasure O}
    (h : PureMeasureClose ε μ ν) {f : O → O'} (hf : Measurable f) :
    PureMeasureClose ε (μ.map hf.aemeasurable) (ν.map hf.aemeasurable) :=
  measureClose_map h hf

/-- Postprocessing theorem for approximate DP:
    If M is (ε,δ)-DP and f is measurable, then (fun d => (M d).map f) is (ε,δ)-DP.

    This is the standard postprocessing theorem from Dwork & Roth. -/
theorem isApproxDP_postprocess {adj : D → D → Prop} {M : Mechanism D O} {ε δ : NNReal}
    (hM : IsApproxDP adj M ε δ) {f : O → O'} (hf : Measurable f) :
    IsApproxDP adj (fun d => (M d).map hf.aemeasurable) ε δ := by
  intro d₁ d₂ hadj
  exact measureClose_map (hM d₁ d₂ hadj) hf

/-- Postprocessing theorem for pure DP:
    If M is ε-DP and f is measurable, then (fun d => (M d).map f) is ε-DP. -/
theorem isPureDP_postprocess {adj : D → D → Prop} {M : Mechanism D O} {ε : NNReal}
    (hM : IsPureDP adj M ε) {f : O → O'} (hf : Measurable f) :
    IsPureDP adj (fun d => (M d).map hf.aemeasurable) ε := by
  intro d₁ d₂ hadj
  exact pureMeasureClose_map (hM d₁ d₂ hadj) hf

end DPlean4
