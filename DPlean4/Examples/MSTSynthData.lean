/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.VectorGaussian
import DPlean4.Privacy.ZCDP
import DPlean4.Basic.TabularData

/-!
# MST: Maximum Spanning Tree Algorithm for DP Synthetic Data

This file formalizes the privacy analysis of the MST algorithm
(McKenna, Sheldon, Miklau 2021), a standard method for differentially private
synthetic data generation.

## Algorithm Overview

MST follows the Select-Measure-Generate paradigm:

1. **Phase 1 (Measure MI)**: Measure all pairwise 2-way marginals using Gaussian
   mechanism to estimate mutual information. Budget: ρ₁-zCDP.
2. **Select (post-processing)**: Compute noisy mutual information from Phase 1
   output. Build maximum spanning tree. No privacy cost.
3. **Phase 2 (Measure selected marginals)**: Measure the selected 2-way marginals
   using Gaussian mechanism. Budget: ρ₂-zCDP.
4. **Generate (post-processing)**: Fit a graphical model (Private-PGM) to noisy
   marginals and sample synthetic data. No privacy cost.

## Scope of this formalization

The prose above describes the full MST algorithm, in which the Phase-2 selection
is **data-dependent** on the noisy Phase-1 output. The theorems in this file do
**not** yet model that dependence: `mstMeasurePhase`/`mstFixedSelection_isZCDP` take
`selectedMarginals` as a *fixed parameter* and compose the two phases with the
non-adaptive product rule (`isZCDP_prod`). The stated bound is correct for any
fixed selection, but it is not a proof of the end-to-end data-dependent pipeline.
Faithfully capturing data-dependent selection requires modelling Phase 2 as a
continuation of Phase 1's output and composing with the adaptive rule
`isZCDP_seq` (`DPlean4/Privacy/ZCDP.lean`); this is done in `mstAdaptive_isZCDP`
below, which is the faithful data-dependent select-measure formalization.

## Privacy Analysis

- Phase 1: C(d,2) = d(d-1)/2 independent Gaussian mechanisms, each ρ-zCDP → total C(d,2)·ρ
- Phase 2: k independent Gaussian mechanisms, each ρ'-zCDP → total k·ρ'
- Total: (C(d,2)·ρ + k·ρ')-zCDP by binary composition
- Convert to (ε,δ)-DP via zCDP→approxDP theorem

## References

* McKenna, Sheldon, Miklau (2021), "Winning the NIST Contest"
* Bun & Steinke (2016), "Concentrated Differential Privacy: Simplifications,
  Extensions, and Lower Bounds"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory
open scoped NNReal ENNReal

variable {Attr : Type*} {dom : Attr → Type*} [∀ a, DecidableEq (dom a)]

-- ============================================================================
-- Phase 1: Measure all pairwise marginals (for MI estimation)
-- ============================================================================

/-- Phase 1 of MST: measure all C(d,2) distinct unordered pairs of attributes
    using vector Gaussian mechanism. The published MST algorithm measures only
    pairs (i,j) with i < j, not all d² ordered pairs. -/
def mstMIPhase {d : ℕ} (attrs : Fin d → Attr)
    [∀ i, Fintype (dom (attrs i))]
    (v₁ : ℝ≥0) :
    Mechanism (TabularDataset Attr dom)
      (∀ p : {p : Fin d × Fin d // p.1 < p.2},
        dom (attrs p.val.1) × dom (attrs p.val.2) → ℝ) :=
  Mechanism.pi (fun p =>
    vectorGaussianMech (marginalVector2 (attrs p.val.1) (attrs p.val.2)) v₁)

/-- Phase 1 is ρ₁-zCDP where ρ₁ = C(d,2) / (2·v₁). -/
theorem mstMIPhase_isZCDP {d : ℕ} (attrs : Fin d → Attr)
    [∀ i, Fintype (dom (attrs i))]
    {v₁ : ℝ≥0} (hv₁ : v₁ ≠ 0) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      (mstMIPhase attrs v₁)
      (∑ _ : {p : Fin d × Fin d // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * v₁)) :=
  isZCDP_pi (fun p =>
    vectorGaussianMech_isZCDP hv₁ (marginalVector2_L2Sensitivity (attrs p.val.1) (attrs p.val.2)))

-- ============================================================================
-- Phase 2: Measure selected marginals
-- ============================================================================

/-- Phase 2 of MST: measure `k` selected 2-way marginals using vector Gaussian.
    The selection is parameterized — the privacy bound holds for ANY choice. -/
def mstMeasurePhase {k : ℕ} (selectedMarginals : Fin k → Attr × Attr)
    [∀ i, Fintype (dom (selectedMarginals i).1)]
    [∀ i, Fintype (dom (selectedMarginals i).2)]
    (v₂ : ℝ≥0) :
    Mechanism (TabularDataset Attr dom)
      (∀ i : Fin k, dom (selectedMarginals i).1 × dom (selectedMarginals i).2 → ℝ) :=
  Mechanism.pi (fun i =>
    vectorGaussianMech (marginalVector2 (selectedMarginals i).1 (selectedMarginals i).2) v₂)

/-- Phase 2 is ρ₂-zCDP where ρ₂ = k / (2·v₂). -/
theorem mstMeasurePhase_isZCDP {k : ℕ} (selectedMarginals : Fin k → Attr × Attr)
    [∀ i, Fintype (dom (selectedMarginals i).1)]
    [∀ i, Fintype (dom (selectedMarginals i).2)]
    {v₂ : ℝ≥0} (hv₂ : v₂ ≠ 0) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      (mstMeasurePhase selectedMarginals v₂)
      (∑ _ : Fin k, (1 : ℝ≥0) ^ 2 / (2 * v₂)) :=
  isZCDP_pi (fun i =>
    vectorGaussianMech_isZCDP hv₂
      (marginalVector2_L2Sensitivity (selectedMarginals i).1 (selectedMarginals i).2))

-- ============================================================================
-- Full MST Privacy Theorem
-- ============================================================================

/-- **MST with a fixed marginal selection satisfies (ρ₁ + ρ₂)-zCDP**, where ρ₁ is
    the MI estimation cost and ρ₂ is the marginal measurement cost.

    Note (scope): `selectedMarginals` here is a *fixed parameter*, and the two
    phases are composed with the non-adaptive product rule. The bound holds for
    any fixed selection, but this is not the end-to-end data-dependent MST
    pipeline (which would select from the noisy Phase-1 output and require
    adaptive composition via `isZCDP_seq`). See the module docstring.

    This formalization parameterizes by per-marginal noise variance v₁, v₂.
    The published MST paper parameterizes by total budget ρ₁, ρ₂ and derives
    v₁ = C(d,2)/(2ρ₁) and v₂ = (d-1)/(2ρ₂). Both are equivalent. -/
theorem mstFixedSelection_isZCDP {d k : ℕ} (attrs : Fin d → Attr)
    [∀ i, Fintype (dom (attrs i))]
    (selectedMarginals : Fin k → Attr × Attr)
    [∀ i, Fintype (dom (selectedMarginals i).1)]
    [∀ i, Fintype (dom (selectedMarginals i).2)]
    {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      ((mstMIPhase attrs v₁).prod (mstMeasurePhase selectedMarginals v₂))
      ((∑ _ : {p : Fin d × Fin d // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * v₁)) +
       (∑ _ : Fin k, (1 : ℝ≥0) ^ 2 / (2 * v₂))) :=
  isZCDP_prod (mstMIPhase_isZCDP attrs hv₁)
    (mstMeasurePhase_isZCDP selectedMarginals hv₂)

/-- **Adaptive MST is (ρ₁ + ρ₂)-zCDP.**

    This is the faithful *data-dependent* formalization. Phase 1 (`mstMIPhase`)
    produces the noisy pairwise measurements `o₁`, and the continuation `K` uses
    `o₁` to **select** which marginals to measure and then measures them. Selection
    is arbitrary post-processing of `o₁` (no privacy cost), and the modelling
    assumption is that for *every* first-stage output `o₁` the resulting Phase-2
    measurement is uniformly `ρ₂`-zCDP (`hK_zcdp`) — which holds for MST because
    the Gaussian measurement cost is the same regardless of which marginals were
    selected. Adaptive composition (`isZCDP_seq`) then yields the `(ρ₁ + ρ₂)`
    bound for the genuinely sequential mechanism `mstMIPhase.seq K`.

    Unlike `mstFixedSelection_isZCDP`, the selection here is a function of the
    Phase-1 output, so this captures the real select-measure pipeline.

    The hypotheses `hK`, `hK_meas` are the standard Markov-kernel regularity
    conditions on the continuation (measurability of the kernel `o₁ ↦ K o₁`);
    for a finite first-stage output type they are automatic (`isZCDP_seqFinite`),
    but Phase 1's output here is continuous, so they are supplied explicitly. -/
theorem mstAdaptive_isZCDP {d : ℕ} (attrs : Fin d → Attr)
    [∀ i, Fintype (dom (attrs i))]
    {O₂ : Type*} [MeasurableSpace O₂]
    [MeasurableSpace.CountableOrCountablyGenerated
      (∀ p : {p : Fin d × Fin d // p.1 < p.2},
        dom (attrs p.val.1) × dom (attrs p.val.2) → ℝ) O₂]
    (K : (∀ p : {p : Fin d × Fin d // p.1 < p.2},
          dom (attrs p.val.1) × dom (attrs p.val.2) → ℝ) →
        Mechanism (TabularDataset Attr dom) O₂)
    {v₁ : ℝ≥0} (hv₁ : v₁ ≠ 0) {ρ₂ : NNReal}
    (hK_zcdp : ∀ o₁, IsZCDP (@ListHeadAddRemove (TabularRow Attr dom)) (K o₁) ρ₂)
    (hK : ∀ dd, AEMeasurable
      (fun o₁ => ((K o₁ dd).toMeasure).map (Prod.mk o₁))
      ((mstMIPhase attrs v₁) dd).toMeasure)
    (hK_meas : ∀ dd, Measurable (fun o₁ => (K o₁ dd).toMeasure)) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      ((mstMIPhase attrs v₁).seq K hK)
      ((∑ _ : {p : Fin d × Fin d // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * v₁)) + ρ₂) :=
  isZCDP_seq (mstMIPhase_isZCDP attrs hv₁) hK_zcdp hK hK_meas

/-- MST with post-processing still satisfies the same zCDP bound. -/
theorem mst_postprocess_isZCDP {d k : ℕ} (attrs : Fin d → Attr)
    [∀ i, Fintype (dom (attrs i))]
    (selectedMarginals : Fin k → Attr × Attr)
    [∀ i, Fintype (dom (selectedMarginals i).1)]
    [∀ i, Fintype (dom (selectedMarginals i).2)]
    {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    {S : Type*} [MeasurableSpace S] {f : _ → S} (hf : Measurable f) :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      (fun d => ((mstMIPhase attrs v₁).prod (mstMeasurePhase selectedMarginals v₂) d).map
        hf.aemeasurable)
      ((∑ _ : {p : Fin d × Fin d // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * v₁)) +
       (∑ _ : Fin k, (1 : ℝ≥0) ^ 2 / (2 * v₂))) :=
  isZCDP_postprocess (mstFixedSelection_isZCDP attrs selectedMarginals hv₁ hv₂) hf

/-- **MST satisfies (ε,δ)-approximate DP** via the zCDP → approxDP conversion. -/
theorem mst_isApproxDP {d k : ℕ} (attrs : Fin d → Attr)
    [∀ i, Fintype (dom (attrs i))]
    (selectedMarginals : Fin k → Attr × Attr)
    [∀ i, Fintype (dom (selectedMarginals i).1)]
    [∀ i, Fintype (dom (selectedMarginals i).2)]
    {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    {ε δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hρ : 0 < ((∑ _ : {p : Fin d × Fin d // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * v₁)) +
               (∑ _ : Fin k, (1 : ℝ≥0) ^ 2 / (2 * v₂))))
    (hε : (ε : ℝ) ≥
          ↑((∑ _ : {p : Fin d × Fin d // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * v₁)) +
            (∑ _ : Fin k, (1 : ℝ≥0) ^ 2 / (2 * v₂)) : ℝ≥0) +
          2 * Real.sqrt (↑((∑ _ : {p : Fin d × Fin d // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * v₁)) +
              (∑ _ : Fin k, (1 : ℝ≥0) ^ 2 / (2 * v₂)) : ℝ≥0) *
            Real.log (1 / ↑δ))) :
    IsApproxDP (@ListHeadAddRemove (TabularRow Attr dom))
      ((mstMIPhase attrs v₁).prod (mstMeasurePhase selectedMarginals v₂)) ε δ :=
  isApproxDP_of_isZCDP (mstFixedSelection_isZCDP attrs selectedMarginals hv₁ hv₂) hρ hδ hδ1 hε

-- ============================================================================
-- Concrete Example: 5-attribute dataset
-- ============================================================================

section ConcreteExample

/-- Concrete MST example: 5 binary attributes, noise variance v=100.

    Phase 1: C(5,2) = 10 pairwise measurements, each 1/(2·100) = 0.005 zCDP
    Phase 2: 4 selected marginals (MST has d-1 = 4 edges), each 0.005 zCDP
    Total: 10 · 0.005 + 4 · 0.005 = 0.05 + 0.02 = 0.07 zCDP -/
example (attrs : Fin 5 → Attr) [∀ i, Fintype (dom (attrs i))]
    (selected : Fin 4 → Attr × Attr)
    [∀ i, Fintype (dom (selected i).1)]
    [∀ i, Fintype (dom (selected i).2)] :
    IsZCDP (@ListHeadAddRemove (TabularRow Attr dom))
      ((mstMIPhase attrs (100 : ℝ≥0)).prod (mstMeasurePhase selected (100 : ℝ≥0)))
      ((∑ _ : {p : Fin 5 × Fin 5 // p.1 < p.2}, (1 : ℝ≥0) ^ 2 / (2 * 100)) +
       (∑ _ : Fin 4, (1 : ℝ≥0) ^ 2 / (2 * 100))) :=
  mstFixedSelection_isZCDP attrs selected (by norm_num) (by norm_num)

end ConcreteExample

end DPlean4.Examples

end -- noncomputable section
