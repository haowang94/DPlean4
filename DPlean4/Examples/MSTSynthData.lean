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

## Privacy Analysis

- Phase 1: C(d,2) = d(d-1)/2 independent Gaussian mechanisms, each ρ-zCDP → total C(d,2)·ρ
- Phase 2: k independent Gaussian mechanisms, each ρ'-zCDP → total k·ρ'
- Total: (C(d,2)·ρ + k·ρ')-zCDP by binary composition
- Convert to (ε,δ)-DP via zCDP→approxDP theorem

## References

* McKenna, Sheldon, Miklau (2021), "Winning the NIST Contest"
* Bun & Dwork (2016), "Concentrated Differential Privacy"
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

/-- **MST satisfies (ρ₁ + ρ₂)-zCDP** where ρ₁ is the MI estimation cost and
    ρ₂ is the marginal measurement cost.

    This formalization parameterizes by per-marginal noise variance v₁, v₂.
    The published MST paper parameterizes by total budget ρ₁, ρ₂ and derives
    v₁ = C(d,2)/(2ρ₁) and v₂ = (d-1)/(2ρ₂). Both are equivalent. -/
theorem mst_isZCDP {d k : ℕ} (attrs : Fin d → Attr)
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
  isZCDP_postprocess (mst_isZCDP attrs selectedMarginals hv₁ hv₂) hf

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
  isApproxDP_of_isZCDP (mst_isZCDP attrs selectedMarginals hv₁ hv₂) hρ hδ hδ1 hε

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
  mst_isZCDP attrs selected (by norm_num) (by norm_num)

end ConcreteExample

end DPlean4.Examples

end -- noncomputable section
