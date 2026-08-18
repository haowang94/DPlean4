/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Mechanism.Gaussian
import DPlean4.Privacy.Composition
import DPlean4.Privacy.ZCDP
import DPlean4.Privacy.RenyiDP
import DPlean4.Basic.Adjacency

/-!
# Independent Gaussian Composition via zCDP

This file demonstrates independent product composition. It does not formalize
the adaptive advanced-composition theorem.

## Background

**Basic composition** (Dwork & Roth 2014, Theorem 3.16):
- k mechanisms, each ε-DP → kε-DP (linear scaling)

**Advanced composition** (Dwork, Rothblum, Vadhan 2010):
- k mechanisms, each ε₀-DP → (ε₀√(2k·ln(1/δ)) + kε₀(e^ε₀-1), kδ₀+δ)-DP

The zCDP accounting route is:
1. Each mechanism has ρ-zCDP (e.g., Gaussian with ρ = Δ²/(2v))
2. k-fold composition gives kρ-zCDP (linear in ρ)
3. Convert to (ε,δ)-DP: ε = kρ + 2√(kρ·ln(1/δ))
4. The result contains both a linear and a square-root term; the linear term
   eventually dominates as k grows

## Examples in This File

* Basic composition: 4 Laplace queries → 4ε-DP
* Independent composition via zCDP: 4 Gaussian queries
* RDP view of the same composition

## References

* Dwork, Rothblum, Vadhan (2010), "Boosting and Differential Privacy"
* Bun & Dwork (2016), "Concentrated Differential Privacy"
* Mironov (2017), "Rényi Differential Privacy"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*}

-- ============================================================================
-- Setup: counting query
-- ============================================================================

private def countQ (l : List α) : ℝ := (l.length : ℝ)

private theorem countQ_sensitivity :
    HasL1Sensitivity ListHeadAddRemove (countQ (α := α)) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj; simp only [countQ, NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

-- ============================================================================
-- Basic Composition: 4 Laplace queries → 4ε-DP (linear scaling)
-- ============================================================================

/-- **Basic composition**: 4 independent Laplace counting queries compose to 4ε-DP.
    This is the naïve bound — privacy cost grows linearly with k. -/
theorem basic_composition_4_laplace {ε : NNReal} (hε : ε ≠ 0) :
    let M := laplaceMech (D := List α) countQ 1 ε
    IsPureDP ListHeadAddRemove (M.prod M |>.prod (M.prod M)) ((ε + ε) + (ε + ε)) := by
  intro M
  exact isPureDP_prod
    (isPureDP_prod (laplaceMech_isPureDP hε countQ_sensitivity)
                   (laplaceMech_isPureDP hε countQ_sensitivity))
    (isPureDP_prod (laplaceMech_isPureDP hε countQ_sensitivity)
                   (laplaceMech_isPureDP hε countQ_sensitivity))

-- ============================================================================
-- Independent composition via zCDP: 4 Gaussian queries
-- ============================================================================

/-- **zCDP composition**: 2 Gaussian counting queries compose to 2ρ-zCDP. -/
theorem two_gaussian_queries_zCDP' {v : ℝ≥0} (hv : v ≠ 0) :
    let M := gaussianMech (D := List α) countQ v
    let ρ := (1 : ℝ≥0) ^ 2 / (2 * v)
    IsZCDP ListHeadAddRemove (M.prod M) (ρ + ρ) :=
  isZCDP_prod (gaussianMech_isZCDP hv countQ_sensitivity.toL2)
    (gaussianMech_isZCDP hv countQ_sensitivity.toL2)

/-- **zCDP composition**: 4 Gaussian counting queries compose to 4ρ-zCDP.
    With ρ = Δ²/(2v) = 1/(2v), total is 4/(2v) = 2/v.
    The key: zCDP composes *linearly in ρ*, not in ε. -/
theorem four_gaussian_queries_zCDP {v : ℝ≥0} (hv : v ≠ 0) :
    let M := gaussianMech (D := List α) countQ v
    let ρ := (1 : ℝ≥0) ^ 2 / (2 * v)
    IsZCDP ListHeadAddRemove (M.prod M |>.prod (M.prod M)) ((ρ + ρ) + (ρ + ρ)) := by
  intro M ρ
  have hM := gaussianMech_isZCDP (D := List α) hv countQ_sensitivity.toL2
  exact isZCDP_prod (isZCDP_prod hM hM) (isZCDP_prod hM hM)

/-- **zCDP → (ε,δ)-DP conversion**: after 4 Gaussian queries,
    the (ε,δ)-DP bound has ε = 4ρ + 2√(4ρ · ln(1/δ)).

    Compare: basic composition gives 4ε₀ (linear in k=4).
    zCDP gives exactly the displayed linear-plus-square-root expression.

    This existential form guarantees that *some* ε achieves (ε,δ)-DP. -/
theorem four_gaussian_queries_approxDP {v : ℝ≥0} (hv : v ≠ 0)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) :
    let M := gaussianMech (D := List α) countQ v
    let ρ := (1 : ℝ≥0) ^ 2 / (2 * v)
    ∃ ε : NNReal, IsApproxDP ListHeadAddRemove (M.prod M |>.prod (M.prod M)) ε δ := by
  intro M ρ
  exact isApproxDP_of_isZCDP' (four_gaussian_queries_zCDP (α := α) hv)
    (by positivity) hδ hδ1

-- ============================================================================
-- RDP view: 4 Gaussian queries at each order α
-- ============================================================================

/-- The same 4 Gaussian queries viewed through the RDP lens: (α, 4ρα)-RDP
    for every order α > 1. This is the basis for the optimal (ε,δ)-DP
    conversion (optimize over α). -/
theorem four_gaussian_queries_isRenyiDP {v : ℝ≥0} (hv : v ≠ 0) {a : ℝ} (ha : 1 < a) :
    let M := gaussianMech (D := List α) countQ v
    let ρ := (1 : ℝ≥0) ^ 2 / (2 * v)
    IsRenyiDP ListHeadAddRemove (M.prod M |>.prod (M.prod M))
      a ((((ρ + ρ) + (ρ + ρ) : ℝ≥0) : ℝ) * a) :=
  isRenyiDP_of_isZCDP (four_gaussian_queries_zCDP hv) ha

-- ============================================================================
-- Concrete comparison: v=2, ρ=1/4 per query
-- ============================================================================

/-- Concrete example with v=2: each query has ρ = 1/(2·2) = 1/4.
    After 4 queries, total ρ = 4·(1/4) = 1, giving
    ε = 1 + 2√(ln(1/δ)) via zCDP → (ε,δ)-DP conversion.

    In contrast, basic composition of 4 (ε₀,δ₀)-DP queries gives 4ε₀.
    The converted zCDP bound contains both `kρ` and a square-root term. -/
theorem four_gaussian_v2_zCDP :
    let M := gaussianMech (D := List α) countQ (2 : ℝ≥0)
    let ρ := (1 : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0))
    IsZCDP ListHeadAddRemove (M.prod M |>.prod (M.prod M)) ((ρ + ρ) + (ρ + ρ)) :=
  four_gaussian_queries_zCDP (by norm_num)

end DPlean4.Examples

end -- noncomputable section
