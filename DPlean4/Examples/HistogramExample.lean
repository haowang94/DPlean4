/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Laplace
import DPlean4.Privacy.Composition
import DPlean4.Basic.Adjacency

/-!
# Private Histogram via Parallel Composition

This file demonstrates the parallel composition theorem using a private
two-bin histogram. When a predicate partitions the data into two disjoint
groups, adding/removing one element affects exactly one bin count — so
the two noisy counts compose at max(ε₁,ε₂) instead of ε₁+ε₂.

## Key Insight (Dwork & Roth 2014, §3.5.2; McSherry 2009)

Standard composition of two ε-DP mechanisms gives 2ε-DP.
Parallel composition on disjoint data gives max(ε,ε) = ε-DP.

## References

* Dwork & Roth (2014), "The Algorithmic Foundations of Differential Privacy", §3.5.2
* McSherry (2009), "Privacy Integrated Queries" (PINQ)
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open scoped NNReal

variable {α : Type*}

-- ============================================================================
-- Sensitivity for predicate-filtered counts
-- ============================================================================

/-- Count of elements satisfying predicate p. -/
def filteredCount (p : α → Bool) (l : List α) : ℝ :=
  (l.countP p : ℝ)

/-- Count of elements NOT satisfying predicate p. -/
def filteredCountNeg (p : α → Bool) (l : List α) : ℝ :=
  (l.countP (fun x => !p x) : ℝ)

/-- Counting elements matching p has sensitivity 1 under add/remove. -/
theorem filteredCount_sens (p : α → Bool) :
    HasL1Sensitivity ListAddRemove (filteredCount p) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj
  simp only [filteredCount, NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp [Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp [Nat.cast_add, Nat.cast_one]

/-- Counting elements NOT matching p has sensitivity 1 under add/remove. -/
theorem filteredCountNeg_sens (p : α → Bool) :
    HasL1Sensitivity ListAddRemove (filteredCountNeg p) (↑(1 : ℝ≥0)) := by
  intro l₁ l₂ hadj
  simp only [filteredCountNeg, NNReal.coe_one]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp [Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp [Nat.cast_add, Nat.cast_one]

-- ============================================================================
-- Two-bin histogram mechanism
-- ============================================================================

/-- Noisy count of elements satisfying p. -/
private abbrev noisyCount (p : α → Bool) (ε : ℝ≥0) : Mechanism (List α) ℝ :=
  laplaceMech (filteredCount p) (1 : ℝ≥0) ε

/-- Noisy count of elements NOT satisfying p. -/
private abbrev noisyCountNeg (p : α → Bool) (ε : ℝ≥0) : Mechanism (List α) ℝ :=
  laplaceMech (filteredCountNeg p) (1 : ℝ≥0) ε

private theorem noisyCount_pureDP (p : α → Bool) {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsPureDP ListAddRemove (noisyCount p ε) ε :=
  laplaceMech_isPureDP hε (filteredCount_sens p)

private theorem noisyCountNeg_pureDP (p : α → Bool) {ε : ℝ≥0} (hε : ε ≠ 0) :
    IsPureDP ListAddRemove (noisyCountNeg p ε) ε :=
  laplaceMech_isPureDP hε (filteredCountNeg_sens p)

-- ============================================================================
-- Example 1: Standard (non-parallel) composition gives 2ε
-- ============================================================================

/-- **Two-bin histogram via standard composition: 2ε-DP.**

    Without parallel composition, two ε-DP mechanisms compose to 2ε-DP.
    This is correct but loose when the data is disjoint. -/
theorem histogram_standard {ε : ℝ≥0} (hε : ε ≠ 0) (p : α → Bool) :
    IsPureDP ListAddRemove
      ((noisyCount p ε).prod (noisyCountNeg p ε))
      (ε + ε) :=
  isPureDP_prod (noisyCount_pureDP p hε) (noisyCountNeg_pureDP p hε)

-- ============================================================================
-- Example 2: Parallel composition gives max(ε, ε) = ε
-- ============================================================================

/-- Adding/removing one element changes either the "positive" count or the
    "negative" count, but not both — the predicate partitions the data. -/
theorem histogram_disjoint (p : α → Bool) :
    ∀ l₁ l₂ : List α, ListAddRemove l₁ l₂ →
      noisyCount p (1 : ℝ≥0) l₁ = noisyCount p (1 : ℝ≥0) l₂ ∨
      noisyCountNeg p (1 : ℝ≥0) l₁ = noisyCountNeg p (1 : ℝ≥0) l₂ := by
  intro l₁ l₂ hadj
  simp only [noisyCount, noisyCountNeg, laplaceMech]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]
    by_cases hp : p a = true
    · right; congr 1; congr 1; simp [filteredCountNeg, List.countP_cons, hp]
    · left; congr 1; congr 1
      simp only [filteredCount, List.countP_cons]
      simp [hp]
  · rw [h.1, h.2]
    by_cases hp : p a = true
    · right; congr 1; congr 1; simp [filteredCountNeg, List.countP_cons, hp]
    · left; congr 1; congr 1
      simp only [filteredCount, List.countP_cons]
      simp [hp]

/-- **Two-bin histogram via parallel composition: ε-DP.**

    Because the predicate partitions the data, adding/removing one element
    changes only one bin. Parallel composition gives max(ε,ε) = ε, which
    is a 2× improvement over standard composition's 2ε.

    This is the key theorem demonstrating why parallel composition matters
    in practice. It applies to any histogram where the bins partition the
    data (each record falls in exactly one bin). -/
theorem histogram_parallel (p : α → Bool) :
    IsPureDP ListAddRemove
      ((noisyCount (α := α) p (1 : ℝ≥0)).prod (noisyCountNeg p (1 : ℝ≥0)))
      (max (1 : ℝ≥0) (1 : ℝ≥0)) :=
  isPureDP_parallel
    (noisyCount_pureDP p one_ne_zero)
    (noisyCountNeg_pureDP p one_ne_zero)
    (histogram_disjoint p)

end DPlean4.Examples

end -- noncomputable section
