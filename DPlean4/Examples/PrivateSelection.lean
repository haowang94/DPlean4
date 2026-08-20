/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Mechanism.Exponential
import DPlean4.Mechanism.ReportNoisyMax
import DPlean4.Basic.Adjacency

/-!
# Private Selection: Choosing the Best Option with Differential Privacy

This file demonstrates the private selection problem and its solution via the
exponential mechanism. Private selection is a fundamental DP primitive used in:
- Hyperparameter tuning (Chaudhuri & Vempala 2011, Liu & Talwar 2019)
- Private model selection
- Private feature selection
- Report Noisy Max (Dwork & Roth 2014, §3.4)

## The Problem

Given n scoring functions (e.g., accuracy of n candidate models on a private
dataset), select the index of the highest-scoring option while preserving DP.

## Key Insight

This is exactly the exponential mechanism with utility u(d, i) = scoreᵢ(d),
giving ε-DP regardless of the number of candidates n. The privacy cost does
NOT scale with n — a non-obvious but crucial property.

## Examples

1. **Private model selection**: Choose the best ML model from a set of candidates
   based on private validation accuracy.
2. **Private feature selection**: Choose the most informative feature from a
   set of candidate features based on a private dataset.

## References

* Dwork & Roth (2014), §3.4: Report Noisy Max and the Exponential Mechanism
* McSherry & Talwar (2007), "Mechanism Design via Differential Privacy"
-/

noncomputable section

namespace DPlean4.Examples

open DPlean4
open scoped NNReal

variable {α : Type*}

-- ============================================================================
-- Private model selection
-- ============================================================================

/-- A model scoring function: evaluates how well model i performs on database d.
    Each modelScore i : List α → ℝ returns the score of model i on database d. -/
def modelScore {n : ℕ} (scores : Fin n → List α → ℝ) : List α → Fin n → ℝ :=
  fun d i => scores i d

/-- If each model's score has L1 sensitivity at most Δ (e.g., each score is
    a count or average over the dataset), then the utility function for
    private selection has utility sensitivity Δ. -/
theorem modelScore_sensitivity {n : ℕ} {scores : Fin n → List α → ℝ} {Δ : ℝ≥0}
    (hsens : ∀ i, HasL1Sensitivity ListHeadAddRemove (scores i) Δ) :
    HasUtilitySensitivity ListHeadAddRemove (modelScore scores) Δ := by
  intro d₁ d₂ hadj i
  exact hsens i d₁ d₂ hadj

/-- Private model selection mechanism: given n ≥ 1 models with scoring functions,
    privately select the best one using the exponential mechanism. -/
def privateModelSelect {n : ℕ} [Nonempty (Fin n)] (scores : Fin n → List α → ℝ)
    (ε : NNReal) (Δ : ℝ≥0) : Mechanism (List α) (Fin n) :=
  reportNoisyMax scores ε Δ

/-- **Private model selection is ε-DP.**

    The privacy cost is ε regardless of the number of models n.
    This is a direct consequence of the exponential mechanism theorem.

    Note: ε does NOT depend on n! Adding more candidate models does not
    increase the privacy cost. This is why the exponential mechanism is
    so powerful for selection problems. -/
theorem privateModelSelect_isPureDP {n : ℕ} [Nonempty (Fin n)]
    {scores : Fin n → List α → ℝ}
    {Δ : ℝ≥0} (hΔ : Δ ≠ 0) {ε : NNReal}
    (hsens : ∀ i, HasL1Sensitivity ListHeadAddRemove (scores i) Δ) :
    IsPureDP ListHeadAddRemove (privateModelSelect scores ε Δ) ε :=
  reportNoisyMax_isPureDP hΔ hsens

-- ============================================================================
-- Concrete example: selecting from 3 models
-- ============================================================================

/-- Concrete scoring functions for 3 models, each computing a different
    count-based statistic on the database. -/
private def score₁ (l : List ℕ) : ℝ := (l.length : ℝ)
private def score₂ (l : List ℕ) : ℝ := (l.countP (· > 5) : ℝ)
private def score₃ (l : List ℕ) : ℝ := (l.countP (· ≤ 5) : ℝ)

private def threeScores : Fin 3 → List ℕ → ℝ :=
  ![score₁, score₂, score₃]

private theorem score₁_sens : HasL1Sensitivity ListHeadAddRemove score₁ 1 := by
  intro l₁ l₂ hadj; simp only [score₁]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.length_cons, Nat.cast_add, Nat.cast_one]

private theorem score₂_sens : HasL1Sensitivity ListHeadAddRemove score₂ 1 := by
  intro l₁ l₂ hadj; simp only [score₂]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp [Nat.cast_add, Nat.cast_one]
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp [Nat.cast_add, Nat.cast_one]

private theorem score₃_sens : HasL1Sensitivity ListHeadAddRemove score₃ 1 := by
  intro l₁ l₂ hadj; simp only [score₃]
  obtain ⟨a, s, h⟩ | ⟨a, s, h⟩ := hadj
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp
  · rw [h.1, h.2]; simp [List.countP_cons]; split <;> simp

/-- Each of the 3 scoring functions has sensitivity 1 under add/remove. -/
private theorem threeScores_sensitivity :
    ∀ i : Fin 3, HasL1Sensitivity ListHeadAddRemove (threeScores i) 1 := by
  intro i; fin_cases i
  · exact score₁_sens
  · exact score₂_sens
  · exact score₃_sens

/-- Selecting the best of 3 models is ε-DP with sensitivity Δ=1. -/
theorem select_best_of_three_models (ε : NNReal) :
    IsPureDP ListHeadAddRemove
      (privateModelSelect threeScores ε 1)
      ε :=
  privateModelSelect_isPureDP (by norm_num : (1 : ℝ≥0) ≠ 0) threeScores_sensitivity

end DPlean4.Examples

end -- noncomputable section
