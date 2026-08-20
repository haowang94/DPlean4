/-
Copyright (c) 2026 DPlean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DPlean4 Contributors
-/

import DPlean4.Basic.Adjacency
import DPlean4.Basic.Sensitivity

/-!
# Tabular Data Model and Marginal Queries

This file defines a tabular data representation and marginal (contingency table)
queries with their sensitivity proofs.

## Main Definitions

* `TabularRow`: a row assigning a value to each attribute
* `TabularDataset`: a list of rows
* `marginalCount1`: 1-way marginal count for a single attribute value
* `marginalVector1`: full 1-way marginal as a vector
* `marginalCount2`: 2-way marginal count for a pair of attribute values
* `marginalVector2`: full 2-way marginal as a vector

## Main Results

* `marginalVector1_L2Sensitivity`: 1-way marginals have L2 sensitivity 1
* `marginalVector2_L2Sensitivity`: 2-way marginals have L2 sensitivity 1

## References

* McKenna, Sheldon, Miklau (2021), "Winning the NIST Contest" (MST)
* McKenna, Mullins, Sheldon, Miklau (2022), "AIM"
-/

namespace DPlean4

open Finset
open scoped NNReal

-- ============================================================================
-- Sensitivity transfer: ListHeadAddRemove → ListAddRemove
-- ============================================================================

/-- For queries where each component is permutation-invariant,
    L2 vector sensitivity under `ListHeadAddRemove` implies L2 vector
    sensitivity under `ListAddRemove`. -/
theorem hasL2VectorSensitivity_addRemove_of_head {α : Type*}
    {ι : Type*} [Fintype ι] {q : List α → ι → ℝ} {Δ : ℝ≥0}
    (hperm : ∀ i, IsPermutationInvariant (fun l => q l i))
    (hsens : HasL2VectorSensitivity (@ListHeadAddRemove α) q Δ) :
    HasL2VectorSensitivity (@ListAddRemove α) q Δ := by
  intro l₁ l₂ hadj
  rcases hadj with ⟨pre, suffix, a, rfl, rfl⟩ | ⟨pre, suffix, a, rfl, rfl⟩
  · have hperm_eq : ∀ i, q (pre ++ a :: suffix) i = q (a :: (pre ++ suffix)) i :=
      fun i => hperm i _ _ List.perm_middle
    simp_rw [hperm_eq]
    exact hsens _ _ (Or.inl ⟨a, pre ++ suffix, rfl, rfl⟩)
  · have hperm_eq : ∀ i, q (pre ++ a :: suffix) i = q (a :: (pre ++ suffix)) i :=
      fun i => hperm i _ _ List.perm_middle
    simp_rw [hperm_eq]
    have h := hsens (a :: (pre ++ suffix)) (pre ++ suffix)
      (Or.inl ⟨a, pre ++ suffix, rfl, rfl⟩)
    simp_rw [show ∀ i, (q (pre ++ suffix) i - q (a :: (pre ++ suffix)) i) ^ 2 =
      (q (a :: (pre ++ suffix)) i - q (pre ++ suffix) i) ^ 2 from
      fun i => by ring] at *
    exact h

variable {Attr : Type*} {dom : Attr → Type*}

-- ============================================================================
-- Tabular Data Representation
-- ============================================================================

/-- A row in a tabular dataset: assigns a value to each attribute. -/
abbrev TabularRow (Attr : Type*) (dom : Attr → Type*) := ∀ a : Attr, dom a

/-- A tabular dataset: a list of rows. -/
abbrev TabularDataset (Attr : Type*) (dom : Attr → Type*) :=
  List (TabularRow Attr dom)

-- ============================================================================
-- 1-Way Marginal Queries
-- ============================================================================

variable [∀ a, DecidableEq (dom a)]

/-- Count of rows where attribute `a` has value `v`. -/
def marginalCount1 (a : Attr) (v : dom a)
    (d : TabularDataset Attr dom) : ℝ :=
  (d.countP (fun row => decide (row a = v)) : ℝ)

/-- Full 1-way marginal: the histogram of attribute `a` values. -/
def marginalVector1 (a : Attr) [Fintype (dom a)]
    (d : TabularDataset Attr dom) : dom a → ℝ :=
  fun v => marginalCount1 a v d

section OneMarginal

private theorem marginalCount1_cons_eq (a : Attr) (v : dom a)
    (row : TabularRow Attr dom) (s : TabularDataset Attr dom) (heq : row a = v) :
    marginalCount1 a v (row :: s) = marginalCount1 a v s + 1 := by
  simp only [marginalCount1, List.countP_cons, heq, decide_true, ite_true,
    Nat.cast_add, Nat.cast_one]

private theorem marginalCount1_cons_ne (a : Attr) (v : dom a)
    (row : TabularRow Attr dom) (s : TabularDataset Attr dom) (hne : row a ≠ v) :
    marginalCount1 a v (row :: s) = marginalCount1 a v s := by
  simp only [marginalCount1, List.countP_cons, hne, decide_false, Nat.cast_inj]
  simp

/-- 1-way marginal has L2 vector sensitivity 1 under add/remove adjacency. -/
theorem marginalVector1_L2Sensitivity (a : Attr) [Fintype (dom a)] :
    HasL2VectorSensitivity (@ListHeadAddRemove (TabularRow Attr dom))
      (marginalVector1 a) 1 := by
  intro d₁ d₂ hadj
  obtain ⟨row, s, h1, h2⟩ | ⟨row, s, h1, h2⟩ := hadj
  · simp only [h1, h2, NNReal.coe_one, one_pow]
    have key : ∀ v : dom a,
        (marginalVector1 a (row :: s) v - marginalVector1 a s v) ^ 2 =
        if v = row a then 1 else 0 := by
      intro v
      simp only [marginalVector1]
      by_cases heq : row a = v
      · rw [marginalCount1_cons_eq a v row s heq]; simp [heq.symm]
      · rw [marginalCount1_cons_ne a v row s heq]; simp [Ne.symm heq]
    simp_rw [key]
    rw [Finset.sum_ite_eq' univ (row a) (fun _ => (1 : ℝ))]
    simp
  · simp only [h1, h2, NNReal.coe_one, one_pow]
    have key : ∀ v : dom a,
        (marginalVector1 a s v - marginalVector1 a (row :: s) v) ^ 2 =
        if v = row a then 1 else 0 := by
      intro v
      simp only [marginalVector1]
      by_cases heq : row a = v
      · rw [marginalCount1_cons_eq a v row s heq]; simp [heq.symm]
      · rw [marginalCount1_cons_ne a v row s heq]; simp [Ne.symm heq]
    simp_rw [key]
    rw [Finset.sum_ite_eq' univ (row a) (fun _ => (1 : ℝ))]
    simp

end OneMarginal

-- ============================================================================
-- 2-Way Marginal Queries
-- ============================================================================

/-- Count of rows where attribute `a₁` has value `v₁` AND attribute `a₂` has value `v₂`. -/
def marginalCount2 (a₁ a₂ : Attr) (v₁ : dom a₁) (v₂ : dom a₂)
    (d : TabularDataset Attr dom) : ℝ :=
  (d.countP (fun row => decide (row a₁ = v₁) && decide (row a₂ = v₂)) : ℝ)

/-- Full 2-way marginal: the contingency table for attributes `a₁` and `a₂`. -/
def marginalVector2 (a₁ a₂ : Attr) [Fintype (dom a₁)] [Fintype (dom a₂)]
    (d : TabularDataset Attr dom) : dom a₁ × dom a₂ → ℝ :=
  fun ⟨v₁, v₂⟩ => marginalCount2 a₁ a₂ v₁ v₂ d

section TwoMarginal

private theorem marginalCount2_cons_eq (a₁ a₂ : Attr) (v₁ : dom a₁) (v₂ : dom a₂)
    (row : TabularRow Attr dom) (s : TabularDataset Attr dom)
    (heq₁ : row a₁ = v₁) (heq₂ : row a₂ = v₂) :
    marginalCount2 a₁ a₂ v₁ v₂ (row :: s) = marginalCount2 a₁ a₂ v₁ v₂ s + 1 := by
  simp only [marginalCount2, List.countP_cons, heq₁, heq₂, decide_true, Bool.true_and,
    ite_true, Nat.cast_add, Nat.cast_one]

private theorem marginalCount2_cons_ne (a₁ a₂ : Attr) (v₁ : dom a₁) (v₂ : dom a₂)
    (row : TabularRow Attr dom) (s : TabularDataset Attr dom)
    (hne : ¬(row a₁ = v₁ ∧ row a₂ = v₂)) :
    marginalCount2 a₁ a₂ v₁ v₂ (row :: s) = marginalCount2 a₁ a₂ v₁ v₂ s := by
  simp only [marginalCount2, List.countP_cons, Nat.cast_inj]
  by_cases h₁ : row a₁ = v₁ <;> by_cases h₂ : row a₂ = v₂ <;> simp_all

/-- 2-way marginal has L2 vector sensitivity 1 under add/remove adjacency. -/
theorem marginalVector2_L2Sensitivity (a₁ a₂ : Attr)
    [Fintype (dom a₁)] [Fintype (dom a₂)] :
    HasL2VectorSensitivity (@ListHeadAddRemove (TabularRow Attr dom))
      (marginalVector2 a₁ a₂) 1 := by
  intro d₁ d₂ hadj
  obtain ⟨row, s, h1, h2⟩ | ⟨row, s, h1, h2⟩ := hadj
  · simp only [h1, h2, NNReal.coe_one, one_pow]
    have key : ∀ p : dom a₁ × dom a₂,
        (marginalVector2 a₁ a₂ (row :: s) p - marginalVector2 a₁ a₂ s p) ^ 2 =
        if p = (row a₁, row a₂) then 1 else 0 := by
      intro ⟨v₁, v₂⟩
      simp only [marginalVector2, Prod.mk.injEq]
      by_cases h : v₁ = row a₁ ∧ v₂ = row a₂
      · rw [marginalCount2_cons_eq a₁ a₂ v₁ v₂ row s h.1.symm h.2.symm]
        simp [h]
      · rw [marginalCount2_cons_ne a₁ a₂ v₁ v₂ row s
            (fun ⟨e1, e2⟩ => h ⟨e1.symm, e2.symm⟩)]
        simp [h]
    simp_rw [key]
    rw [Finset.sum_ite_eq' univ (row a₁, row a₂) (fun _ => (1 : ℝ))]
    simp
  · simp only [h1, h2, NNReal.coe_one, one_pow]
    have key : ∀ p : dom a₁ × dom a₂,
        (marginalVector2 a₁ a₂ s p - marginalVector2 a₁ a₂ (row :: s) p) ^ 2 =
        if p = (row a₁, row a₂) then 1 else 0 := by
      intro ⟨v₁, v₂⟩
      simp only [marginalVector2, Prod.mk.injEq]
      by_cases h : v₁ = row a₁ ∧ v₂ = row a₂
      · rw [marginalCount2_cons_eq a₁ a₂ v₁ v₂ row s h.1.symm h.2.symm]
        simp [h]
      · rw [marginalCount2_cons_ne a₁ a₂ v₁ v₂ row s
            (fun ⟨e1, e2⟩ => h ⟨e1.symm, e2.symm⟩)]
        simp [h]
    simp_rw [key]
    rw [Finset.sum_ite_eq' univ (row a₁, row a₂) (fun _ => (1 : ℝ))]
    simp

end TwoMarginal

-- ============================================================================
-- Permutation invariance and ListAddRemove sensitivity
-- ============================================================================

/-- 1-way marginal counts are permutation-invariant: they depend only on the
    multiset of rows, not their ordering. -/
theorem marginalCount1_perm_invariant (a : Attr) (v : dom a) :
    IsPermutationInvariant (marginalCount1 (dom := dom) a v) := by
  intro l₁ l₂ hp
  simp only [marginalCount1, hp.countP_eq]

/-- 2-way marginal counts are permutation-invariant. -/
theorem marginalCount2_perm_invariant (a₁ a₂ : Attr) (v₁ : dom a₁) (v₂ : dom a₂) :
    IsPermutationInvariant (marginalCount2 (dom := dom) a₁ a₂ v₁ v₂) := by
  intro l₁ l₂ hp
  simp only [marginalCount2, hp.countP_eq]

/-- 1-way marginals have L2 sensitivity 1 under arbitrary-position `ListAddRemove`. -/
theorem marginalVector1_L2Sensitivity_addRemove (a : Attr) [Fintype (dom a)] :
    HasL2VectorSensitivity (@ListAddRemove (TabularRow Attr dom))
      (marginalVector1 a) 1 :=
  hasL2VectorSensitivity_addRemove_of_head
    (fun v => marginalCount1_perm_invariant a v)
    (marginalVector1_L2Sensitivity a)

/-- 2-way marginals have L2 sensitivity 1 under arbitrary-position `ListAddRemove`. -/
theorem marginalVector2_L2Sensitivity_addRemove (a₁ a₂ : Attr)
    [Fintype (dom a₁)] [Fintype (dom a₂)] :
    HasL2VectorSensitivity (@ListAddRemove (TabularRow Attr dom))
      (marginalVector2 a₁ a₂) 1 :=
  hasL2VectorSensitivity_addRemove_of_head
    (fun p => marginalCount2_perm_invariant a₁ a₂ p.1 p.2)
    (marginalVector2_L2Sensitivity a₁ a₂)

end DPlean4
