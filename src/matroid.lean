import data.fintype.basic
import tactic
import finset

-- TODO: 
-- matroid constructions: subtype, contract, direct sum, map
-- base theorem, base construction
-- circuit theorem, circuit construction
-- rank theorem, rank construction
-- closure theorem, closure construction
-- examples

structure matroid (X : Type*) [fintype X] [decidable_eq X] :=
  (ind : set (finset X))
  (ind_empty : ind ∅)
  (ind_subset : ∀ (A B), A ⊆ B → ind B → ind A)
  (ind_exchange : ∀ (A B : finset X), A ∈ ind → B ∈ ind → A.card < B.card →
    (∃ (c ∈ B), (c ∉ A) ∧ ind (insert c A)))

variables {X : Type*} [fintype X] [decidable_eq X] {m : matroid X}

open finset

namespace matroid

@[simp] lemma ind_empty_def : m.ind ∅ := m.ind_empty

@[simp] lemma ind_subset_def : ∀ (A B), A ⊆ B → m.ind B → m.ind A := m.ind_subset

def base (m : matroid X) (A : finset X) := m.ind A ∧ ∀ x ∉ A, ¬m.ind (insert x A)

@[simp] lemma base_ind {A : finset X} : m.base A → m.ind A := λ x, x.1

def circuit (m : matroid X) (C : finset X) := ¬ m.ind C ∧ ∀ x ∈ C, m.ind (C.erase x)

@[simp] lemma circuit_not_ind {C : finset X} : m.circuit C → ¬ m.ind C := λ x, x.1



end matroid