import data.fintype.basic
import tactic
import finset

-- TODO: 
-- matroid constructions: subtype, contraction, direct sum, map
-- dual matroid, matroid isomorphism
-- base theorem, base construction
-- circuit theorem, circuit construction
-- rank theorem, rank construction
-- closure theorem, closure construction
-- examples

structure matroid (α : Type*) [fintype α] [decidable_eq α] :=
  (ind : set (finset α))
  [ind_dec : decidable_pred ind]
  (ind_empty : ind ∅)
  (ind_subset : ∀ (A B), A ⊆ B → ind B → ind A)
  (ind_exchange : ∀ (A B : finset α), ind A → ind B → A.card < B.card →
    (∃ (c ∈ B), (c ∉ A) ∧ ind (insert c A)))

variables {α : Type*} [fintype α] [decidable_eq α] {m : matroid α} {A B X : finset α}

open finset

namespace matroid

@[simp] lemma ind_empty_def : m.ind ∅ := m.ind_empty

@[simp] lemma ind_subset_def : A ⊆ B → m.ind B → m.ind A := m.ind_subset _ _

@[simp] lemma dep_superset {A B} : A ⊆ B → ¬m.ind A → ¬m.ind B := λ h hA hB, hA (m.ind_subset _ _ h hB)

def base (m : matroid α) (A : finset α) := m.ind A ∧ ∀ x ∉ A, ¬m.ind (insert x A)

def base_of (m : matroid α) (A B : finset α) := B ⊆ A ∧ m.ind B ∧ ∀ (x ∉ B), (x ∈ A) → ¬m.ind (insert x B) 

@[simp] lemma base_ind : m.base A → m.ind A := λ h, h.1

@[simp] lemma base_of_ind : m.base_of X A → m.ind A := λ h, h.2.1

@[simp] lemma base_of_subset : m.base_of X A → A ⊆ X := λ h, h.1

@[simp] lemma base_of_univ_iff_base {A : finset α} : m.base_of univ A ↔ m.base A :=
  ⟨λ ⟨_, h_ind, h_ins⟩, ⟨h_ind, λ x hx, h_ins x hx (mem_univ x)⟩, λ ⟨h_ind, h_ins⟩, ⟨subset_univ A, h_ind, λ x hx _, h_ins x hx⟩⟩

def circuit (m : matroid α) (A : finset α) := ¬ m.ind A ∧ ∀ x ∈ A, m.ind (A.erase x)

@[simp] lemma circuit_dep : m.circuit A → ¬ m.ind A := λ x, x.1

end matroid