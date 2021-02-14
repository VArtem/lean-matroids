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

lemma base_eq_card {A B : finset X} (hA : m.base A) (hB : m.base B) : A.card = B.card := 
begin
  by_contradiction,
  wlog : A.card ≤ B.card := le_total A.card B.card using [A B, B A],
  replace h := nat.lt_of_le_and_ne case h,
  rcases m.ind_exchange _ _ (base_ind hA) (base_ind hB) h with ⟨w, wB, wA, winsert⟩,
  exact hA.2 w wA winsert,
end

theorem base_exists : ∃ A, m.base A :=
begin
  by_contradiction,
  push_neg at h,
  suffices ind_unbounded : ∀ k, ∃ A, (m.ind A) ∧ A.card = k, {
    rcases ind_unbounded (fintype.card X + 1) with ⟨A, Aind, Acard⟩,
    have Acard_le := finset.card_le_univ A,
    linarith,
  },
  intro k,
  induction k, {
    use ∅,
    simp only [finset.card_empty, ind_empty, eq_self_iff_true, and_self],
  }, {
    rcases k_ih with ⟨A, Aind, Acard⟩,
    specialize h A,    
    rw base at h,
    push_neg at h,
    rcases h Aind with ⟨x, xA, ind_insert⟩,
    use [insert x A, ind_insert],
    rw ← Acard,
    exact finset.card_insert_of_not_mem xA,
  }
end

theorem base_not_subset {A B} : m.base A → m.base B → A ⊆ B → A = B :=
begin
  rintro Abase Bbase h_subset,
  exact finset.eq_of_card_eq_subset h_subset (base_eq_card Abase Bbase),
end

-- TODO: use in base_exists
lemma ind_extension {A} : m.ind A → ∃ B, A ⊆ B ∧ m.base B :=
begin
  sorry,
end

lemma base_iff_ind_and_eq_card_base {A B} (Abase : m.base A) : (m.ind B ∧ A.card = B.card) ↔ m.base B :=
begin
  split, {
    rintro ⟨Bind, Acard⟩,
    use Bind,
    intros x xB h_insert_ind,
    sorry,
  }, {
    intro Bbase,
    exact ⟨Bbase.1, base_eq_card Abase Bbase⟩,
  }
end

theorem base_exchange {A B} : m.base A → m.base B → A ≠ B → ∀ x ∈ A \ B, ∃ b ∈ B, b ∉ A ∧ m.base (insert b (A.erase x)) :=
begin
  intros Abase Bbase h_neq x xA,
  rcases m.ind_exchange (A.erase x) B _ Bbase.1 _ with ⟨c, cB, cA, cinsert⟩,
  use [c, cB],
  {
    rw [mem_erase] at cA,
    push_neg at cA,
    rw mem_sdiff at xA,
    split, {
      finish,
    }, {
      apply (base_iff_ind_and_eq_card_base Abase).1,
      use cinsert,
      sorry,
    },
  }, { 
    exact m.ind_subset _ _ (erase_subset _ _) Abase.1, 
  }, {
    rw [← base_eq_card Abase Bbase, card_erase_of_mem xA],
    exact nat.pred_lt (card_ne_zero_of_mem xA),
  },
end

end matroid