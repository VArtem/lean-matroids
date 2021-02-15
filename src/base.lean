import data.fintype.basic
import tactic
import matroid
import finset

variables {X : Type*} [fintype X] [decidable_eq X] {m : matroid X}

open finset

namespace matroid

lemma base_eq_card {A B : finset X} (hA : m.base A) (hB : m.base B) : A.card = B.card := 
begin
  by_contradiction,
  wlog : A.card ≤ B.card := le_total A.card B.card using [A B, B A],
  replace h := nat.lt_of_le_and_ne case h,
  rcases m.ind_exchange _ _ (base_ind hA) (base_ind hB) h with ⟨w, wB, wA, winsert⟩,
  exact hA.2 w wA winsert,
end

lemma ind_subset_base {A} : m.ind A → ∃ B, A ⊆ B ∧ m.base B :=
begin
  intro Aind,
  by_contradiction,
  push_neg at h,
  suffices ind_unbounded : ∀ k ≥ A.card, ∃ B, A ⊆ B ∧ (m.ind B) ∧ B.card = k, {
    rcases ind_unbounded (fintype.card X + 1) _ with ⟨B, h_suibset, Bind, Bcard⟩,
    have Bcard_le := card_le_univ B,
    linarith,
    have Acard_le := card_le_univ A,
    linarith,
  },
  apply nat.le_induction, {
    use [A, subset.refl A, Aind, rfl],
  }, {
    rintro n Acard ⟨B, h_subset, Bind, Bcard⟩,
    specialize h B h_subset,
    rw base at h,
    push_neg at h,
    rcases h Bind with ⟨x, xB, x_insert⟩,
    use [insert x B],
    rw ← Bcard,
    use [subset.trans h_subset (subset_insert _ _), x_insert, card_insert_of_not_mem xB],
  }
end

theorem base_exists : ∃ A, m.base A :=
begin
  obtain ⟨B, _, Bbase⟩ := ind_subset_base m.ind_empty,
  exact ⟨B, Bbase⟩,
end

theorem base_not_subset {A B} : m.base A → m.base B → A ⊆ B → A = B :=
begin
  rintro Abase Bbase h_subset,
  exact finset.eq_of_subset_card_eq_card h_subset (base_eq_card Abase Bbase),
end

lemma ind_and_card_eq_card_base_iff_base {A B} (Abase : m.base A) : (m.ind B ∧ A.card = B.card) ↔ m.base B :=
begin
  split, {
    rintro ⟨Bind, Acard⟩,
    use Bind,
    intros x xB h_insert_ind,
    obtain ⟨C, Bsubset, Cbase⟩ := ind_subset_base h_insert_ind,
    replace Bsubset := card_le_of_subset Bsubset,
    rw [base_eq_card Abase Cbase] at Acard,
    rw card_insert_of_not_mem xB at Bsubset,
    linarith,
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
    rw mem_sdiff at xA,
    split, {
      finish,
    }, {
      apply (ind_and_card_eq_card_base_iff_base Abase).1,
      use cinsert,
      rw [card_insert_of_not_mem cA, card_erase_of_mem' xA.1],
    },
  }, { 
    exact m.ind_subset _ _ (erase_subset _ _) Abase.1, 
  }, {
    rw mem_sdiff at xA,
    rw [← base_eq_card Abase Bbase, card_erase_of_mem xA.1],
    exact nat.pred_lt (card_ne_zero_of_mem xA.1),
  },
end

end matroid