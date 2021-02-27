import data.fintype.basic
import tactic
import matroid
import finset
import base_of

variables {α : Type*} [fintype α] [decidable_eq α] {m : matroid α} {A B: finset α}

open finset

namespace matroid

lemma base_eq_card (hA : m.base A) (hB : m.base B) : A.card = B.card := 
  by {rw [←base_of_univ_iff_base] at *, exact base_of_eq_card hA hB} 

lemma ind_subset_base : m.ind A → ∃ B, A ⊆ B ∧ m.base B := λ hA, begin
  obtain ⟨B, hAB, h_base⟩ := ind_subset_base_of (subset_univ A) hA,
  rw base_of_univ_iff_base at h_base,
  use [B, hAB, h_base],
end

theorem exists_base : ∃ A, m.base A := 
begin
  obtain ⟨B, _, Bbase⟩ := ind_subset_base m.ind_empty,
  exact ⟨B, Bbase⟩,
end

theorem base_not_subset {A B} : m.base A → m.base B → A ⊆ B → A = B :=
begin
  rintro Abase Bbase h_subset,
  exact eq_of_subset_of_card_le h_subset (ge_of_eq $ base_eq_card Abase Bbase),
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