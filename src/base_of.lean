import data.fintype.basic
import tactic
import matroid
import finset

variables {α : Type*} [fintype α] [decidable_eq α] {m : matroid α} {A B X: finset α}

open finset

namespace matroid

lemma base_of_refl_iff_ind : m.ind A ↔ m.base_of A A :=
begin
  split, {
    intro Aind,
    refine ⟨subset.refl _, Aind, λ x hnx hx, absurd hx hnx⟩,
  }, {
    exact λ hb, hb.2.1,
  }
end

lemma base_of_eq_card (hA : m.base_of X A) (hB : m.base_of X B) : A.card = B.card := 
begin
  by_contradiction,
  wlog : A.card ≤ B.card := le_total A.card B.card using [A B, B A],
  replace h := nat.lt_of_le_and_ne case h,
  obtain ⟨w, wB, wA, winsert⟩ := m.ind_exchange _ _ (base_of_ind hA) (base_of_ind hB) h,
  refine hA.2.2 w wA (base_of_subset hB wB) winsert,
end

lemma ind_subset_base_of : A ⊆ X → m.ind A → ∃ B, A ⊆ B ∧ m.base_of X B :=
begin
  intros hAX hA,
  by_contradiction,
  push_neg at h,
  suffices ind_unbounded : ∀ k ≥ A.card, ∃ B, A ⊆ B ∧ B ⊆ X ∧ m.ind B ∧ B.card = k, {
    rcases ind_unbounded (X.card + 1) _ with ⟨B, hAB, hBX, Bind, Bcard⟩,    
    replace hBX := card_le_of_subset hBX,
    linarith, 
    replace hAX := card_le_of_subset hAX,
    linarith,
  },
  apply nat.le_induction, {
    use [A, subset.refl A, hAX, hA],
  }, {
    rintro n Acard ⟨B, hAB, hBX, Bind, rfl⟩,
    specialize h B hAB,
    rw base_of at h,
    push_neg at h,
    rcases h hBX Bind with ⟨w, wB, wX, w_insert⟩,
    use [insert w B],
    use [subset.trans hAB (subset_insert _ _)],
    use [insert_subset.2 ⟨wX, hBX⟩],
    use [w_insert, card_insert_of_not_mem wB],
  }
end

theorem exists_base_of (m : matroid α) (X : finset α): ∃ A, m.base_of X A :=
begin
  obtain ⟨B, _, Bbase⟩ := ind_subset_base_of (empty_subset X) m.ind_empty,
  exact ⟨B, Bbase⟩,
end

lemma ind_card_le_base_of_card : (A ⊆ X) → m.ind A → m.base_of X B → A.card ≤ B.card :=
begin
  intros hAX Aind Bbase,
  obtain ⟨T, hAT, Tbase⟩ := ind_subset_base_of hAX Aind,
  rw base_of_eq_card Bbase Tbase,
  exact card_le_of_subset hAT,
end

end matroid