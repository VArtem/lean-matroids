import data.fintype.basic
import tactic
import matroid
import finset
import base_of

variables {α : Type*} [fintype α] [decidable_eq α] {m : matroid α} {A B X: finset α}

open finset

namespace matroid

instance : decidable_pred m.ind := m.ind_dec

-- def rank (m : matroid α) (A : finset α) : ℕ := card (classical.some $ exists_base_of m A) 
def rank (m : matroid α) (A : finset α) : ℕ := sup (filter m.ind (powerset A)) card

@[simp] lemma rank_def : rank m A = sup (filter m.ind (powerset A)) card := rfl

@[simp] lemma rank_empty : rank m ∅ = 0 := 
begin
  rw rank,
  simp only [card_empty, filter_true_of_mem, forall_eq, powerset_empty, sup_singleton, ind_empty_def, mem_singleton],
end

lemma rank_eq_card_base_of (Bbase : m.base_of A B) : rank m A = B.card :=
begin
  rw rank_def,
  apply nat.le_antisymm, {
    apply finset.sup_le,
    intros C hC,
    simp only [mem_powerset, mem_filter] at hC,
    exact ind_card_le_base_of_card hC.1 hC.2 Bbase,
  }, {
    apply le_sup,
    simp only [mem_powerset, mem_filter],
    exact ⟨Bbase.1, Bbase.2.1⟩,
  }
end

lemma rank_exists_base_of (m : matroid α) (A : finset α) : 
  ∃ (B : finset α), m.rank A = B.card ∧ m.base_of A B :=
begin
  obtain ⟨B, Bbase⟩ := exists_base_of m A,
  refine ⟨B, rank_eq_card_base_of Bbase, Bbase⟩,
end

@[simp] lemma rank_subset (hAB : A ⊆ B) : rank m A ≤ rank m B :=
begin
  obtain ⟨bA, bAbase⟩ := exists_base_of m A,
  obtain ⟨bB, bBbase⟩ := exists_base_of m B,
  rw rank_eq_card_base_of bAbase,
  rw rank_eq_card_base_of bBbase,
  refine ind_card_le_base_of_card (subset.trans bAbase.1 hAB) bAbase.2.1 bBbase,
end

@[simp] lemma rank_ind : m.ind A ↔ rank m A = A.card :=
begin
  split, {
    intro Aind,
    rw [base_of_refl_iff_ind] at Aind,
    rw rank_eq_card_base_of Aind,
  }, {
    intro h_card,
    obtain ⟨B, Bcard, Bbase⟩ := rank_exists_base_of m A,
    rw h_card at Bcard, 
    suffices h_eq : A = B, {
      subst h_eq,
      exact Bbase.2.1,
    },
    symmetry,
    exact eq_of_subset_of_card_le Bbase.1 (le_of_eq Bcard),
  }
end

theorem rank_submodular : m.rank (A ∩ B) + m.rank (A ∪ B) ≤ m.rank A + m.rank B :=
begin
  obtain ⟨bInter, bInter_base⟩ := exists_base_of m (A ∩ B),
  have rankInter := rank_eq_card_base_of bInter_base,
  
  obtain ⟨bA, bA_sub, bA_base⟩ := ind_subset_base_of (subset.trans bInter_base.1 (inter_subset_left _ _)) (bInter_base.2.1),
  have rankA := rank_eq_card_base_of bA_base,
  
  obtain ⟨bUnion, bUnion_sub, bUnion_base⟩ :=
    ind_subset_base_of (subset.trans bA_base.1 (subset_union_left A B)) bA_base.2.1,
  have rankUnion := rank_eq_card_base_of bUnion_base,
  
  obtain ⟨bB, bB_base⟩ := exists_base_of m B,
  have rankB := rank_eq_card_base_of bB_base,  
  
  have indB_sub : (bUnion \ (bA \ bInter)) ⊆ B := sorry,
  have indB_ind : m.ind (bUnion \ (bA \ bInter)) := ind_subset_def (sdiff_subset _ _) bUnion_base.2.1,

  have tmp := ind_card_le_base_of_card indB_sub indB_ind bB_base,
  have indB_card : (bUnion \ (bA \ bInter)).card = bUnion.card - (bA.card - bInter.card) := sorry,

  rw [rankInter, rankA, rankUnion, rankB],
  sorry,
end

end matroid