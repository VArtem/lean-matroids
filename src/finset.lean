import data.finset.basic
import tactic

variables {X : Type*} [fintype X] [decidable_eq X]

namespace finset

open finset

lemma card_erase_of_mem' {A : finset X} {x} (h : x ∈ A) : (A.erase x).card + 1 = A.card :=
begin
  rw [card_erase_of_mem h, nat.add_one, nat.succ_pred_eq_of_pos],
  rw [gt_iff_lt, pos_iff_ne_zero],
  exact card_ne_zero_of_mem h,
end

lemma sdiff_subset_erase_of_mem {A B : finset X} {x} : x ∈ B → A \ B ⊆ A.erase x :=
begin
  intros xB,
  rw [← sdiff_singleton_eq_erase x A],
  apply sdiff_subset_sdiff (subset.refl _) _,
  rwa singleton_subset_iff,
end

lemma eq_or_ssubset_of_subset {A B : finset X} (h : A ⊆ B) : A = B ∨ A ⊂ B :=
begin
  rwa [← le_iff_subset, le_iff_eq_or_lt] at h,
end

lemma union_singleton {A : finset X} {x : X} : {x} ∪ A  = insert x A :=
begin
  exact (insert_eq x A).symm,
end

lemma card_succ_iff_erase_mem {A B : finset X} (h : A ⊆ B) :
  B.card = A.card + 1 ↔ ∃ x ∈ B, A = B.erase x :=
begin
  split, {
    intro h_card,
    have hC : (B \ A).card = 1, from by {
      rw [card_sdiff h],
      exact nat.sub_eq_of_eq_add h_card,
    },
    obtain ⟨x, h_sing⟩ := card_eq_one.1 hC,
    use x,
    have hx : x ∈ B \ A, by simp only [h_sing, mem_singleton],
    rw mem_sdiff at hx,
    use hx.1,
    rw [←sdiff_union_of_subset h, h_sing, ←insert_eq, erase_insert hx.2],
  }, {
    rintro ⟨x, xB, rfl⟩,
    exact (card_erase_of_mem' xB).symm,
  }
end

lemma very_important_lemma {A B S : finset X} : 
  (A ∩ B) ⊆ S → S ⊆ (A ∪ B) → (A ∪ B).card = S.card + 1 → (A ⊆ S ∨ B ⊆ S) :=
begin
  intros ABS SAB Scard,
  obtain ⟨x, xUnion, rfl⟩ := (card_succ_iff_erase_mem SAB).1 Scard,
  rw mem_union at xUnion,
  wlog xA : x ∈ A := xUnion using [A B, B A],
  right,
  have xInter : x ∉ A ∩ B := λ h, not_mem_erase _ _ (ABS h),
  have xB : x ∉ B := λ h, xInter $ mem_inter_of_mem xA h,
  nth_rewrite 0 ← (erase_eq_of_not_mem xB),
  exact erase_subset_erase _ (subset_union_right _ _),
end

lemma eq_or_eq_succ_of_le_and_le_succ {x y : ℕ}: x ≤ y → y ≤ x + 1 → x = y ∨ x + 1 = y :=
begin
  intros hxy hyx1,
  cases le_iff_lt_or_eq.1 hxy, {
    right,
    linarith,
  }, {
    left, exact h,
  }
end


lemma not_mem_sdiff_iff {x : X} {A B : finset X} : x ∉ A \ B ↔ x ∉ A ∨ x ∈ B :=
begin
  rw not_iff_comm,
  push_neg, 
  simp only [mem_sdiff, iff_self],
end

lemma card_sdiff_ℤ {A B : finset X} (hAB : A ⊆ B) : ((B \ A).card : ℤ) = (B.card : ℤ) - (A.card : ℤ) :=  
begin
  suffices h : (B \ A).card + A.card = B.card, {
    linarith,
  },
  rw [card_sdiff hAB, nat.sub_add_cancel (card_le_of_subset hAB)],
end

end finset