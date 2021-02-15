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

lemma eq_of_subset_card_eq_card {A B : finset X} : A ⊆ B → A.card = B.card → A = B :=
begin
  intros h_subset h_card,
  induction B using finset.induction_on generalizing A, {
    simpa only [card_empty, card_eq_zero] using h_card,
  },
  case h₂ : x B x_mem ih {
    rw subset_insert_iff at h_subset,
    rw card_insert_of_not_mem x_mem at h_card,
    have t : x ∈ A, from by {
      by_contradiction,
      replace h_subset := card_le_of_subset h_subset,
      rw [erase_eq_of_not_mem h, h_card] at h_subset,
      simpa only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] using h_subset,
    },
    rw [← card_erase_of_mem' t, add_left_inj] at h_card,
    specialize ih h_subset h_card,
    apply_fun insert x at ih,
    rwa insert_erase t at ih,
  },
end

example {A : finset X} {x} : A.erase x = A \ {x} := (sdiff_singleton_eq_erase x A).symm

lemma sdiff_subset_erase_of_mem {A B : finset X} {x} : x ∈ B → A \ B ⊆ A.erase x :=
begin
  intros xB,
  rw [← sdiff_singleton_eq_erase x A],
  apply sdiff_subset_sdiff (subset.refl _) _,
  rwa singleton_subset_iff,
end

end finset