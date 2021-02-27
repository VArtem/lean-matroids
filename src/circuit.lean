import data.nat.basic
import data.finset.basic
import tactic
import matroid
import finset
import base_of

variables {α : Type*} [fintype α] [decidable_eq α] {m : matroid α} {A B : finset α}

open finset

namespace matroid

lemma circuit_sdiff  : m.circuit A → B ⊆ A → B ≠ ∅ → m.ind (A \ B) :=
begin
  rintro ⟨Anind, Aerase⟩ Bsubset Bnonempty, 
  rw ← nonempty_iff_ne_empty at Bnonempty,
  rcases Bnonempty with ⟨x, xB⟩,
  have xA := Bsubset xB,
  refine m.ind_subset _ (A.erase x) _ (Aerase x xA),
  exact sdiff_subset_erase_of_mem xB,
end 

lemma circuit_ssubset : m.circuit A → B ⊂ A → m.ind B :=
begin 
  rintro ⟨Anind, Aerase⟩ Bsubset,
  rw ssubset_iff at Bsubset,
  rcases Bsubset with ⟨x, xB, x_insert⟩,
  rw insert_subset at x_insert,
  cases x_insert with xA h_subset,  
  apply m.ind_subset _ (A.erase x) _ (Aerase x xA),
  rw ← erase_eq_of_not_mem xB,
  exact erase_subset_erase x h_subset,
end

lemma ind_iff_not_contains_circuit (A) : m.ind A ↔ ∀ C, m.circuit C → ¬ C ⊆ A :=
begin
  split, {
    intros Aind C Ccirc hCA,
    refine dep_superset hCA (Ccirc.1) Aind,
  }, {
    intros h,
    by_contradiction Aind,
    suffices subsets_dep : ∀ k ≤ A.card, ∃ B ⊆ A, B.card = k ∧ ¬ m.ind B, {
      obtain ⟨B, Bsub, Bcard, Bdep⟩ := subsets_dep 0 (zero_le _),
      rw [card_eq_zero] at Bcard,
      subst Bcard,
      exact Bdep m.ind_empty,
    },
    intros k k_le_card,
    refine nat.decreasing_induction (λ n, _) k_le_card _, {
      rintro ⟨B, hBA, Bcard, Bdep⟩,
      specialize h B,
      rw imp_not_comm at h,
      specialize h hBA,
      rw circuit at h,
      push_neg at h,
      obtain ⟨x, xAB, h_dep_erase⟩ := h Bdep,
      refine ⟨B.erase x, subset.trans (erase_subset _ _) hBA, _, h_dep_erase⟩,
      rw ← card_erase_of_mem' xAB at Bcard,
      exact nat.succ_inj'.1 Bcard,
    }, {
      use [A, subset.refl _, rfl],
    }
  }
end

lemma dep_iff_contains_circuit (A) : ¬ m.ind A ↔ ∃ C, m.circuit C ∧ C ⊆ A :=
begin
  have h := not_congr (ind_iff_not_contains_circuit A),
  push_neg at h,
  exact h,
end

theorem empty_not_circuit : ¬ m.circuit ∅ := λ ⟨empty_dep, _⟩, empty_dep m.ind_empty

theorem circuit_not_subset {A B} : m.circuit A → m.circuit B → A ⊆ B → A = B :=
begin
  rintro Acirc Bcirc h_subset,
  cases eq_or_ssubset_of_subset h_subset,
  { exact h, },
  {
    exfalso,
    exact Acirc.1 (circuit_ssubset Bcirc h),
  },
end

theorem circuit_common_element {x} (Acirc : m.circuit A) (Bcirc : m.circuit B): 
  A ≠ B → x ∈ A → x ∈ B → ∃ C, m.circuit C ∧ C ⊆ ((A ∪ B).erase x) :=
begin
  intros A_neq_B xA xB, 
  rw ← dep_iff_contains_circuit,
  intro union_ind,
  have inter_ind : m.ind (A ∩ B), from by {
    rw ind_iff_not_contains_circuit,
    intros C Ccirc Csub,
    have hAC := circuit_not_subset Ccirc Acirc (subset.trans Csub (inter_subset_left _ _)),
    have hBC := circuit_not_subset Ccirc Bcirc (subset.trans Csub (inter_subset_right _ _)),
    exact A_neq_B (eq.trans hAC.symm hBC),
  },
  have tmp : A ∩ B ⊆ A ∪ B := subset.trans (inter_subset_left _ _) (subset_union_left _ _),
  obtain ⟨X, hABX, hXbase_of⟩ := ind_subset_base_of tmp (inter_ind),
  have tmp2 := ind_card_le_base_of_card (erase_subset _ _) union_ind hXbase_of,
  
  replace tmp2 := nat.add_le_add_right tmp2 1, 
  rw [card_erase_of_mem' (mem_union_left _ xA)] at tmp2,
  have tmp3 := card_le_of_subset hXbase_of.1,
  cases eq_or_eq_succ_of_le_and_le_succ tmp3 tmp2, {
    replace h := eq_of_subset_of_card_le (hXbase_of.1) (ge_of_eq h),
    subst h,
    refine (dep_iff_contains_circuit (A ∪ B)).2 _ hXbase_of.2.1,
    use [A, Acirc, subset_union_left _ _],
  }, {
    cases very_important_lemma hABX hXbase_of.1 h.symm, {
      refine (dep_iff_contains_circuit X).2 _ hXbase_of.2.1,
      use [A, Acirc, h_1],
    }, {
      refine (dep_iff_contains_circuit X).2 _ hXbase_of.2.1,
      use [B, Bcirc, h_1],      
    }
  }
end

lemma circuit_subset_ind_insert {x} (Aind : m.ind A) (hx : x ∉ A) (Bcirc : m.circuit B) :
  B ⊆ insert x A → x ∈ B :=
begin
  intro Bsub,
  by_contradiction,
  rw [subset_insert_iff, erase_eq_of_not_mem h] at Bsub,
  exact (circuit_dep Bcirc) (ind_subset_def _ _ Bsub Aind),
end

theorem base_insert_unique_circuit {x} (Abase : m.base A) (hx : x ∉ A) :
  ∃! C, C ⊆ (insert x A) ∧ m.circuit C :=
begin
  have tmp : ¬ m.ind (insert x A) := Abase.2 x hx,
  obtain ⟨C, Ccirc, Csub⟩ := (dep_iff_contains_circuit _).1 tmp,
  use [C, Csub, Ccirc],
  rintro D ⟨Dsub, Dcirc⟩,
  have Cmem := circuit_subset_ind_insert (Abase.1) hx Ccirc Csub,
  have Dmem := circuit_subset_ind_insert (Abase.1) hx Dcirc Dsub,
  by_contradiction,
  rcases circuit_common_element Dcirc Ccirc h Dmem Cmem with ⟨U, Ucirc, Usub⟩,
  suffices hUA : U ⊆ A, {
    exact (circuit_dep Ucirc) (ind_subset_def _ _ hUA Abase.1),
  }, {
    have tmp : (D ∪ C) ⊆ (insert x A) := union_subset Dsub Csub,
    replace tmp := erase_subset_erase x tmp,
    rw erase_insert hx at tmp,
    exact subset.trans Usub tmp,
  }
end

end matroid