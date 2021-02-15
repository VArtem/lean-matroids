import data.fintype.basic
import tactic
import matroid
import finset

variables {X : Type*} [fintype X] [decidable_eq X] {m : matroid X}

open finset

namespace matroid

lemma circuit_sdiff {A B} : m.circuit A → B ⊆ A → B ≠ ∅ → m.ind (A \ B) :=
begin
  rintro ⟨Anind, Aerase⟩ Bsubset Bnonempty, 
  rw ← nonempty_iff_ne_empty at Bnonempty,
  rcases Bnonempty with ⟨x, xB⟩,
  have xA := Bsubset xB,
  refine m.ind_subset _ (A.erase x) _ (Aerase x xA),
  exact sdiff_subset_erase_of_mem xB,
end 

lemma circuit_subset {A B} : m.circuit A → B ⊂ A → m.ind B :=
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

end matroid