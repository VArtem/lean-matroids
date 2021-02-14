import data.finset.basic
import tactic

variables {X : Type*} [fintype X] [decidable_eq X]

lemma finset.eq_of_card_eq_subset {A B : finset X} : A ⊆ B → A.card = B.card → A = B :=
begin
  intros h_subset h_card,
  induction B using finset.induction_on generalizing A, {
    simpa only [finset.card_empty, finset.card_eq_zero] using h_card,
  },
  case h₂ : x B x_mem ih {
    specialize @ih (A \ {x}),
    have t : x ∈ A, from by {
      sorry,
    },
    sorry,
  },
end
