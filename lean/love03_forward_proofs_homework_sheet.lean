import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
fix hdn : double_negation,
have hem : excluded_middle :=
  sorry_lemmas.em_of_dn hdn,
have hp : peirce :=
  peirce_of_em hem,
show peirce, from
  hp

lemma em_of_peirce :
  peirce → excluded_middle :=
fix hp : peirce,
have hdn : double_negation :=
  dn_of_peirce hp,
have hem : excluded_middle :=
  sorry_lemmas.em_of_dn hdn,
show excluded_middle, from
  hem

lemma dn_of_em :
  excluded_middle → double_negation :=
fix hem : excluded_middle,
have hp : peirce :=
  peirce_of_em hem,
have hdn : double_negation :=
  dn_of_peirce hp,
show double_negation, from
  hdn

end backward_proofs

/-! 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute_aux {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) → (∃x, q x ∧ p x) :=
assume he,
show ∃x, q x ∧ p x, from exists.elim he (
  fix a,
  assume hpq,
  have hp : p a, from and.elim_left hpq,
  have hq : q a, from and.elim_right hpq,
  have hqp : q a ∧ p a, from and.intro hq hp,
  show ∃ (x : α), q x ∧ p x, from exists.intro a hqp
)

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
have ltr : (∃x, p x ∧ q x) → (∃x, q x ∧ p x), from exists_and_commute_aux p q,
have rtl : (∃x, q x ∧ p x) → (∃x, p x ∧ q x), from exists_and_commute_aux q p,
show (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x), from iff.intro ltr rtl


/-! ## Question 2 (3 points): Fokkink Logic Puzzles

If you have studied Logic and Sets with Prof. Fokkink, you will know he is fond
of logic puzzles. This question is a tribute.

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/-! 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
λa b, λf, f (λg, g (λha, f (λh, ha)))

/-! 2.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
fix a b,
assume f,
show b, from f (
  assume g,
  show a, from g (
    assume ha,
    show b, from f (
      assume h,
      ha
    )
  )
)

end LoVe
