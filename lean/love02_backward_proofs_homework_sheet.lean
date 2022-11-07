import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 2: Backward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/-! ## Question 1 (4 points): Connectives and Quantifiers

1.1 (3 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
begin
  intros hab hca hc,
  apply hab,
  apply hca,
  exact hc
end

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
begin
  intros habc hab ha,
  apply habc,
  exact ha,
  apply hab,
  exact ha
end

lemma more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
begin
  intros hcaba hc hb,
  apply hcaba,
  { exact hc },
  { intro ha,
    exact hb }
end

lemma even_more_nonsense (a b c : Prop) :
  (a → a → b) → (b → c) → a → b → c :=
begin
  intros _ hbc _ hb,
  apply hbc,
  exact hb
end

/-! 1.2 (1 point). Prove the following lemma using basic tactics. -/

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
begin
  intro hp,
  apply hp,
  intro hq,
  apply hq,
  intro ha,
  apply hp,
  intro hr,
  exact ha
end


/-! ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about implication using basic
tactics.

Hints:

* Keep in mind that `¬ a` is the same as `a → false`. You can start by invoking
  `rw not_def` if this helps you.

* You will need to apply the elimination rules for `∨` and `false` at some
  point. -/

lemma about_implication (a b : Prop) :
  ¬ a ∨ b → a → b :=
begin
  intros hp ha,
  apply or.elim hp,
  { intro hna,
    apply false.elim,
    apply hna,
    exact ha },
  { intro hb,
    exact hb }
end

/-! 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* You can use `rw double_negation` to unfold the definition of
  `double_negation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check excluded_middle
#check peirce
#check double_negation

lemma em_of_dn :
  double_negation → excluded_middle :=
begin
  rw double_negation,
  rw excluded_middle,
  intros hdn a,
  apply hdn,
  clear hdn,
  -- We just need to prove ¬¬(a ∨ ¬a), which is true intuitionistically
  rw not_def,
  rw not_def,
  intro hnem,
  apply hnem,
  apply or.intro_right,
  rw not_def,
  intro ha,
  apply hnem,
  apply or.intro_left,
  exact ha
end

/-! 2.3 (2 points). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

-- enter your solution here

lemma em_of_peirce :
  peirce → excluded_middle :=
begin
  intro p,
  apply em_of_dn,
  apply dn_of_peirce,
  exact p
end

lemma peirce_of_dn :
  double_negation → peirce :=
begin
  intro d,
  apply peirce_of_em,
  apply em_of_dn,
  exact d
end

lemma dn_of_en :
  excluded_middle → double_negation :=
begin
  intro e,
  apply dn_of_peirce,
  apply peirce_of_em,
  exact e
end

end backward_proofs

end LoVe
