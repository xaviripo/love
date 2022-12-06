import .love09_hoare_logic_demo


/-! # LoVe Homework 9: Hoare Logic

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Hoare Logic for LOOP

We introduce the LOOP language: -/

namespace loop

inductive stmt : Type
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| it     : (state → Prop) → stmt → stmt
| loop   : stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/-! The language is similar to WHILE. There are three differences:

* There is no `skip` statement.

* The `it` statement is an `if`–`then` construct with no `else` case.

* The `loop` construct corresponds to a randomized `while` loop. It executes
  the body an unspecified (possibly infinite) number of times.

The big-step semantics for LOOP is defined below. -/

inductive big_step : stmt × state → state → Prop
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| seq {S T s t u} (hs : big_step (S, s) t)
    (ht : big_step (T, t) u) :
  big_step (S ;; T, s) u
| it_true {b : state → Prop} {S s t} (hcond : b s) (hbody : big_step (S, s) t) :
  big_step (stmt.it b S, s) t
| it_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  big_step (stmt.it b S, s) s
| loop_continue {S s t u} (hbody : big_step (S, s) t)
    (hrest : big_step (stmt.loop S, t) u) :
  big_step (stmt.loop S, s) u
| loop_exit {S s} :
  big_step (stmt.loop S, s) s

infix ` ⟹ ` : 110 := big_step

/-! The definition of Hoare triples for partial correctness is unsurprising: -/

def partial_hoare (P : state → Prop) (S : stmt) (Q : state → Prop) : Prop :=
∀s t, P s → (S, s) ⟹ t → Q t

local notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` :=
partial_hoare P S Q

namespace partial_hoare

/-! 1.1 (1 point). Prove the consequence rule. -/

lemma consequence {P P' Q Q' : state → Prop} {S} (h : {* P *} S {* Q *})
    (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  {* P' *} S {* Q' *} :=
begin
  rw partial_hoare at *,
  intros s t,
  intro p's,
  intro sst,
  apply hq,
  apply h s t,
  apply hp,
  exact p's,
  exact sst
end

/-! 1.2 (1 point). Prove the rule for `assign`. -/

lemma assign_intro {P : state → Prop} {x} {a : state → ℕ} :
  {* λs, P (s{x ↦ a s}) *} stmt.assign x a {* P *} :=
begin
  rw partial_hoare,
  intros s t,
  intro ps,
  intro assign,
  cases' assign,
  apply ps
end

/-! 1.3 (1 point). Prove the rule for `seq`. -/

lemma seq_intro {P Q R S T} (hS : {* P *} S {* Q *}) (hT : {* Q *} T {* R *}) :
  {* P *} stmt.seq S T {* R *} :=
begin
  rw partial_hoare at *,
  intros s t,
  intro ps,
  intro seq,
  cases' seq,
  apply hT t t_1,
  apply hS s t,
  exact ps,
  exact seq,
  exact seq_1
end

/-! 1.4 (1 point). Prove the rule for `it`. -/

lemma it_intro {b P Q : state → Prop} {S}
    (htrue : {* λs, P s ∧ b s *} S {* Q *}) (hfalse : ∀s, P s ∧ ¬ b s → Q s) :
  {* P *} stmt.it b S {* Q *} :=
begin
  rw partial_hoare at *,
  intros s t,
  intro ps,
  intro it,
  cases' it,
  apply htrue s t,
  apply and.intro,
  exact ps,
  exact hcond,
  exact it,
  apply hfalse t,
  apply and.intro,
  exact ps,
  exact hcond
end

/-! 1.5 (2 points). Prove the rule for `loop`. Notice the similarity with the
rule for `while` in the WHILE language. -/

lemma loop_intro {S} (P : state → Prop) (h : {* P *} S {* P *}) :
  {* P *} stmt.loop S {* P *} :=
begin
  rw partial_hoare at *,
  intros s t,
  intro ps,
  intro loop,
  induction' loop,
  apply ih_loop_1 P h,
  apply ih_loop P h,
  apply h s t,
  exact ps,
  exact loop,
  repeat { sorry } -- TODO
end

end partial_hoare

end loop


/-! ## Question 2 (3 points): Program Verification

The following WHILE program is intended to compute 2 to the power of `n`,
leaving the result in `y`. -/

def POWER_OF_TWO : stmt :=
stmt.assign "y" (λs, 1) ;;
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "y" (λs, s "y" * 2) ;;
   stmt.assign "n" (λs, s "n" - 1))

/-! 2.1 (1 point). Define a recursive function that computes 2 to the power of
`n`. -/

def two_to_the_nth : ℕ → ℕ
| nat.zero     := 1
| (nat.succ n) := 2 * (two_to_the_nth n)

/-! Remember to test your function. Otherwise, you will have big difficulties
answering question 2.2 below. -/

#eval two_to_the_nth 0   -- expected: 1
#eval two_to_the_nth 1   -- expected: 2
#eval two_to_the_nth 2   -- expected: 4
#eval two_to_the_nth 3   -- expected: 8
#eval two_to_the_nth 8   -- expected: 256

/-! 2.2 (2 points). Prove the correctness of `POWER_OF_TWO` using `vcg`. -/

lemma POWER_OF_TWO_correct (n₀ : ℕ) :
  {* λs, s "n" = n₀ *} POWER_OF_TWO {* λs, s "y" = two_to_the_nth n₀ *} :=
show {* λs, s "n" = n₀ ∧ s "y" = 1 *}
     stmt.while_inv (λs, 2 ^ (n₀ - s "n") = s "y")
       (λs, s "n" ≠ 0)
       (stmt.assign "y" (λs, s "y" * 2) ;;
        stmt.assign "n" (λs, s "n" - 1))
     {* λs, s "n" = 0 ∧ s "y" = 2 ^ n₀ *}, from
  begin
    vcg; simp { contextual := tt },
    intros s hny hnz,
    rw ←hny,
    cases s "n",
    { finish },
    {
      sorry
    }
  end

end LoVe
