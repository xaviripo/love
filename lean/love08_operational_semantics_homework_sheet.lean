import .lovelib


/-! # LoVe Homework 8: Operational Semantics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points + 1 bonus point): Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| unless : (state → Prop) → stmt → stmt
| repeat : ℕ → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/-! The `skip`, `assign`, and `S ;; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b S` statement executes `S` unless `b` is true—i.e., it executes `S`
if `b` is false. Otherwise, `unless b S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S ;; S ;; S ;; S ;; S` (as far as the big-step semantics
is concerned), and `repeat 0 S` has the same effect as `skip`.

1.1 (1.5 points). Complete the following definition of a big-step
semantics: -/

inductive big_step : stmt × state → state → Prop
| skip {s} :
  big_step (stmt.skip, s) s
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (S ;; T, s) u
| unless_true {b : state → Prop} {S s} (hcond : b s) :
  big_step (stmt.unless b S, s) s
| unless_false {b : state → Prop} {S s t} (hcond : ¬ b s)
    (hbody : big_step (S, s) t) :
  big_step (stmt.unless b S, s) t
| repeat_zero {S s} :
  big_step (stmt.repeat nat.zero S, s) s
| repeat_succ {n S s t u}
    (hbody : big_step (S, s) t)
    (hrest : big_step (stmt.repeat n S, t) u) :
  big_step (stmt.repeat (nat.succ n) S, s) u

infix ` ⟹ ` : 110 := big_step

/-! 1.2 (1.5 points). Complete the following definition of a small-step
semantics: -/

inductive small_step : stmt × state → stmt × state → Prop
| assign {x a s} :
  small_step (stmt.assign x a, s) (stmt.skip, s{x ↦ a s})
| seq_step {S S' T s s'} (hS : small_step (S, s) (S', s')) :
  small_step (S ;; T, s) (S' ;; T, s')
| seq_skip {T s} :
  small_step (stmt.skip ;; T, s) (T, s)
| unless_true {b : state → Prop} {S s} (hcond : b s) :
  small_step (stmt.unless b S, s) (stmt.skip, s)
| unless_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  small_step (stmt.unless b S, s) (S, s)
| repeat_zero {S s} :
  small_step (stmt.repeat nat.zero S, s) (stmt.skip, s)
| repeat_succ {n S s} :
  small_step (stmt.repeat (nat.succ n) S, s) (S ;; stmt.repeat n S, s)

infixr ` ⇒ ` := small_step
infixr ` ⇒* ` : 100 := star small_step

/-! 1.3 (1 point). We will now attempt to prove termination of the REPEAT
language. More precisely, we will show that there cannot be infinite chains of
the form

    `(S₀, s₀) ⇒ (S₁, s₁) ⇒ (S₂, s₂) ⇒ ⋯`

Towards this goal, you are asked to define a __measure__ function: a function
`mess` that takes a statement `S` and that returns a natural number indicating
how "big" the statement is. The measure should be defined so that it strictly
decreases with each small-step transition. -/

def mess : stmt → ℕ
| stmt.skip         := 0
| (stmt.assign x a) := 1
| (stmt.seq S T)    := 1 + mess S + mess T
| (stmt.unless b S) := 1 + mess S
| (stmt.repeat n S) := n * (2 + mess S) + 1

/-! 1.4 (1 point). Consider the following program `S₀`: -/

def incr (x : string) : stmt :=
stmt.assign x (λs, s x + 1)

def S₀ : stmt :=
stmt.repeat 1 (incr "m" ;; incr "n")

/-! Check that `mess` strictly decreases with each step of its small-step
evaluation, by giving `S₀`, `S₁`, `S₂`, …, as well as the corresponding values
of `mess` (which you can obtain using `#eval`). -/

def S₁ : stmt :=
incr "m" ;; incr "n" ;; stmt.repeat 0 (incr "m" ;; incr "n")

def S₂ : stmt :=
stmt.skip ;; incr "n" ;; stmt.repeat 0 (incr "m" ;; incr "n")

def S₃ : stmt :=
incr "n" ;; stmt.repeat 0 (incr "m" ;; incr "n")

def S₄ : stmt :=
stmt.skip ;; stmt.repeat 0 (incr "m" ;; incr "n")

def S₅ : stmt :=
stmt.repeat 0 (incr "m" ;; incr "n")

def S₆ : stmt :=
stmt.skip

#eval mess S₀
#eval mess S₁
#eval mess S₂
#eval mess S₃
#eval mess S₄
#eval mess S₅
#eval mess S₆

/-! 1.5 (1 point). Prove that the measure decreases with each small-step
transition. If necessary, revise your answer to question 1.3. -/

lemma small_step_mess_decreases {Ss Tt : stmt × state} (h : Ss ⇒ Tt) :
  mess (prod.fst Ss) > mess (prod.fst Tt) :=
begin
  induction' h,
  any_goals { simp [mess] },
  case small_step.seq_step {
    simp at ih,
    exact ih
  },
  case small_step.unless_true {
    linarith
  },
  case small_step.repeat_succ {
    rw add_assoc,
    rw add_comm,
    apply add_lt_add_right,
    rw ←nat.add_one,
    linarith
  }
end

/-! 1.6 (1 bonus point). Prove that the inverse of the `⇒` relation is well
founded. The inverse is simply `λTt Ss, Ss ⇒ Tt`. A relation `≺` is well founded
if there exist no infinite left-descending chains of the form

    `⋯ ≺ x₂ ≺ x₁ ≺ x₀`

Proof strategy: The `measure` function from `mathlib` converts a function to `ℕ`
to a relation, using `<` to compare two numbers. Hence, start by proving that
`measure mess`, or rather `measure (mess ∘ prod.fst)`, is well founded. Here,
`library_search` can help, or just search manually in `wf.lean`, close to the
definition of `measure`. Then prove that `λTt Ss, Ss ⇒ Tt` is a subrelation of
`measure (mess ∘ prod.fst)` (using lemma `small_step_mess_decreases` from
question 1.5) and therefore (using another lemma from `wf.lean`) that it must be
well founded. -/

lemma small_step_wf :
  well_founded (λTt Ss, Ss ⇒ Tt) :=
sorry


/-! ## Question 2 (3 points): Inversion Rules

2.1 (1 point). Prove the following inversion rule for the big-step semantics
of `unless`. -/

lemma big_step_ite_iff {b S s t} :
  (stmt.unless b S, s) ⟹ t ↔ (b s ∧ s = t) ∨ (¬ b s ∧ (S, s) ⟹ t) :=
begin
  apply iff.intro,
  {
    intro p,
    cases' p,
    case unless_true {
      apply or.intro_left,
      apply and.intro,
      apply hcond,
      refl
    },
    case unless_false {
      apply or.intro_right,
      apply and.intro,
      apply hcond,
      exact p,
    }
  },
  {
    intro p,
    cases' p,
    case or.inl {
      cases' h,
      rw ←right,
      apply (big_step.unless_true left)
    },
    case or.inr {
      cases' h,
      apply (big_step.unless_false left right)
    }
  }
end

/-! 2.2 (2 points). Prove the following inversion rule for the big-step
semantics of `repeat`. -/

lemma big_step_repeat_iff {n S s u} :
  (stmt.repeat n S, s) ⟹ u ↔
  (n = 0 ∧ u = s)
  ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (stmt.repeat m S, t) ⟹ u) :=
begin
  apply iff.intro,
  {
    intro p,
    induction' n,
    case nat.zero {
      apply or.intro_left,
      simp,
      induction' p,
      simp
    },
    case nat.succ {
      apply or.intro_right,
      apply exists.intro n,
      simp,
      cases p,
      apply exists.intro p_t,
      apply and.intro,
      exact p_hbody,
      exact p_hrest
    }
  },
  {
    intro p,
    cases' p,
    case or.inl {
      cases' h,
      rw [left, right],
      apply big_step.repeat_zero
    },
    case or.inr {
      cases' h,
      cases' h,
      cases' h,
      rw left,
      cases' right,
      apply big_step.repeat_succ left_1 right
    }
  }
end

end LoVe
