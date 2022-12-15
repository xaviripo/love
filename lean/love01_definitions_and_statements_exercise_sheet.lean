import .love01_definitions_and_statements_demo


/-! # LoVe Exercise 1: Definitions and Statements

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Truncated Subtraction

1.1. Define the function `sub` that implements truncated subtraction on natural
numbers by recursion. "Truncated" means that results that mathematically would
be negative are represented by 0. For example:

    `sub 7 2 = 5`
    `sub 2 7 = 0` -/

def sub : ℕ → ℕ → ℕ
| m 0 := m
| 0 n := 0
| (nat.succ m) (nat.succ n) := sub m n

/-! 1.2. Check that your function works as expected. -/

#eval sub 0 0   -- expected: 0
#eval sub 0 1   -- expected: 0
#eval sub 0 7   -- expected: 0
#eval sub 1 0   -- expected: 1
#eval sub 1 1   -- expected: 0
#eval sub 3 0   -- expected: 3
#eval sub 2 7   -- expected: 0
#eval sub 3 1   -- expected: 2
#eval sub 3 3   -- expected: 0
#eval sub 3 7   -- expected: 0
#eval sub 7 2   -- expected: 5


/-! ## Question 2: Arithmetic Expressions

Consider the type `aexp` from the lecture and the function `eval` that
computes the value of an expression. You will find the definitions in the file
`love01_definitions_and_statements_demo.lean`. One way to find them quickly is
to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `aexp` or `eval`;
3. click the identifier. -/

#check aexp
#check eval

/-! 2.1. Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Make sure to use `#eval`. For technical reasons, `#reduce` does not work well
here. Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `aexp`) are unrelated. -/

def some_env : string → ℤ
| "x" := 3
| "y" := 17
| _   := 201

#eval eval some_env (aexp.var "x")   -- expected: 3
-- invoke `#eval` here

#eval eval some_env (aexp.add (aexp.var "x") (aexp.var "y")) -- expected: 20
#eval eval some_env (aexp.sub (aexp.var "y") (aexp.var "x")) -- expected: 14
#eval eval some_env (aexp.mul (aexp.var "x") (aexp.var "y")) -- expected: 51
#eval eval some_env (aexp.div (aexp.var "y") (aexp.var "x")) -- expected: 5

/-! 2.2. The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : aexp → aexp
| (aexp.add (aexp.num 0) e₂) := simplify e₂
| (aexp.add e₁ (aexp.num 0)) := simplify e₁
-- insert the missing cases here
-- catch-all cases below
| (aexp.num i)               := aexp.num i
| (aexp.var x)               := aexp.var x
| (aexp.add e₁ e₂)           := aexp.add (simplify e₁) (simplify e₂)
| (aexp.sub e₁ e₂)           := aexp.sub (simplify e₁) (simplify e₂)
| (aexp.mul e₁ e₂)           := aexp.mul (simplify e₁) (simplify e₂)
| (aexp.div e₁ e₂)           := aexp.div (simplify e₁) (simplify e₂)

/-! 2.3. Is the `simplify` function correct? In fact, what would it mean for it
to be correct or not? Intuitively, for `simplify` to be correct, it must
return an arithmetic expression that yields the same numeric value when
evaluated as the original expression.

Given an environment `env` and an expression `e`, state (without proving it)
the property that the value of `e` after simplification is the same as the
value of `e` before. -/

lemma simplify_correct (env : string → ℤ) (e : aexp) :
  eval env (simplify e) = eval env e :=  -- replace `true` by your lemma statement
sorry


/-! ## Question 3: λ-Terms

3.1. Complete the following definitions, by replacing the `sorry` markers by
terms of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
λa, a

def K : α → β → α :=
λa b, a

def C : (α → β → γ) → β → α → γ :=
λf, λb a, f a b

def proj_1st : α → α → α :=
λa1 a2, a1

/-! Please give a different answer than for `proj_1st`. -/

def proj_2nd : α → α → α :=
λa1 a2, a2

def some_nonsense : (α → β → γ) → α → (α → γ) → β → γ :=
λf, λa, λg, λb, g a

/-! 3.2. Show the typing derivation for your definition of `C` above, on paper
or using ASCII or Unicode art. You might find the characters `–` (to draw
horizontal bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

/-

    ———————————————————————————------------------------ Cst  ———————————————————————————--------------------- Cst
    f : α → β → γ, a : α, g : α → γ, b : β ⊢ g : α → γ       f : α → β → γ, a : α, g : α → γ, b : β ⊢ a : α
    ————————————————————————————————————————————————————————————————————————————————————————————————————————- App
    f : α → β → γ, a : α, g : α → γ, b : β ⊢ g a : γ
    ————————————————————————————————————————————————---------- Lam
    f : α → β → γ, a : α, g : α → γ, ⊢ (λ b : β, g a) : β → γ
    ————————————————————————————————————————————————--------------------- Lam
    f : α → β → γ, a : α ⊢ (λ g : α → γ, λ b : β, g a) : (α → γ) → β → γ
    ————————————————————————————————————————————————--------------------------- Lam
    f : α → β → γ ⊢ (λ a : α, λ g : α → γ, λ b : β, g a) : α → (α → γ) → β → γ
    ————————————————————————————————————————————————-------------------------------------------- Lam
    ⊢ (λ f : α → β → γ, λ a : α, λ g : α → γ, λ b : β, g a) : (α → β → γ) → α → (α → γ) → β → γ

-/

end LoVe
