import .love04_functional_programming_demo


/-! # LoVe Homework 4: Functional Programming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (2 points): Maps

1.1 (1 point). Complete the following definition. The `map_btree` function
should apply its argument `f` to all values of type `α` stored in the tree and
otherwise preserve the tree's structure. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node (f a) (map_btree l) (map_btree r)

/-! 1.2 (1 point). Prove the following lemma about your `map_btree` function. -/

lemma map_btree_iden {α : Type} :
  ∀t : btree α, map_btree (λa, a) t = t :=
fix t,
begin
  induction' t,
  case empty {
    refl
  },
  case node : a _ _ ih_l ih_r {
    simp [map_btree, ih_l, ih_r]
  }
end


/-! ## Question 2 (4 points): Tail-Recursive Factorials

Recall the definition of the factorial functions: -/

#check fact

/-! 2.1 (2 points). Experienced functional programmers tend to avoid definitions
such as the above, because they lead to a deep call stack. Tail recursion can be
used to avoid this. Results are accumulated in an argument and returned. This
can be optimized by compilers. For factorials, this gives the following
definition: -/

def accufact : ℕ → ℕ → ℕ
| a 0       := a
| a (n + 1) := accufact ((n + 1) * a) n

/-! Prove that, given 1 as the accumulator `a`, `accufact` computes `fact`.

Hint: You will need to prove a generalized version of the statement as a
separate lemma or `have`, because the desired property fixes `a` to 1, which
yields a too weak induction hypothesis. -/

lemma accufact_eq_fact (n : ℕ) (a : ℕ):
  accufact a n = a * fact n :=
begin
  induction' n,
  case nat.zero {
    simp [accufact, fact]
  },
  case nat.succ {
    rw fact,
    rw ←mul_assoc,
    rw mul_comm,
    rw ←mul_assoc,
    rw [mul_comm _ a],
    rw accufact,
    rw ih,
    cc
  }
end

lemma accufact_1_eq_fact (n : ℕ) :
  accufact 1 n = fact n :=
calc  accufact 1 n
    = 1 * fact n :
  accufact_eq_fact n 1
... = fact n :
  by rw one_mul

/-! 2.2 (2 points). Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

/-

Lemma. ∀n : ℕ, ∀a : N, accufact a n = a * fact n.
Proof.

Fix an arbitrary a. By induction on n.

- Base case. We need to prove accufact a 0 = a * fact 0.

    accufact a 0 =
      (by definition of accufact)
    = a =
      (by 1 being the identity element of the product)
    = a * 1 =
      (by definition of fact)
    = a * fact 0

- Inductive case. We need to prove accufact a (n + 1) = a * fact (n + 1),
  assuming that ∀a' : ℕ, accufact a' n = a' * fact n.

    accufact a (n + 1) =
      (by definition of accufact)
    = accufact ((n + 1) * a) n
      (by the induction hypothesis, with a' := (n + 1) * a)
    = ((n + 1) * a) * fact n
      (by commutativity and associativity of the product)
    = a * ((n + 1) * fact n)
      (by definition of fact)
    = a * fact (n + 1)

Qed.

Lemma. ∀n : N, accufact 1 n = fact n.
Proof.

  accufact 1 n =
    (by the previous lemma, with a = 1)
  = 1 * fact n =
    (by 1 being the identity element of the product)
  = fact n

Qed.

-/


/-! ## Question 3 (3 points): Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/-! 3.1 (2 point). Prove the following lemma, discovered by Carl Friedrich Gauss
as a pupil.

Hint: The `mul_add` and `add_mul` lemmas might be useful to reason about
multiplication. -/

#check mul_add
#check add_mul

lemma sum_upto_eq :
  ∀m : ℕ, 2 * sum_upto (λi, i) m = m * (m + 1) :=
begin
  intro m,
  induction' m,
  case nat.zero {
    simp [sum_upto]
  },
  case nat.succ {
    simp [sum_upto],
    rw mul_add,
    rw ih,
    rw ←add_mul,
    rw mul_comm
  }
end

/-! 3.2 (1 point). Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sum_upto (λi, f i + g i) n = sum_upto f n + sum_upto g n :=
begin
  intro n,
  induction' n,
  case nat.zero {
    simp [sum_upto]
  },
  case nat.succ {
    simp [sum_upto, ih],
    cc
  }
end

end LoVe
