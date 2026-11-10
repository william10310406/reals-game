import Game.Levels.Naturals.L10_ZeroMul

World "Naturals"
Level 11
Title "succ times b"

namespace MyNat

Introduction "
This one is longer. Take it one rewrite at a time.
"

/-- $\operatorname{succ}(a) \cdot b = a \cdot b + b$. -/
Statement succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  Hint "Induction on `b`."
  induction b with d hd
  · Hint "Remove `* 0` twice and `+ 0` once."
    rw [mul_zero, mul_zero, add_zero]
  · Hint "Use `mul_succ` twice, then `{hd}`."
    rw [mul_succ, mul_succ, hd]
    Hint "Move the `succ` out of both sums with `add_succ`."
    rw [add_succ, add_succ]
    Hint "Inside the `succ` you have two sums of the same three numbers.
    Use `add_assoc` twice, then `add_comm` on the right pair."
    rw [add_assoc, add_assoc, add_comm d a]

Conclusion "
Long rewrite chains are normal. Look at the goal after each step.
"

TheoremTab "*"

end MyNat
