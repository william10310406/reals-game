import Game.Levels.Naturals.L11_SuccMul

World "Naturals"
Level 12
Title "Multiplication is commutative"

namespace MyNat

Introduction "
Use induction and your new theorems.
"

/-- $a \cdot b = b \cdot a$. -/
Statement mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with d hd
  · Hint "`a * 0 = 0 * a`. You have a theorem for each side."
    rw [mul_zero, zero_mul]
  · Hint "Use `mul_succ` on the left and `succ_mul` on the right. Then `{hd}`."
    rw [mul_succ, succ_mul, hd]

Conclusion "
Now `mul_comm` is yours.
"

TheoremTab "*"

end MyNat
