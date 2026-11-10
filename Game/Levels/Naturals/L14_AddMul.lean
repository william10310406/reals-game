import Game.Levels.Naturals.L13_MulAdd

World "Naturals"
Level 14
Title "Distributivity on the right"

namespace MyNat

Introduction "
No induction needed. Turn the product around and use `mul_add`.
"

/-- $(a + b) c = ac + bc$. -/
Statement add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  Hint "`rw [mul_comm]` swaps the first product it finds."
  rw [mul_comm]
  Hint "Now multiply out with `mul_add`."
  rw [mul_add]
  Hint "Make the right side look like the left: `rw [mul_comm a c, mul_comm b c]`."
  rw [mul_comm a c, mul_comm b c]

Conclusion "
Using a theorem is often shorter than a new induction.
"

TheoremTab "*"

end MyNat
