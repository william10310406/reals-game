import Game.Levels.Naturals.L09_EqZero

World "Naturals"
Level 10
Title "Multiplication"

namespace MyNat

Introduction "
Multiplication has two rules too:

* `mul_zero : a * 0 = 0`
* `mul_succ : a * succ b = a * b + a`

Show that `0 * n = 0`.
"

/-- $0 \cdot n = 0$. -/
Statement zero_mul (n : ℕ) : 0 * n = 0 := by
  Hint "Induction on `n`."
  induction n with d hd
  · rw [mul_zero]
  · Hint "Use `mul_succ`, then `{hd}`, then `add_zero`."
    rw [mul_succ, hd, add_zero]

Conclusion "
Same pattern as `zero_add`.
"

NewTheorem MyNat.mul_zero MyNat.mul_succ
NewDefinition MyNat.mul
TheoremTab "*"

end MyNat
