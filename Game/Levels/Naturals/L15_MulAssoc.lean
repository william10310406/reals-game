import Game.Levels.Naturals.L14_AddMul

World "Naturals"
Level 15
Title "Brackets again"

namespace MyNat

Introduction "
Show that brackets do not matter for multiplication either.
"

/-- $(ab)c = a(bc)$. -/
Statement mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by
  Hint "Induction on `c`."
  induction c with d hd
  · rw [mul_zero, mul_zero, mul_zero]
  · Hint "Use `mul_succ` twice, then `mul_add`, then `{hd}`."
    rw [mul_succ, mul_succ, mul_add, hd]

Conclusion "
`ℕ` with `+` and `*` now has all the usual rules.
"

TheoremTab "*"

end MyNat
