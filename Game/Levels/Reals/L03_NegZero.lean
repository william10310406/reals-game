import Game.Levels.Reals.L02_SuccNeZero

World "Reals"
Level 3
Title "Minus zero"

namespace MyRat

Introduction "
A small fact we need: `-0 = 0` in `ℚ`.
"

/-- $-0 = 0$ in $\mathbb{Q}$. -/
Statement neg_zero : -(0 : ℚ) = 0 := by
  Hint "Write `0` as a fraction, use `neg_frac`, then write the integer `0` as `mk 0 0`."
  rw [zero_def, neg_frac, MyInt.zero_def, MyInt.neg_mk]

Conclusion "
`neg_zero` is in your inventory.
"

TheoremTab "ℚ"

end MyRat
