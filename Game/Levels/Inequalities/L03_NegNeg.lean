import Game.Levels.Inequalities.L02_IntNegNeg

World "Inequalities"
Level 3
Title "Minus minus in ℚ"

namespace MyRat

Introduction "
Now the same for `ℚ`.
"

/-- $-(-x) = x$ for rationals. -/
Statement neg_neg (x : ℚ) : -(-x) = x := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  Hint "Use `neg_frac` twice, then `MyInt.neg_neg`."
  Branch
    rw [neg_frac, neg_frac]
    Hint "Now `-(-a)` is in `ℤ`: use `MyInt.neg_neg`."
  rw [neg_frac, neg_frac, MyInt.neg_neg]

Conclusion "
`neg_neg` is in your inventory.
"

TheoremTab "ℚ"

end MyRat
