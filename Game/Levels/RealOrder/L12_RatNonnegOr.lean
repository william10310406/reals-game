import Game.Levels.RealOrder.L11_IntNonnegOr

World "RealOrder"
Level 12
Title "Signs in ℚ"

namespace MyRat

Introduction "
The same for `ℚ`. A fraction has the sign of its numerator.
"

/-- For rationals, $x \ge 0$ or $-x \ge 0$. -/
Statement nonneg_or_nonneg_neg (x : ℚ) : nonneg x ∨ nonneg (-x) := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  Hint "`rw [neg_frac, nonneg_frac {hb}, nonneg_frac {hb}]`, then the last level."
  Branch
    rw [nonneg_frac hb]
    Hint "`-frac a b` is not a fraction yet. Use `neg_frac` first."
  rw [neg_frac, nonneg_frac hb, nonneg_frac hb]
  exact MyInt.nonneg_or_nonneg_neg a

Conclusion "
Every rational has a sign.
"

TheoremTab "ℚ"

end MyRat
