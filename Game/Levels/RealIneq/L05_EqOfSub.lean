import Game.Levels.RealIneq.L04_EqZero

World "RealIneq"
Level 5
Title "Zero difference"

namespace MyReal

Introduction "
If `y - x = 0`, then `y = x`. The trick: `y = (y - x) + x`.
"

/-- If $y - x = 0$, then $y = x$ for reals. -/
Statement eq_of_sub_eq_zero (x y : ℝ) : y - x = 0 → y = x := by
  intro h
  Hint "First `have e : y = y - x + x := by` …
  (inside: `sub_eq_add_neg`, `add_assoc`, `add_comm (-x) x`, `add_neg`, `add_zero`)."
  have e : y = y - x + x := by
    rw [sub_eq_add_neg, add_assoc, add_comm (-x) x, add_neg, add_zero]
  Hint "Now `rw [{e}, {h}, zero_add]`."
  rw [e, h, zero_add]

Conclusion "
The same proof as for `ℚ`.
"

TheoremTab "ℝ"

end MyReal
