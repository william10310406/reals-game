import Game.Levels.Inequalities.L07_NegSub

World "Inequalities"
Level 8
Title "Difference zero"

namespace MyRat

Introduction "
If `y - x = 0`, then `y = x`. The trick: `y = (y - x) + x`.
"

/-- If $y - x = 0$, then $y = x$. -/
Statement eq_of_sub_eq_zero (x y : ℚ) : y - x = 0 → y = x := by
  intro h
  Hint "First `have e : y = y - x + x := by` …
  (inside: `sub_eq_add_neg`, `add_assoc`, `add_comm (-x) x`, `add_neg`, `add_zero`)."
  Branch
    rw [sub_eq_add_neg] at h
    Hint "The trick is `y = (y - x) + x`. Prove it first with `have e : y = y - x + x := by …`."
  have e : y = y - x + x := by
    rw [sub_eq_add_neg, add_assoc, add_comm (-x) x, add_neg, add_zero]
  Hint "Now `rw [{e}, {h}]`, then clean up `0 + x` with `add_comm` and `add_zero`."
  rw [e, h, add_comm, add_zero]

Conclusion "
Adding and subtracting the same number changes nothing.
"

TheoremTab "ℚ"

end MyRat
