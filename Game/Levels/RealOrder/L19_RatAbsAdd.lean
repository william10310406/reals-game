import Game.Levels.RealOrder.L18_RatAbsLe

World "RealOrder"
Level 19
Title "Triangle inequality in ℚ"

namespace MyRat

Introduction "
`abs (a + b) ≤ abs a + abs b`. No case split needed: use the last two levels.
"

/-- $|a + b| \le |a| + |b|$ for rationals. -/
Statement abs_add (a b : ℚ) : abs (a + b) ≤ abs a + abs b := by
  Hint "`obtain ⟨a1, a2⟩ := abs_bounds a` and the same for `b`."
  obtain ⟨a1, a2⟩ := abs_bounds a
  obtain ⟨b1, b2⟩ := abs_bounds b
  Hint "Now `apply abs_le`."
  Branch
    by_cases h : nonneg (a + b)
    Hint "Cases work, but there are many. Faster: `apply abs_le`, then `add_le_add`."
  apply abs_le
  · exact add_le_add _ _ _ _ a1 b1
  · Hint "`rw [neg_add]` first."
    rw [neg_add]
    exact add_le_add _ _ _ _ a2 b2

Conclusion "
The triangle inequality for `ℚ`.
"

TheoremTab "abs"

end MyRat
