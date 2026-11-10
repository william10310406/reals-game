import Game.Levels.RealOrder.L17_RatAbsBounds

World "RealOrder"
Level 18
Title "Bounding |c|"

namespace MyRat

Introduction "
To show `abs c ≤ d`, show `c ≤ d` and `-c ≤ d`.
"

/-- If $c \le d$ and $-c \le d$, then $|c| \le d$. -/
Statement abs_le (c d : ℚ) : c ≤ d → -c ≤ d → abs c ≤ d := by
  intro h1 h2
  Hint "`by_cases h : nonneg c`."
  by_cases h : nonneg c
  · rw [abs_of_nonneg h]
    exact h1
  · rw [abs_of_not_nonneg h]
    exact h2

Conclusion "
`apply abs_le` turns a goal `abs c ≤ d` into two goals without `abs`.
"

TheoremTab "abs"

end MyRat
