import Game.Levels.RealLimits.L02_EpsHalf

World "RealLimits"
Level 3
Title "Smaller and smaller"

namespace MyReal

Introduction "
A bigger index gives a smaller `eps`. You proved this for `ℚ` (`MyRat.inv_le_inv`).
"

/-- If $k \le n$, then $\frac{1}{n+1} \le \frac{1}{k+1}$ in $\mathbb{R}$. -/
Statement eps_le (k n : ℕ) : k ≤ n → eps n ≤ eps k := by
  intro h
  rw [eps_def n, eps_def k]
  exact ofRat_le _ _ (MyRat.inv_le_inv k n h)

Conclusion "
`eps_le` is in your inventory.
"

TheoremTab "limℝ"

end MyReal
