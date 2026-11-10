import Game.Levels.RealIneq.L05_EqOfSub

World "RealIneq"
Level 6
Title "ℚ inside ℝ: order"

namespace MyReal

Introduction "
`ofRat` keeps `≤`: if `a ≤ b` in `ℚ`, then `ofRat a ≤ ofRat b` in `ℝ`.
"

/-- If $a \le b$ in $\mathbb{Q}$, then $\iota(a) \le \iota(b)$ in $\mathbb{R}$. -/
Statement ofRat_le (a b : ℚ) : a ≤ b → ofRat a ≤ ofRat b := by
  intro h
  Hint "`rw [ofRat_def, ofRat_def]`, then `apply le_of_eventually`."
  rw [ofRat_def, ofRat_def]
  apply le_of_eventually
  use 0
  intro n hn
  rw [MyRat.const_apply, MyRat.const_apply]
  exact h

Conclusion "
`ℚ` sits inside `ℝ` with the same `+`, `*` and `≤`.
"

TheoremTab "≤ℝ"

end MyReal
