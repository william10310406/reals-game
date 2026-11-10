import Game.MyReal.RealSeq

World "RealLimits"
Level 1
Title "Small reals"

namespace MyReal

open MyNat (succ)

Introduction "
Now sequences of **reals**: `a : ℕ → ℝ`. *Small* means: at most `eps k`, the real `1/(k+1)`.

* `eps_def k : eps k = ofRat (frac 1 (succ k))`

First: `eps k ≥ 0`.
"

/-- $0 \le \frac{1}{k+1}$ in $\mathbb{R}$. -/
Statement eps_nonneg (k : ℕ) : 0 ≤ eps k := by
  Hint "`rw [eps_def, zero_def]`, then `ofRat_le` and `MyRat.eps_nonneg k`."
  Branch
    rw [le_iff_nonneg]
    Hint "That is the long way. Shorter: `rw [eps_def, zero_def]` and
    `exact ofRat_le _ _ (MyRat.eps_nonneg k)`."
  rw [eps_def, zero_def]
  exact ofRat_le _ _ (MyRat.eps_nonneg k)

Conclusion "
Facts about `ℚ` move to `ℝ` with `ofRat_le` and `ofRat_add`.
"

NewTheorem MyReal.eps_def
NewDefinition MyReal.eps
TheoremTab "limℝ"

end MyReal
