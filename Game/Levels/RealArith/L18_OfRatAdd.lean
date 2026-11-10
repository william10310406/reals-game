import Game.Levels.RealArith.L17_MulAdd

World "RealArith"
Level 18
Title "ℚ inside ℝ: sums"

namespace MyReal

Introduction "
`ofRat` puts `ℚ` inside `ℝ`. It should keep sums: adding in `ℚ` first, or in `ℝ` afterwards,
gives the same real.
"

/-- $\iota(a + b) = \iota(a) + \iota(b)$ for the embedding $\iota : \mathbb{Q} \to \mathbb{R}$. -/
Statement ofRat_add (a b : ℚ) : ofRat (a + b) = ofRat a + ofRat b := by
  Hint "Unfold `ofRat` three times with `ofRat_def`, then `ofSeq_add` and `ofSeq_eq`."
  Branch
    rw [ofRat_def]
    Hint "Only the first `ofRat` was unfolded. `ofSeq_add` needs both summands as sequences:
    `rw [ofRat_def, ofRat_def]` for the other two."
  rw [ofRat_def, ofRat_def, ofRat_def, ofSeq_add, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "`MyRat.const_apply` and `MyRat.addSeq_apply` until both sides are `a + b`."
  rw [MyRat.const_apply, MyRat.addSeq_apply, MyRat.const_apply, MyRat.const_apply]

Conclusion "
`ofRat` keeps sums.
"

TheoremTab "ℝ"

end MyReal
