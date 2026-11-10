import Game.Levels.RealArith.L18_OfRatAdd

World "RealArith"
Level 19
Title "ℚ inside ℝ: products"

namespace MyReal

Introduction "
Last level of this world: `ofRat` keeps products too.
"

/-- $\iota(ab) = \iota(a)\,\iota(b)$ for the embedding $\iota : \mathbb{Q} \to \mathbb{R}$. -/
Statement ofRat_mul (a b : ℚ) : ofRat (a * b) = ofRat a * ofRat b := by
  rw [ofRat_def, ofRat_def, ofRat_def, ofSeq_mul, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  rw [MyRat.const_apply, MyRat.mulSeq_apply, MyRat.const_apply, MyRat.const_apply]

Conclusion "
`ℚ` sits inside `ℝ` with the same `+` and `*`.
"

TheoremTab "ℝ"

end MyReal
