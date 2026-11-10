import Game.Levels.RealArith.L10_NegAdd

World "RealArith"
Level 11
Title "Double negative"

namespace MyReal

Introduction "
You proved `MyRat.neg_neg` in the Inequalities world. Now for `ℝ`.
"

/-- $-(-x) = x$ for reals. -/
Statement neg_neg (x : ℝ) : -(-x) = x := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "`rw [ofSeq_neg, ofSeq_neg, ofSeq_eq]`."
  rw [ofSeq_neg, ofSeq_neg, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "Compute with `MyRat.negSeq_apply` twice, then `MyRat.neg_neg`."
  rw [MyRat.negSeq_apply, MyRat.negSeq_apply, MyRat.neg_neg]

Conclusion "
Two minus signs cancel.
"

TheoremTab "ℝ"

end MyReal
