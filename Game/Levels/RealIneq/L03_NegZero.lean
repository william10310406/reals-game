import Game.Levels.RealIneq.L02_AddLeAdd

World "RealIneq"
Level 3
Title "Minus zero"

namespace MyReal

Introduction "
`-0 = 0` in `ℝ`. A small fact we need next.
"

/-- $-0 = 0$ for reals. -/
Statement neg_zero : -(0 : ℝ) = 0 := by
  Hint "Write `0` as a sequence: `rw [zero_def, ofRat_def, ofSeq_neg, ofSeq_eq]`."
  Branch
    rw [zero_def]
    Hint "`ofRat 0` is not of the form `ofSeq …` yet, so `ofSeq_neg` cannot see it.
    Unfold it with `rw [ofRat_def]`."
  rw [zero_def, ofRat_def, ofSeq_neg, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  rw [MyRat.negSeq_apply, MyRat.const_apply, MyRat.neg_zero]

Conclusion "
`-0 = 0`.
"

TheoremTab "ℝ"

end MyReal
