import Game.Levels.RealArith.L15_MulAssoc

World "RealArith"
Level 16
Title "One"

namespace MyReal

Introduction "
`one_def : (1 : ℝ) = ofRat 1`.
"

/-- $x \cdot 1 = x$ for reals. -/
Statement mul_one (x : ℝ) : x * 1 = x := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "Write `1` as a sequence: `rw [one_def, ofRat_def]`."
  Branch
    rw [mul_comm]
    Hint "Swapping does not help: `1` is still not a sequence. Use `rw [one_def, ofRat_def]`."
  rw [one_def, ofRat_def, ofSeq_mul, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "`MyRat.mulSeq_apply`, `MyRat.const_apply`, `MyRat.mul_one`."
  rw [MyRat.mulSeq_apply, MyRat.const_apply, MyRat.mul_one]

Conclusion "
`1` is neutral for `*` on `ℝ`.
"

NewTheorem MyReal.one_def
TheoremTab "ℝ"

end MyReal
