import Game.Levels.RealArith.L06_AddAssoc

World "RealArith"
Level 7
Title "Zero"

namespace MyReal

Introduction "
A rational `q` is a real number: the constant sequence `q, q, q, …`.
We call it `ofRat q`.

* `ofRat_def q : ofRat q = ofSeq (MyRat.const q) (MyRat.const_cauchy q)`
* `zero_def : (0 : ℝ) = ofRat 0`
"

/-- $x + 0 = x$ for reals. -/
Statement add_zero (x : ℝ) : x + 0 = x := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "Write `0` as a sequence: `rw [zero_def, ofRat_def]`."
  Branch
    rw [add_comm]
    Hint "Swapping does not help: `0` is still not a sequence.
    Write it as one with `rw [zero_def, ofRat_def]`."
  rw [zero_def, ofRat_def]
  Hint "Now as before: `ofSeq_add`, `ofSeq_eq`, `apply MyRat.close_of_eq`, `intro n`."
  rw [ofSeq_add, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "Compute: `MyRat.addSeq_apply`, `MyRat.const_apply`, then `MyRat.add_zero`."
  rw [MyRat.addSeq_apply, MyRat.const_apply, MyRat.add_zero]

Conclusion "
`0` is neutral for `+` on `ℝ`.
"

NewTheorem MyReal.ofRat_def MyReal.zero_def
NewDefinition MyReal.ofRat
TheoremTab "ℝ"

end MyReal
