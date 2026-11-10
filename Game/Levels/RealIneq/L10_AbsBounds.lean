import Game.Levels.RealIneq.L09_AbsSubComm

World "RealIneq"
Level 10
Title "x and -x are below |x|"

namespace MyReal

Introduction "
Both `x` and `-x` are `≤ abs x`. Term by term, with `le_of_eventually` and `MyRat.abs_bounds`.
"

/-- $x \le |x|$ and $-x \le |x|$ for reals. -/
Statement abs_bounds (x : ℝ) : x ≤ abs x ∧ -x ≤ abs x := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  rw [ofSeq_abs, ofSeq_neg]
  constructor
  · apply le_of_eventually
    use 0
    intro n hn
    rw [MyRat.absSeq_apply]
    Hint "`obtain ⟨b1, b2⟩ := MyRat.abs_bounds (s n)`."
    obtain ⟨b1, b2⟩ := MyRat.abs_bounds (s n)
    exact b1
  · apply le_of_eventually
    use 0
    intro n hn
    rw [MyRat.absSeq_apply, MyRat.negSeq_apply]
    obtain ⟨b1, b2⟩ := MyRat.abs_bounds (s n)
    exact b2

Conclusion "
Use it as `obtain ⟨h1, h2⟩ := abs_bounds x`.
"

TheoremTab "abs"

end MyReal
