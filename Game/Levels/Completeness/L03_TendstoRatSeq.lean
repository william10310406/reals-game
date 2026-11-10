import Game.Levels.Completeness.L02_AbsSubLe

World "Completeness"
Level 3
Title "A real is a limit of rationals"

namespace MyReal

open MyNat (succ)

Introduction "
`ratSeq q` is the sequence `ofRat (q 0), ofRat (q 1), …` (`ratSeq_apply`).

If `q` is a Cauchy sequence of rationals, then `ofSeq q hq` is a real.
Show: the rationals `q n`, seen in `ℝ`, tend to it. So every real is a limit of rationals.
"

/-- If $q$ is a Cauchy sequence of rationals, then $q_n \to$ the real of $q$ in $\mathbb{R}$. -/
Statement tendsto_ratSeq (q : ℕ → ℚ) (hq : MyRat.IsCauchy q) : Tendsto (ratSeq q) (ofSeq q hq) := by
  intro k
  obtain ⟨N, hN⟩ := hq k
  use N
  intro n hn
  Hint "Write everything as sequences:
  `rw [ratSeq_apply, ofRat_def, sub_eq_add_neg, ofSeq_neg, ofSeq_add, ofSeq_abs, eps_def, ofRat_def]`."
  rw [ratSeq_apply, ofRat_def, sub_eq_add_neg, ofSeq_neg, ofSeq_add, ofSeq_abs, eps_def, ofRat_def]
  Hint "Compare the terms: `apply le_of_eventually`, `use N`, `intro i hi`."
  apply le_of_eventually
  use N
  intro i hi
  rw [MyRat.absSeq_apply, MyRat.addSeq_apply, MyRat.const_apply, MyRat.negSeq_apply,
    MyRat.const_apply, ← MyRat.sub_eq_add_neg]
  Hint "`apply MyRat.abs_le`, then `hN`."
  apply MyRat.abs_le
  · exact hN n i hn hi
  · rw [MyRat.neg_sub]
    exact hN i n hi hn

Conclusion "
`ℚ` is dense in `ℝ`: every real is a limit of rationals.
"

NewTheorem MyReal.ratSeq_apply
NewDefinition MyReal.ratSeq
TheoremTab "limℝ"

end MyReal
