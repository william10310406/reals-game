import Game.Levels.Completeness.L08_TendstoOfNear

World "Completeness"
Level 9
Title "ℝ is complete"

namespace MyReal

Introduction "
Final boss. **Every Cauchy sequence of reals converges.**

1. Pick a rational `q n` next to each `a n` (`exists_rat_near` and `choose`).
2. `q` is a Cauchy sequence of rationals (`cauchy_ratSeq`, `rat_cauchy`), so it is a real `L`.
3. `ratSeq q → L` (`tendsto_ratSeq`), so `a → L` (`tendsto_of_near`).
"

/-- Every Cauchy sequence of real numbers converges. -/
Statement complete (a : ℕ → ℝ) : IsCauchy a → ∃ L, Tendsto a L := by
  intro ha
  Hint "First the rationals: `have h : ∀ n, ∃ q : ℚ, abs (a n - ofRat q) ≤ eps n := by …`
  (`intro n`, then `exists_rat_near`)."
  have h : ∀ n, ∃ q : ℚ, abs (a n - ofRat q) ≤ eps n := by
    intro n
    exact exists_rat_near (a n) n
  Hint "`choose q hq using {h}`."
  Branch
    obtain ⟨q, hq⟩ := h 0
    Hint "This picks one rational, for `n = 0` only. You need one for every `n`:
    `choose q hq using {h}`."
  choose q hq using h
  Hint "`have hc := rat_cauchy q (cauchy_ratSeq a q {ha} {hq})`."
  have hc := rat_cauchy q (cauchy_ratSeq a q ha hq)
  Hint "The limit is the real of `q`: `use ofSeq q {hc}`."
  use ofSeq q hc
  exact tendsto_of_near a (ratSeq q) (ofSeq q hc) (tendsto_ratSeq q hc) hq

Conclusion "
**`ℝ` is complete.** You built the real numbers from logic: `ℕ`, `ℤ`, `ℚ`, then `ℝ` as Cauchy
sequences, with `+`, `*`, `≤`, `abs`, limits, and now completeness. Every step used only theorems
you proved yourself.
"

TheoremTab "limℝ"

end MyReal
