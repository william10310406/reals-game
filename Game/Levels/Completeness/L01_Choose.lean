import Game.MyReal.Complete

World "Completeness"
Level 1
Title "Choosing"

Introduction "
The last world. Goal: **every Cauchy sequence of reals converges**.

The plan: next to each real `a n`, pick a rational `q n`. The rationals `q n` form a Cauchy
sequence, so they *are* a real `L`. Then show `a → L`.

To pick one `q n` for every `n` at once, you need a new tool.
`choose f hf using h` turns `h : ∀ n, ∃ y, P n y` into a function `f` and
`hf : ∀ n, P n (f n)`. (This is the axiom of choice.)
"

/-- If every $n$ has some $m$ with $P(n, m)$, then there is a function $f$ with $P(n, f(n))$. -/
Statement (P : ℕ → ℕ → Prop) : (∀ n, ∃ m, P n m) → ∃ f : ℕ → ℕ, ∀ n, P n (f n) := by
  intro h
  Hint "`choose f hf using {h}`."
  Branch
    obtain ⟨m, hm⟩ := h 0
    Hint "This gives one value, for `n = 0` only. A function needs one for every `n`:
    `choose f hf using {h}`."
  choose f hf using h
  use f
  exact hf

Conclusion "
`choose` builds a whole function out of `∀ … ∃ …`.
"

NewTactic choose
TheoremTab "logic"
