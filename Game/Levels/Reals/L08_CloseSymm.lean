import Game.Levels.Reals.L07_CloseRefl

World "Reals"
Level 8
Title "Close is symmetric"

namespace MyRat

Introduction "
To use `h : Close s t`, give it a `k`: `h k` says that some `N` works.
"

/-- If $s$ is close to $t$, then $t$ is close to $s$. -/
Statement close_symm (s t : ℕ → ℚ) : Close s t → Close t s := by
  intro h
  intro k
  Hint "Get an `N` from `{h}`: `obtain ⟨N, hN⟩ := {h} k`."
  Branch
    use k
    Hint "Which `N`? Get it from `{h}` first: `obtain ⟨N, hN⟩ := {h} k`."
  obtain ⟨N, hN⟩ := h k
  use N
  intro n hn
  Hint "`{hN} n {hn}` gives both inequalities. Take them apart with `obtain`."
  obtain ⟨h1, h2⟩ := hN n hn
  constructor
  exact h2
  exact h1

Conclusion "
The definition of `Close` treats `s` and `t` the same way.
"

TheoremTab "ℚ"

end MyRat
