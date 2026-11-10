import Game.Levels.Reals.L08_CloseSymm

World "Reals"
Level 9
Title "Close is transitive"

namespace MyRat

open MyNat (succ)

Introduction "
Boss level. If `s` is close to `t`, and `t` to `u`, then `s` is close to `u`.

The idea: for `1/(k+1)`, ask both hypotheses for half of it.
Half of `1/(k+1)` is `1/(succ k + succ k)`, which is `frac 1 (succ (succ k + k))` (by `MyNat.add_succ`).
So ask for index `succ k + k`.

Then take `N₁ + N₂`, which is bigger than both.
"

/-- If $s$ is close to $t$ and $t$ is close to $u$, then $s$ is close to $u$. -/
Statement close_trans (s t u : ℕ → ℚ) : Close s t → Close t u → Close s u := by
  intro hst htu k
  Hint "Ask for half: `obtain ⟨N1, h1⟩ := {hst} (succ k + k)`, and the same with `{htu}`."
  obtain ⟨N1, h1⟩ := hst (succ k + k)
  obtain ⟨N2, h2⟩ := htu (succ k + k)
  use N1 + N2
  intro n hn
  Hint "Show `N1 ≤ n`: `have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) {hn}`."
  have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) hn
  Hint "For `N2 ≤ n`, first swap the sum in `{hn}` with `MyNat.add_comm`."
  rw [MyNat.add_comm] at hn
  have hn2 : N2 ≤ n := MyNat.le_trans N2 (N2 + N1) n (MyNat.le_add_right N2 N1) hn
  obtain ⟨a1, a2⟩ := h1 n hn1
  obtain ⟨b1, b2⟩ := h2 n hn2
  Hint "Split `1/(k+1)` into two halves:
  `rw [← half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ]`."
  rw [← half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ]
  constructor
  · Hint "Split `s n - u n` at `t n`: `rw [← sub_add_sub (u n) (t n) (s n)]`. Then `add_le_add`."
    rw [← sub_add_sub (u n) (t n) (s n)]
    exact add_le_add _ _ _ _ a1 b1
  · rw [← sub_add_sub (s n) (t n) (u n)]
    exact add_le_add _ _ _ _ b2 a2

Conclusion "
`Close` is an equivalence relation: reflexive, symmetric, transitive.
So we can glue close Cauchy sequences together. The glued objects are the **real numbers**.
"

TheoremTab "ℚ"

end MyRat
