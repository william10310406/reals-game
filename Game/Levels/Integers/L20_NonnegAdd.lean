import Game.Levels.Integers.L19_NonnegIff

World "Integers"
Level 20
Title "Adding nonnegatives"

namespace MyInt

Introduction "
`rw [nonneg_iff] at hx hy ⊢` rewrites three places at once.
"

/-- If $0 \le x$ and $0 \le y$, then $0 \le x + y$. -/
Statement nonneg_add (x y : ℤ) : 0 ≤ x → 0 ≤ y → 0 ≤ x + y := by
  intro hx hy
  Hint "Use `nonneg_iff` everywhere: `rw [nonneg_iff] at {hx} {hy} ⊢`."
  rw [nonneg_iff] at hx hy ⊢
  Hint "`obtain ⟨c, rfl⟩ := {hx}` replaces `x` by `mk c 0`."
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨e, rfl⟩ := hy
  Hint "Which natural number is the sum?"
  use c + e
  rw [mk_add_mk, MyNat.add_zero]

Conclusion "
Sums of naturals are naturals.
"

TheoremTab "ℤ"

end MyInt
