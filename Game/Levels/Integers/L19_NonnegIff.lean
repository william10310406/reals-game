import Game.Levels.Integers.L18_MkMul

World "Integers"
Level 19
Title "Nonnegative integers"

namespace MyInt

Introduction "
Which integers are `≥ 0`? Exactly the naturals `mk c 0`.

An `↔` needs `constructor`, then one proof per direction.
"

/-- $0 \le x$ if and only if $x = c - 0$ for a natural $c$. -/
Statement nonneg_iff (x : ℤ) : 0 ≤ x ↔ ∃ c : ℕ, x = mk c 0 := by
  rw [le_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    Hint "Use the same `{c}`."
    Branch
      use 0
      Hint "Not `0`: `{hc}` already tells you what `x` is. Use `{c}`."
    use c
    Hint "Rewrite with `{hc}`, then `zero_add`."
    rw [hc, zero_add]
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    rw [hc, zero_add]

Conclusion "
From now on, `0 ≤ x` can be read as: `x` is a natural number.
"

TheoremTab "ℤ"

end MyInt
