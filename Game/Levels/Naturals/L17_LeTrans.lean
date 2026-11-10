import Game.Levels.Naturals.L16_LeRefl

World "Naturals"
Level 17
Title "Chains of ≤"

namespace MyNat

Introduction "
Boss level of this world.

You can unfold `≤` in several places at once:
`rw [le_iff_exists_add] at h₁ h₂ ⊢`. The `⊢` means the goal. Type it as `\\|-`.
"

/-- If $a \le b$ and $b \le c$, then $a \le c$. -/
Statement le_trans (a b c : ℕ) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab
  intro hbc
  Hint "Unfold `≤` everywhere: `rw [le_iff_exists_add] at {hab} {hbc} ⊢`."
  rw [le_iff_exists_add] at hab hbc ⊢
  Hint "Take the hypotheses apart with `obtain`."
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hbc
  Hint "`c = b + {e}` and `b = a + {d}`. So which number do you `use`?"
  use d + e
  Hint "Rewrite `c` with `{he}`, then `b` with `{hd}`, then fix the brackets."
  rw [he, hd, add_assoc]

Conclusion "
You built the natural numbers: addition, multiplication and order, all proved by you.
Next: the integers.
"

TheoremTab "≤"

end MyNat
