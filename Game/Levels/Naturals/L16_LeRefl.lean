import Game.Levels.Naturals.L15_MulAssoc

World "Naturals"
Level 16
Title "Less or equal"

namespace MyNat

Introduction "
`a ≤ b` means: there is a `c` with `b = a + c`.

The theorem `le_iff_exists_add` says exactly this.
Use `rw [le_iff_exists_add]` to unfold `≤`.
"

/-- $a \le a$. -/
Statement le_refl (a : ℕ) : a ≤ a := by
  Hint "Unfold `≤` with `rw [le_iff_exists_add]`."
  rw [le_iff_exists_add]
  Hint "Which `c` gives `a = a + c`? Use `use`."
  use 0
  rw [add_zero]

Conclusion "
Every number is less or equal to itself.
"

NewTheorem MyNat.le_iff_exists_add
NewDefinition MyNat.le
TheoremTab "≤"

end MyNat
