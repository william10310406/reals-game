import Game.Levels.Integers.L10_MulAssoc

World "Integers"
Level 11
Title "Order on the integers"

namespace MyInt

Introduction "
For integers, `x ≤ y` means `y = x + mk c 0` for some natural `c`.
The theorem `le_iff` says this.

Use what you proved in this world.
"

/-- $x \le x$ for integers. -/
Statement le_refl (x : ℤ) : x ≤ x := by
  Hint "Unfold `≤` with `rw [le_iff]`."
  rw [le_iff]
  Hint "Which natural number `c` works?"
  use 0
  Hint "`mk 0 0` is `0`: `rw [← zero_def]`. Then `add_zero`."
  rw [← zero_def, add_zero]

Conclusion "
You built the integers. Next: fractions.
"

NewTheorem MyInt.le_iff
NewDefinition MyInt.le
TheoremTab "ℤ"

end MyInt
