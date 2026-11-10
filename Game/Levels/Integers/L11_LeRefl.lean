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
  Branch
    use 1
    Hint "`mk 1 0` is `1`, and `x ≠ x + 1`. Which `c` makes `x + mk c 0 = x`?"
  use 0
  Hint "`mk 0 0` is `0`: `rw [← zero_def]`. Then `add_zero`."
  rw [← zero_def, add_zero]

Conclusion "
`le_refl` for `ℤ` is yours. A few more rules, and `ℤ` is ready for fractions.
"

NewTheorem MyInt.le_iff
NewDefinition MyInt.le
TheoremTab "ℤ"

end MyInt
