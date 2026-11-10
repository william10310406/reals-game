import Game.Levels.Rationals.L10_LeRefl

World "Rationals"
Level 11
Title "Telescoping"

namespace MyRat

Introduction "
`have h : A = B := by ac_rfl` proves a small fact and names it `h`.
"

/-- $(z - y) + (y - x) = z - x$. -/
Statement sub_add_sub (x y z : ℚ) : z - y + (y - x) = z - x := by
  Hint "Turn every `-` into `+ -` with `sub_eq_add_neg` (three times)."
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
  Hint "Regroup: `have h : z + -y + (y + -x) = z + -x + (y + -y) := by ac_rfl`."
  Branch
    rw [add_assoc]
    Hint "Regrouping by hand is long. Use `have h : … := by ac_rfl` to put `y` and `-y` together."
  have h : z + -y + (y + -x) = z + -x + (y + -y) := by ac_rfl
  Hint "Now `rw [{h}, add_neg, add_zero]`."
  rw [h, add_neg, add_zero]

Conclusion "
The `y` cancels. We use this for chains of `≤`.
"

TheoremTab "ℚ"

end MyRat
