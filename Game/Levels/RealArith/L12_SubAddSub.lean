import Game.Levels.RealArith.L11_NegNeg

World "RealArith"
Level 12
Title "Subtraction"

namespace MyReal

Introduction "
Subtraction is adding the negative: `sub_eq_add_neg x y : x - y = x + -y`.

This level needs no sequences: use the laws of `ℝ` you proved, and `ac_rfl`.
"

/-- $(z - y) + (y - x) = z - x$ for reals. -/
Statement sub_add_sub (x y z : ℝ) : z - y + (y - x) = z - x := by
  Hint "Turn every `-` into `+ -` with `sub_eq_add_neg` (three times)."
  Branch
    obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
    Hint "No sequences needed here. Use `sub_eq_add_neg`, then `ac_rfl` and the laws of `ℝ`."
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
  Hint "Regroup: `have h : z + -y + (y + -x) = z + -x + (y + -y) := by ac_rfl`."
  have h : z + -y + (y + -x) = z + -x + (y + -y) := by ac_rfl
  Hint "Now `rw [{h}, add_neg, add_zero]`."
  rw [h, add_neg, add_zero]

Conclusion "
The same proof as for `ℚ`. Once the laws hold, the proofs carry over.
"

NewTheorem MyReal.sub_eq_add_neg
TheoremTab "ℝ"

end MyReal
