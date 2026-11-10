import Game.Levels.RealOrder.L03_NonnegAdd

World "RealOrder"
Level 4
Title "Chains of ≤"

namespace MyReal

Introduction "
If `x ≤ y` and `y ≤ z`, then `x ≤ z`. No sequences needed: split `z - x` at `y`.
"

/-- If $x \le y$ and $y \le z$, then $x \le z$. -/
Statement le_trans (x y z : ℝ) : x ≤ y → y ≤ z → x ≤ z := by
  intro hxy hyz
  rw [le_iff_nonneg] at hxy hyz ⊢
  Hint "Split `z - x` at `y`: `rw [← sub_add_sub x y z]`."
  Branch
    obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
    Hint "No sequences needed. Split `z - x` at `y` with `rw [← sub_add_sub x y z]`."
  rw [← sub_add_sub x y z]
  Hint "Now this is `nonneg_add`."
  exact nonneg_add (z - y) (y - x) hyz hxy

Conclusion "
`≤` on `ℝ` is transitive.
"

TheoremTab "≤ℝ"

end MyReal
