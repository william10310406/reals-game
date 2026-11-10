import Game.Levels.Inequalities.L09_LeAntisymm

World "Inequalities"
Level 10
Title "Products in ℤ"

namespace MyInt

Introduction "
The product of two nonnegative integers is nonnegative.
"

/-- If $0 \le x$ and $0 \le y$, then $0 \le xy$. -/
Statement nonneg_mul (x y : ℤ) : 0 ≤ x → 0 ≤ y → 0 ≤ x * y := by
  intro hx hy
  rw [nonneg_iff] at hx hy ⊢
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨e, rfl⟩ := hy
  Branch
    use c + e
    Hint "Not the sum: `mk c 0 * mk e 0` is `mk (c * e) 0`."
  use c * e
  Hint "`mk_mul_mk_zero` says exactly this."
  rw [mk_mul_mk_zero]

Conclusion "
Naturals times naturals are naturals.
"

TheoremTab "ℤ"

end MyInt
