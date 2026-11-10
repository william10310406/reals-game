import Game.Levels.Integers.L20_NonnegAdd

World "Integers"
Level 21
Title "Scaling a nonnegative"

namespace MyInt

Introduction "
Last level of this world. Multiply a nonnegative integer by a natural number.
"

/-- If $0 \le x$, then $0 \le x \cdot (n - 0)$. -/
Statement nonneg_mul_mk (x : ℤ) (n : ℕ) : 0 ≤ x → 0 ≤ x * mk n 0 := by
  intro hx
  rw [nonneg_iff] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  Hint "Which natural number is the product?"
  Branch
    use c
    Hint "Not `c`: you need the product `c * n`."
  use c * n
  rw [mk_mul_mk]
  Hint (hidden := true) "`MyNat.mul_zero`, `MyNat.zero_mul`, `MyNat.mul_zero`, `MyNat.add_zero`, `MyNat.add_zero`."
  rw [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_zero, MyNat.add_zero, MyNat.add_zero]

Conclusion "
You built the integers: ring rules and order. Next: fractions.
"

TheoremTab "ℤ"

end MyInt
