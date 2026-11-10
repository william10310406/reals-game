import Game.Levels.Integers.L17_NegMul

World "Integers"
Level 18
Title "Naturals inside ℤ"

namespace MyInt

Introduction "
A natural number `n` sits inside `ℤ` as `mk n 0`.
Products of naturals stay products.
"

/-- $(bd) - 0 = (b - 0)(d - 0)$. -/
Statement mk_mul_mk_zero (b d : ℕ) : mk (b * d) 0 = mk b 0 * mk d 0 := by
  Branch
    rw [MyNat.mul_comm]
    Hint "Swapping does not help. Multiply the right side out with `mk_mul_mk`."
  rw [mk_mul_mk]
  Hint "Remove the products with a `0`: `MyNat.mul_zero`, `MyNat.zero_mul`, `MyNat.mul_zero`."
  rw [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_zero]
  Hint "And the sums with a `0`: `MyNat.add_zero` twice."
  rw [MyNat.add_zero, MyNat.add_zero]

Conclusion "
So `ℕ` lives inside `ℤ`, with the same multiplication.
"

TheoremTab "ℤ"

end MyInt
