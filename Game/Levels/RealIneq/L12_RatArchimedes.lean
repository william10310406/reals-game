import Game.Levels.RealIneq.L11_AbsLe

World "RealIneq"
Level 12
Title "Archimedes in ℚ"

namespace MyRat

open MyNat (succ)
open MyInt (mk)

Introduction "
**Archimedean property**: no rational is bigger than all naturals.
For every `q` there is a natural `n` with `q ≤ n`. Here `n` as a rational is `frac (mk n 0) 1`.

For `q = frac (mk p r) b` (that is `(p - r) / b`), the natural `p` works.
A computation in `ℕ`.
"

/-- For every rational $q$ there is a natural $n$ with $q \le n$. -/
Statement archimedean (q : ℚ) : ∃ n : ℕ, q ≤ frac (mk n 0) 1 := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac q
  obtain ⟨p, r, rfl⟩ := MyInt.exists_mk a
  use p
  Hint "`b ≠ 0`, so `b = succ c`: `cases b with c`."
  cases b with c
  · exfalso
    apply hb
    rfl
  · Hint "Unfold `≤` and add the fractions:
    `rw [le_iff_nonneg, sub_eq_add_neg, neg_frac, frac_add_frac MyNat.one_ne_zero {hb}]`,
    then `nonneg_frac (MyNat.mul_ne_zero 1 (succ c) MyNat.one_ne_zero {hb})`."
    rw [le_iff_nonneg, sub_eq_add_neg, neg_frac, frac_add_frac MyNat.one_ne_zero hb,
      nonneg_frac (MyNat.mul_ne_zero 1 (succ c) MyNat.one_ne_zero hb)]
    Hint "Compute in `ℤ`: `rw [MyInt.neg_mk, MyInt.mk_mul_mk, MyInt.mk_mul_mk, MyInt.mk_add_mk,
    MyInt.nonneg_iff]`."
    rw [MyInt.neg_mk, MyInt.mk_mul_mk, MyInt.mk_mul_mk, MyInt.mk_add_mk, MyInt.nonneg_iff]
    Hint "The difference is `p * c + r`: `use p * c + r`, then `rw [MyInt.mk_eq]`."
    use p * c + r
    rw [MyInt.mk_eq]
    Hint "Clean up the products: `rw [MyNat.mul_zero, MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_zero,
    MyNat.mul_one, MyNat.mul_one, MyNat.mul_succ]`.
    Then the zeros: `MyNat.add_zero` three times and `MyNat.zero_add` three times. Finish with `ac_rfl`."
    rw [MyNat.mul_zero, MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_zero, MyNat.mul_one,
      MyNat.mul_one, MyNat.mul_succ]
    rw [MyNat.add_zero, MyNat.add_zero, MyNat.add_zero, MyNat.zero_add, MyNat.zero_add, MyNat.zero_add]
    ac_rfl

Conclusion "
Every rational is below some natural number.
"

TheoremTab "ℚ"

end MyRat
