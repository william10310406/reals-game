import Game.Levels.Reals.L04_EpsNonneg

World "Reals"
Level 5
Title "Two halves"

namespace MyRat

open MyInt (mk)

Introduction "
The key trick of analysis: to make a sum small, make each half small.

Show `1/(2m) + 1/(2m) = 1/m`. A long computation; follow the hints.
"

/-- $\frac{1}{m+m} + \frac{1}{m+m} = \frac{1}{m}$. -/
Statement half (m : ℕ) (hm : m ≠ 0) : frac 1 (m + m) + frac 1 (m + m) = frac 1 m := by
  Hint "First get `m + m ≠ 0`:
  `have h2 : m + m ≠ 0 := by` and then, on new lines, `intro h`, `apply {hm}`,
  `exact MyNat.eq_zero_of_add_eq_zero m m h`."
  Branch
    rw [frac_add_frac]
    Hint "Without a proof of `m + m ≠ 0`, `frac_add_frac` leaves you side goals. Prove `have h2 : m + m ≠ 0` first."
  have h2 : m + m ≠ 0 := by
    intro h
    apply hm
    exact MyNat.eq_zero_of_add_eq_zero m m h
  Hint "Add, then cross-multiply:
  `rw [frac_add_frac {h2} {h2}, frac_eq (MyNat.mul_ne_zero (m + m) (m + m) {h2} {h2}) {hm}]`."
  rw [frac_add_frac h2 h2, frac_eq (MyNat.mul_ne_zero (m + m) (m + m) h2 h2) hm]
  Hint "Remove the `1 *`: `MyInt.mul_comm 1` turns `1 * x` into `x * 1`, then `MyInt.mul_one`. Twice."
  rw [MyInt.mul_comm 1, MyInt.mul_one, MyInt.mul_comm 1, MyInt.mul_one]
  Hint "Add the pairs, clean `0 + 0`, and join the product: `MyInt.mk_add_mk`, `MyNat.add_zero`,
  `← MyInt.mk_mul_mk_zero`."
  rw [MyInt.mk_add_mk, MyNat.add_zero, ← MyInt.mk_mul_mk_zero]
  Hint "Now it is about `ℕ`. Multiply out: `MyNat.add_mul` three times, then `MyNat.mul_add`."
  rw [MyNat.add_mul, MyNat.add_mul, MyNat.add_mul, MyNat.mul_add]

Conclusion "
This is the famous *ε/2* trick, in our language.
"

TheoremTab "ℚ"

end MyRat
