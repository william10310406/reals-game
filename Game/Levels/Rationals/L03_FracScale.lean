import Game.Levels.Rationals.L02_MulNeZero

World "Rationals"
Level 3
Title "Fractions"

namespace MyRat

open MyInt (mk)

Introduction "
A rational number is `frac a b`, read as `a / b`. Here `a : ℤ` and `b : ℕ` with `b ≠ 0`.

Two fractions are equal when you can cross-multiply:

`frac_eq hb hd : frac a b = frac c d ↔ a * mk d 0 = c * mk b 0`.

You must give the proofs `hb : b ≠ 0` and `hd : d ≠ 0`.
"

/-- $\frac{a}{b} = \frac{ac}{bc}$. -/
Statement frac_scale (a : ℤ) (b c : ℕ) (hb : b ≠ 0) (hc : c ≠ 0) :
    frac a b = frac (a * mk c 0) (b * c) := by
  Hint "Cross-multiply with `frac_eq`. The second denominator is `b * c`; its proof is
  `MyNat.mul_ne_zero b c {hb} {hc}`."
  Branch
    rw [MyInt.mul_comm]
    Hint "Rearranging inside is fine, but first compare the two fractions with `frac_eq`."
  rw [frac_eq hb (MyNat.mul_ne_zero b c hb hc)]
  Hint "Split `mk (b * c) 0` with `MyInt.mk_mul_mk_zero`, then use `ac_rfl`."
  rw [MyInt.mk_mul_mk_zero]
  ac_rfl

Conclusion "
Multiplying top and bottom by the same number does not change a fraction.
"

NewTheorem MyRat.frac_eq
NewDefinition MyRat MyRat.frac
TheoremTab "ℚ"

end MyRat
