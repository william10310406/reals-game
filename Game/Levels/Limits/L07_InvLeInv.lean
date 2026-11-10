import Game.Levels.Limits.L06_OfSeqEq

World "Limits"
Level 7
Title "Smaller fractions"

namespace MyRat

open MyNat (succ)

open MyInt (mk)

Introduction "
A bigger denominator gives a smaller fraction: if `k ≤ n`, then `1/(n+1) ≤ 1/(k+1)`.
A long computation, step by step.
"

/-- If $k \le n$, then $\frac{1}{n+1} \le \frac{1}{k+1}$. -/
Statement inv_le_inv (k n : ℕ) : k ≤ n → frac 1 (succ n) ≤ frac 1 (succ k) := by
  intro h
  Hint "Write `n = k + c`: `rw [MyNat.le_iff_exists_add] at {h}`, then `obtain ⟨c, rfl⟩ := {h}`."
  Branch
    rw [le_iff_nonneg]
    Hint "First write `n = k + c`: `rw [MyNat.le_iff_exists_add] at {h}` and `obtain ⟨c, rfl⟩ := {h}`."
  rw [MyNat.le_iff_exists_add] at h
  obtain ⟨c, rfl⟩ := h
  Hint "Unfold `≤` and add the fractions."
  rw [le_iff_nonneg, sub_eq_add_neg, neg_frac,
    frac_add_frac (MyNat.succ_ne_zero k) (MyNat.succ_ne_zero (k + c))]
  rw [nonneg_frac (MyNat.mul_ne_zero (succ k) (succ (k + c)) (MyNat.succ_ne_zero k)
    (MyNat.succ_ne_zero (k + c)))]
  Hint "Remove the `1 *` and `-1 *`: `MyInt.neg_mul`, then `MyInt.mul_comm 1` and `MyInt.mul_one`, twice."
  rw [MyInt.neg_mul, MyInt.mul_comm 1, MyInt.mul_one, MyInt.mul_comm 1, MyInt.mul_one]
  Hint "Compute with `MyInt.neg_mk`, `MyInt.mk_add_mk`, then `MyInt.nonneg_iff`."
  rw [MyInt.neg_mk, MyInt.mk_add_mk, MyInt.nonneg_iff]
  Hint "Which natural number is the difference?"
  use c
  Hint "Now `MyInt.mk_eq`, then clean up in `ℕ`:
  `MyNat.add_zero` twice, `MyNat.zero_add`, `MyNat.add_succ`, `MyNat.add_comm k c`."
  rw [MyInt.mk_eq, MyNat.add_zero, MyNat.add_zero, MyNat.zero_add, MyNat.add_succ, MyNat.add_comm k c]

Conclusion "
`inv_le_inv` is in your inventory.
"

TheoremTab "lim"

end MyRat
