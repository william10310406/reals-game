import Game.Levels.Limits.L07_InvLeInv

World "Limits"
Level 8
Title "One over n"

namespace MyRat

open MyNat (succ)

Introduction "
Final boss. The sequence `invSucc`: `1/1, 1/2, 1/3, ...` tends to `0`.
(`invSucc_apply : invSucc n = frac 1 (succ n)`.)

Which `N` works for `1/(k+1)`? Take `N = k`.
"

/-- $\frac{1}{n+1} \to 0$. -/
Statement tendsto_invSucc : Tendsto invSucc 0 := by
  intro k
  Hint "Use `use k`."
  use k
  intro n hn
  Hint "Clean up: `invSucc_apply`, then `sub_eq_add_neg`, `neg_zero`, `add_zero` for `x - 0`,
  then `sub_eq_add_neg`, `add_comm`, `add_zero` for `0 - x`."
  rw [invSucc_apply, sub_eq_add_neg, neg_zero, add_zero, sub_eq_add_neg, add_comm, add_zero]
  constructor
  · Hint "That is `inv_le_inv`."
    exact inv_le_inv k n hn
  · Hint "First show `-frac 1 (succ n) ≤ 0` with `have`:
    `rw [← neg_zero]`, then `neg_le_neg` and `eps_nonneg n`."
    have h0 : -frac 1 (succ n) ≤ 0 := by
      rw [← neg_zero]
      exact neg_le_neg 0 (frac 1 (succ n)) (eps_nonneg n)
    Hint "Chain: `le_trans _ 0 _ {h0} (eps_nonneg k)`."
    exact le_trans _ 0 _ h0 (eps_nonneg k)

Conclusion "
A limit computed by hand: `1/(n+1) → 0`, using only theorems you proved yourself.
So far all of this happened in `ℚ`. Next you make `ℝ` a full number system.
"

NewTheorem MyRat.invSucc_apply
NewDefinition MyRat.invSucc
TheoremTab "lim"

end MyRat
