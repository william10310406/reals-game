import Game.Levels.RealOrder.L09_NotImp

World "RealOrder"
Level 10
Title "Comparing naturals"

namespace MyNat

Introduction "
Any two reals can be compared: `x ≤ y` or `y ≤ x`. To prove that, we first need it for
`ℕ`, then for `ℤ` and `ℚ`.

Two naturals can always be compared. Induction on `a`.
"

/-- For naturals, $a \le b$ or $b \le a$. -/
Statement le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := by
  Hint "`induction a with d hd`."
  Branch
    induction b with d hd
    Hint "Induction on `b` works too, but the hints follow induction on `a`."
  induction a with d hd
  · Hint "`0 ≤ b`: `left`, then `rw [le_iff_exists_add]` and `use b`."
    left
    rw [le_iff_exists_add]
    use b
    rw [zero_add]
  · Hint "Use the two cases of `{hd}`: `obtain h | h := {hd}`."
    obtain h | h := hd
    · Hint "`{h} : d ≤ b`. Write `b = d + c` and split `c` with `cases c with e`."
      rw [le_iff_exists_add] at h
      obtain ⟨c, hc⟩ := h
      cases c with e
      · Hint "`b = d + 0`, so `b ≤ succ d`."
        right
        rw [le_iff_exists_add]
        use 1
        rw [hc, add_zero, add_one_eq_succ]
      · Hint "`b = d + succ e = succ d + e`."
        left
        rw [le_iff_exists_add]
        use e
        rw [hc, add_succ, succ_add]
    · Hint "`{h} : b ≤ d`, so `b ≤ succ d`."
      right
      rw [le_iff_exists_add] at h ⊢
      obtain ⟨c, hc⟩ := h
      use succ c
      rw [add_succ, ← hc]

Conclusion "
`≤` on `ℕ` is a total order.
"

TheoremTab "≤"

end MyNat
