import Game.Levels.RealArith.L05_CloseOfEq

World "RealArith"
Level 6
Title "Sums of reals are associative"

namespace MyReal

Introduction "
The recipe for a law of `ℝ`:

1. Write each real as a sequence: `obtain ⟨s, hs, rfl⟩ := exists_ofSeq x`.
2. Compute with `ofSeq_add` (and later `ofSeq_neg`, `ofSeq_mul`).
3. `rw [ofSeq_eq]`, then `apply MyRat.close_of_eq` and `intro n`.
4. Compute the terms (`MyRat.addSeq_apply`) and use the law of `ℚ`.
"

/-- $(x + y) + z = x + (y + z)$ for reals. -/
Statement add_assoc (x y z : ℝ) : x + y + z = x + (y + z) := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  obtain ⟨u, hu, rfl⟩ := exists_ofSeq z
  Hint "There are four sums of reals. `rw [ofSeq_add]` four times, then `ofSeq_eq`."
  rw [ofSeq_add, ofSeq_add, ofSeq_add, ofSeq_add, ofSeq_eq]
  Hint "Now `apply MyRat.close_of_eq` and `intro n`."
  Branch
    intro k
    Hint "That works, but it is the long way. `apply MyRat.close_of_eq` does the `ε` part for you."
  apply MyRat.close_of_eq
  intro n
  Hint "Compute the terms with `MyRat.addSeq_apply` (four times)."
  rw [MyRat.addSeq_apply, MyRat.addSeq_apply, MyRat.addSeq_apply, MyRat.addSeq_apply]
  Hint "This is `MyRat.add_assoc`."
  exact MyRat.add_assoc (s n) (t n) (u n)

Conclusion "
From now on `ac_rfl` also works for `+` on `ℝ`.
"

TheoremTab "ℝ"

-- `ac_rfl` may now use the laws the player proved for `+` on `ℝ`.
instance : Std.Associative (α := MyReal) (· + ·) := ⟨MyReal.add_assoc⟩
instance : Std.Commutative (α := MyReal) (· + ·) := ⟨MyReal.add_comm⟩

end MyReal
