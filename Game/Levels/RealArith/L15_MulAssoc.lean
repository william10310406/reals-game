import Game.Levels.RealArith.L14_MulComm

World "RealArith"
Level 15
Title "Products of reals are associative"

namespace MyReal

Introduction "
Like `add_assoc`, with `ofSeq_mul` and `MyRat.mul_assoc`.
"

/-- $(xy)z = x(yz)$ for reals. -/
Statement mul_assoc (x y z : ℝ) : x * y * z = x * (y * z) := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  obtain ⟨t, ht, rfl⟩ := exists_ofSeq y
  obtain ⟨u, hu, rfl⟩ := exists_ofSeq z
  Hint "`rw [ofSeq_mul]` four times, then `ofSeq_eq`."
  rw [ofSeq_mul, ofSeq_mul, ofSeq_mul, ofSeq_mul, ofSeq_eq]
  apply MyRat.close_of_eq
  intro n
  Hint "`MyRat.mulSeq_apply` four times, then `MyRat.mul_assoc`."
  rw [MyRat.mulSeq_apply, MyRat.mulSeq_apply, MyRat.mulSeq_apply, MyRat.mulSeq_apply]
  exact MyRat.mul_assoc (s n) (t n) (u n)

Conclusion "
From now on `ac_rfl` also works for `*` on `ℝ`.
"

TheoremTab "ℝ"

-- `ac_rfl` may now use the laws the player proved for `*` on `ℝ`.
instance : Std.Associative (α := MyReal) (· * ·) := ⟨MyReal.mul_assoc⟩
instance : Std.Commutative (α := MyReal) (· * ·) := ⟨MyReal.mul_comm⟩

end MyReal
