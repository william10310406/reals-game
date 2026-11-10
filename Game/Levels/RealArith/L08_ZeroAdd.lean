import Game.Levels.RealArith.L07_AddZero

World "RealArith"
Level 8
Title "Zero on the left"

namespace MyReal

Introduction "
Not every law needs sequences. Some follow from laws you already have.
"

/-- $0 + x = x$ for reals. -/
Statement zero_add (x : ℝ) : 0 + x = x := by
  Hint "Swap the sum with `add_comm`, then use `add_zero`."
  Branch
    obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
    Hint "That works, but there is a short way without sequences:
    `rw [add_comm, add_zero]`."
  rw [add_comm, add_zero]

Conclusion "
Two lines. Laws you proved are tools.
"

TheoremTab "ℝ"

end MyReal
