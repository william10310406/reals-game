import Game.Levels.Reals.L01_LeAddRight
import Game.Levels.Reals.L02_SuccNeZero
import Game.Levels.Reals.L03_NegZero
import Game.Levels.Reals.L04_EpsNonneg
import Game.Levels.Reals.L05_Half
import Game.Levels.Reals.L06_ConstCauchy
import Game.Levels.Reals.L07_CloseRefl
import Game.Levels.Reals.L08_CloseSymm
import Game.Levels.Reals.L09_CloseTrans
import Game.Levels.Reals.L10_AddCauchy
import Game.Levels.Reals.L11_CloseAdd
import Game.Levels.Reals.L12_AddComm

World "Reals"
Title "Cauchy sequences and Reals"

Introduction "
`ℚ` has holes: no rational squares to `2`. We fill them with sequences.

A sequence `s 0, s 1, s 2, ...` of rationals is **Cauchy** when its terms get close together.
Two sequences are **close** when their terms get close to each other.
A **real number** is a Cauchy sequence, where close sequences count as the same.

*Small* always means: at most `1/(k+1)` for a `k` of your opponent's choice.
"

Conclusion "
`ℝ` is built, with addition. Next: inequalities.
"
