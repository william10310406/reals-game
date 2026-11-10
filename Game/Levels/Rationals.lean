import Game.Levels.Rationals.L01_OneNeZero
import Game.Levels.Rationals.L02_MulNeZero
import Game.Levels.Rationals.L03_FracScale
import Game.Levels.Rationals.L04_AddComm
import Game.Levels.Rationals.L05_AddZero
import Game.Levels.Rationals.L06_AddNeg
import Game.Levels.Rationals.L07_NegAdd
import Game.Levels.Rationals.L08_AddAssoc
import Game.Levels.Rationals.L09_NonnegAdd
import Game.Levels.Rationals.L10_LeRefl
import Game.Levels.Rationals.L11_SubAddSub
import Game.Levels.Rationals.L12_LeTrans
import Game.Levels.Rationals.L13_AddLeAdd

World "Rationals"
Title "Rationals"

Introduction "
In `ℤ` you cannot solve `2 * x = 1`. We build fractions.

A rational is `frac a b`, read as `a / b`, with `a : ℤ` and `b : ℕ`, `b ≠ 0`.
Two fractions are equal when they cross-multiply to the same integer.

Every proof here has the same shape: write rationals as fractions, compute, reduce to `ℤ`.
Then we build the order `≤`.
"

Conclusion "
`ℚ` is built, with addition and order. These are the tools for Cauchy sequences.
"
