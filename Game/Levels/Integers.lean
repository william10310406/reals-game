import Game.Levels.Integers.L01_Pairs
import Game.Levels.Integers.L02_AcRfl
import Game.Levels.Integers.L03_Zero
import Game.Levels.Integers.L04_AddComm
import Game.Levels.Integers.L05_AddAssoc
import Game.Levels.Integers.L06_AddZero
import Game.Levels.Integers.L07_AddNeg
import Game.Levels.Integers.L08_MulComm
import Game.Levels.Integers.L09_MulAdd
import Game.Levels.Integers.L10_MulAssoc
import Game.Levels.Integers.L11_LeRefl

World "Integers"
Title "Integers"

Introduction "
In `ℕ` you cannot solve `x + 3 = 1`. We fix this by building the integers `ℤ`.

An integer is a pair of naturals `mk a b`, read as `a - b`.
The pairs `mk 1 3` and `mk 0 2` are the same integer: `1 + 2 = 0 + 3`.

Every proof in this world has the same shape:
write integers as pairs, compute, and reduce to `ℕ`.
"

Conclusion "
`ℤ` is built, with addition, negatives, multiplication and order.
"
