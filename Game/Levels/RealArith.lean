import Game.Levels.RealArith.L01_RatMulComm
import Game.Levels.RealArith.L02_RatMulAssoc
import Game.Levels.RealArith.L03_RatMulOne
import Game.Levels.RealArith.L04_RatMulAdd
import Game.Levels.RealArith.L05_CloseOfEq
import Game.Levels.RealArith.L06_AddAssoc
import Game.Levels.RealArith.L07_AddZero
import Game.Levels.RealArith.L08_ZeroAdd
import Game.Levels.RealArith.L09_AddNeg
import Game.Levels.RealArith.L10_NegAdd
import Game.Levels.RealArith.L11_NegNeg
import Game.Levels.RealArith.L12_SubAddSub
import Game.Levels.RealArith.L13_NegSub
import Game.Levels.RealArith.L14_MulComm
import Game.Levels.RealArith.L15_MulAssoc
import Game.Levels.RealArith.L16_MulOne
import Game.Levels.RealArith.L17_MulAdd
import Game.Levels.RealArith.L18_OfRatAdd
import Game.Levels.RealArith.L19_OfRatMul

World "RealArith"
Title "Arithmetic in ℝ"

Introduction "
So far `ℝ` only has addition. Now it gets everything else:
`0`, `1`, negatives, subtraction, multiplication, and `ℚ` inside `ℝ`.

Reals compute term by term. So each law of `ℝ` comes from the same law of `ℚ`,
applied to every term of the sequences.
"

Conclusion "
`ℝ` is a commutative ring that contains `ℚ`. Next: order.
"
