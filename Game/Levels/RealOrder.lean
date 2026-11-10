import Game.Levels.RealOrder.L01_NegEpsLe
import Game.Levels.RealOrder.L02_LeRefl
import Game.Levels.RealOrder.L03_NonnegAdd
import Game.Levels.RealOrder.L04_LeTrans
import Game.Levels.RealOrder.L05_AddLeAddRight
import Game.Levels.RealOrder.L06_LeAntisymm
import Game.Levels.RealOrder.L07_NotExists
import Game.Levels.RealOrder.L08_NotForall
import Game.Levels.RealOrder.L09_NotImp
import Game.Levels.RealOrder.L10_NatLeTotal
import Game.Levels.RealOrder.L11_IntNonnegOr
import Game.Levels.RealOrder.L12_RatNonnegOr
import Game.Levels.RealOrder.L13_RatLeTotal
import Game.Levels.RealOrder.L14_RealNonnegOr
import Game.Levels.RealOrder.L15_RealLeTotal
import Game.Levels.RealOrder.L16_RatAbsNonneg
import Game.Levels.RealOrder.L17_RatAbsBounds
import Game.Levels.RealOrder.L18_RatAbsLe
import Game.Levels.RealOrder.L19_RatAbsAdd
import Game.Levels.RealOrder.L20_NonnegOfEventually
import Game.Levels.RealOrder.L21_LeOfEventually
import Game.Levels.RealOrder.L22_AbsOfNonneg
import Game.Levels.RealOrder.L23_NonnegMul
import Game.Levels.RealOrder.L24_AbsAdd

World "RealOrder"
Title "Order in ℝ"

Introduction "
Now `ℝ` gets `≤`. As for `ℚ`, `x ≤ y` means `nonneg (y - x)`.

You will prove that `≤` is a total order that fits with `+` and `*`,
build the absolute value, and prove the triangle inequality.
"

Conclusion "
`ℝ` is an ordered commutative ring: a total order that fits with `+` and `*`. Next: inequalities.
"
