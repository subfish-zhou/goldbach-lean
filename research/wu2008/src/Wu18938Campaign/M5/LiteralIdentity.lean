import Wu18938Campaign.M5.LiteralCount
import WR2SixthCountCarriers

noncomputable section

namespace Wu18938Campaign.M5.LiteralIdentity

theorem window_eq (N : ℕ) (l u : ℝ) :
    LiteralCount.window N l u = WuPaper.R2SixthCount.window N l u := rfl

theorem atom_eq (N d : ℕ) :
    LiteralCount.atom N d =
      Wu2008DoubleSieve.sourceSieveCountLE N d N
        ((N : ℝ) ^ WuPaper.R2SixthCount.alpha) := rfl

theorem pairCount_eq (N : ℕ) (l u v w : ℝ) :
    LiteralCount.pairCount N l u v w =
      WuPaper.R2SixthCount.rectangleCount N l u v w := rfl

theorem upsilon6_eq (N : ℕ) :
    LiteralCount.upsilon6 N = WuPaper.R2SixthCount.upsilon6 N := rfl

theorem countA_eq (N : ℕ) :
    LiteralCount.countA N 0 = WuPaper.R2SixthCount.countA N := by
  simp only [LiteralCount.countA, sub_zero]
  rfl

theorem countB_eq (N : ℕ) :
    LiteralCount.countB N 0 = WuPaper.R2SixthCount.countB N := by
  simp only [LiteralCount.countB, sub_zero]
  rfl

end Wu18938Campaign.M5.LiteralIdentity
