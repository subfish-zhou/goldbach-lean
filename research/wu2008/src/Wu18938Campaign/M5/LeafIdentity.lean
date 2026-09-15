import Wu18938Campaign.M5.LiteralCount
import MathlibNt.Wu2008DoubleSieve.SourceCarriers

noncomputable section

namespace Wu18938Campaign.M5.LeafIdentity

open Wu2008DoubleSieve
open scoped Classical

theorem window_eq (N : ℕ) (l u : ℝ) :
    LiteralCount.window N l u = primeWindow N ((N : ℝ) ^ l) ((N : ℝ) ^ u) := rfl

theorem atom_eq (N d : ℕ) :
    LiteralCount.atom N d = sourceSieveCountLE N d N
      ((N : ℝ) ^ (100 / 1327 : ℝ)) := rfl

theorem pairCount_eq (N : ℕ) (l u v w : ℝ) :
    LiteralCount.pairCount N l u v w =
      ∑ q ∈ primeWindow N ((N : ℝ) ^ v) ((N : ℝ) ^ w),
        ∑ p ∈ primeWindow N ((N : ℝ) ^ l) ((N : ℝ) ^ u),
          sourceSieveCountLE N (p * q) N ((N : ℝ) ^ (100 / 1327 : ℝ)) := rfl

end Wu18938Campaign.M5.LeafIdentity
