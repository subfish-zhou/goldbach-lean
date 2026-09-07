import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLocalGlobal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWeilBridge

/-!
# The Fouvry interval estimate from primitive prime powers

This is a conditional assembly theorem. It assumes only the local primitive
estimate, not any complete all-modulus or incomplete Kloosterman estimate.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem reciprocalInterval_fouvry_of_primitive_prime_power
    (hlocal : ∀ (p k : ℕ) (_ : Fact p.Prime) (a d : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (X Y : ℝ),
      X ≤ Y → Y - X ≤ q →
      ‖reciprocalInterval q d X Y‖ ≤
        C * Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  exact reciprocalInterval_weil_to_fouvry
    (fun q _ m d ↦ completeKloosterman_weil_zmod_of_primitive_prime_power hlocal q m d) hε

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
