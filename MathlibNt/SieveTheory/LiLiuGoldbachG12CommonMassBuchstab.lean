import MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The same modulus-independent mass controls the original cross mother and the actual divisor residual. -/
theorem goldbachG12CommonMass_buchstab_and_distribution (A η : ℝ)
    (hA : 0 < A) (hη : 0 < η) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (ε : ℝ) (Q : ℕ),
        (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ)^B →
        400*goldbachG12PrimeWindowMainMass N ε ≤
          goldbachG12BuchstabUpperMass N η + 8400*N/(N : ℝ)^(4/53 : ℝ) ∧
        (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG12CommonDivisorResidual N ε d|) ≤
          C*N/Real.log (N : ℝ)^A := by
  obtain ⟨B,C,hB,hC,L,hL,hd⟩ := goldbachG12CommonDivisorResidual_log_saving A hA
  obtain ⟨M,_,hm⟩ := goldbachG12WindowWeightSum_le_buchstab η hη
  refine ⟨B,C,hB,hC,max L M,by omega,?_⟩
  intro N hN ε Q hQ
  constructor
  · simpa only [goldbachG12PrimeWindowMainMass,goldbachG12PrimeWindowWeight] using hm N (by omega) ε
  · exact hd N (by omega) ε Q hQ

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
