import MathlibNt.SieveTheory.LiLiuGoldbachG11MainMassBuchstab
import MathlibNt.SieveTheory.LiLiuGoldbachG11EulerProduct
import MathlibNt.SieveTheory.LiLiuGoldbachWeightG11PaidConsumed

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

theorem goldbachG11PrimeProduct_nonneg (N : ℕ) (hEven : Even N) (Z : ℝ) :
    0 ≤ goldbachB10PrimeProduct N Z := by
  rw [← goldbachG11Linked_sieveProduct_eq N hEven 0 Z 0]
  let S := goldbachG11LinkedBoundingSieve N hEven 0 Z 0
  change 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S
  unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpDvd := (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_squarefree.ne_zero).mp hp |>.2
  exact (sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd)).le

/-- Fixed ratio s=2, with the actual-label Buchstab sum in place of prime-window mass. -/
def goldbachG11BuchstabSieveEnvelope (N : ℕ) (Z A C ρ η : ℝ) : ℝ :=
  (goldbachG11BuchstabUpperMass N η + 8400*N/(N : ℝ)^(4/53 : ℝ))*
    (Real.exp Real.eulerMascheroniConstant+ρ)*goldbachB10PrimeProduct N Z +
    400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ)

theorem goldbachG11PaidEnvelope_le_buchstab (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (hEven : Even N) (ε Z A C ρ : ℝ), 0 ≤ ρ →
      goldbachG11PaidRosserEnvelope N hEven ε Z 2 A C ρ ≤
        goldbachG11BuchstabSieveEnvelope N Z A C ρ η := by
  obtain ⟨N₀,hN₀,hmass⟩ := goldbachG11PrimeWindowMainMass_le_buchstabUpper η hη
  refine ⟨N₀,hN₀,?_⟩
  intro N hN hEven ε Z A C ρ hρ
  have hF : jurkatRichertUpperLinearSieveFactor (2 : ℝ) = Real.exp Real.eulerMascheroniConstant := by
    norm_num [jurkatRichertUpperLinearSieveFactor]
  have hf : 0 ≤ Real.exp Real.eulerMascheroniConstant+ρ := add_nonneg (Real.exp_pos _).le hρ
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hmass N hN ε) hf) (goldbachG11PrimeProduct_nonneg N hEven Z)
  unfold goldbachG11PaidRosserEnvelope
  dsimp only
  rw [goldbachG11Linked_sieveProduct_eq, hF]
  unfold goldbachG11BuchstabSieveEnvelope
  exact add_le_add (add_le_add hh le_rfl) le_rfl

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig