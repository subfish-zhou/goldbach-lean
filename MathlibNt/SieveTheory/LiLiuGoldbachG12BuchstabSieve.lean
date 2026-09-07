import MathlibNt.SieveTheory.LiLiuGoldbachG12OutputEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG11BuchstabSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG11SieveParameters

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

/-- Original cross mother with the actual output sieve providing the second logarithm. -/
def goldbachG12BuchstabSieveEnvelope (N : ℕ) (Z A C ρ η : ℝ) : ℝ :=
  (goldbachG12BuchstabUpperMass N η + 8400*N/(N : ℝ)^(4/53 : ℝ))*
    (Real.exp Real.eulerMascheroniConstant+ρ)*goldbachB10PrimeProduct N Z +
    400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ)

/-- All cutoff choices are discharged using the square-root-level parameter theorem.
No assertion of the author's stronger low-band coefficient is made. -/
theorem goldbachG12OutputTotal_le_concreteBuchstabSieve (A ρ η : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ),
        (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
          goldbachG12NormalizedCoefficient N m *
            ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
          goldbachG12BuchstabSieveEnvelope N (goldbachG11SieveCutoff B N) A C ρ η := by
  obtain ⟨B,C,z₀,hB,hC,K,hK,hpaid⟩ :=
    goldbachG12OutputTotal_le_paidRosser_actualEuler A ρ hA hρ
  obtain ⟨L,_,hgeom⟩ := goldbachG11SieveParameters_eventually B z₀ 1 hB.le (by norm_num) le_rfl
  obtain ⟨M,_,hmass⟩ := goldbachG12WindowWeightSum_le_buchstab η hη
  refine ⟨B,C,hB,hC,max K (max L M),by omega,?_⟩
  intro N hN hEven ε
  have hg := hgeom N (by omega)
  have hp := hpaid N (by omega) hEven ε (goldbachG11SieveCutoff B N)
    (goldbachG11SieveLevel B N) 2 ((le_max_right _ _).trans hg.1)
    ((le_max_left _ _).trans hg.1) hg.2.2.1 hg.2.2.2.1
    (by norm_num) (by norm_num) hg.2.2.2.2.1
  have hF : jurkatRichertUpperLinearSieveFactor (2 : ℝ) = Real.exp Real.eulerMascheroniConstant := by
    norm_num [jurkatRichertUpperLinearSieveFactor]
  rw [hF] at hp
  have hm := hmass N (by omega) ε
  change 400*goldbachG12PrimeWindowMainMass N ε ≤ _ at hm
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hm (add_nonneg (Real.exp_pos Real.eulerMascheroniConstant).le hρ.le))
    (goldbachG11PrimeProduct_nonneg N hEven (goldbachG11SieveCutoff B N))
  exact hp.trans (add_le_add (add_le_add hh le_rfl) le_rfl)

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
