import MathlibNt.SieveTheory.LiLiuGoldbachG11PaidRosser
import MathlibNt.SieveTheory.LiLiuGoldbachWeightG11GoodConsumed

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

/-- Explicit proved Rosser envelope; its common mass is still unnormalized. -/
def goldbachG11PaidRosserEnvelope (N : ℕ) (hEven : Even N) (ε Z s A C ρ : ℝ) : ℝ :=
  let X := goldbachG11PrimeWindowMainMass N ε
  let S := goldbachG11LinkedBoundingSieve N hEven ε Z X
  400*X*(jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
    400*C*N/Real.log (N : ℝ)^A + 8000*(Nat.ceil Z : ℝ)

/-- Only the still-unevaluated G11 good count is removed from the previous base. -/
def goldbachWeightG11PaidBase (N : ℕ) (ε : ℝ) : ℤ :=
  goldbachWeightG11GoodRemainder N ε +
    goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))

theorem goldbachWeightG11_le_paidRosser (A ρ δ : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (hEven : Even N) (ε : ℝ), 0 ≤ ε → ∀ Z Δ s : ℝ,
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ → s = Real.log Δ/Real.log Z →
      3/2 ≤ s → s ≤ 4 → Δ ≤ Real.sqrt N/Real.log (N : ℝ)^B →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      goldbachG11PaidRosserEnvelope N hEven ε Z s A C ρ +
        δ*(SingularSeries.liuSingularSeries N * (N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨B,C,z₀,hB,hC,K,hK,hpaid⟩ := goldbachG11GoodTotal_le_paidRosser A ρ hA hρ
  obtain ⟨L,_,hgood⟩ := goldbachWeightG11_le_goodSwitched_normalized δ hδ
  refine ⟨B,C,z₀,hB,hC,max K L,hK.trans (le_max_left _ _), ?_⟩
  intro N hN hEven ε hε Z Δ s hz hZ hΔ hs hslo hshi hlevel
  have hp : (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤ goldbachG11PaidRosserEnvelope N hEven ε Z s A C ρ :=
    hpaid N ((le_max_left _ _).trans hN) hEven ε Z Δ s hz hZ hΔ hs hslo hshi hlevel
  exact (hgood N ((le_max_right _ _).trans hN) ε hε).trans (add_le_add hp le_rfl)

/-- Actual D19 lower bound with the good G11 count replaced by its paid Rosser
expression. The remaining signed base, low term and common-mass normalization
remain explicit; no final positivity is asserted. -/
theorem goldbachWeight_g11PaidRosser_consumed (A ρ δ : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < (2 : ℝ)/15 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ hEven : Even N,
      ∀ Zlow : ℝ, 1 ≤ Zlow → Zlow ≤ Real.sqrt (N : ℝ) →
      ∀ Z Δ s : ℝ, z₀ ≤ Z → 2 ≤ Z → 0 < Δ → s = Real.log Δ/Real.log Z →
      3/2 ≤ s → s ≤ 4 → Δ ≤ Real.sqrt N/Real.log (N : ℝ)^B →
      (goldbachWeightG11PaidBase N ε : ℝ) - (goldbachB9LowPositivePrefixSiftedCount N ε Zlow : ℝ) +
        (goldbachWeightHighFirstCoefficient ε - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) -
        goldbachG11PaidRosserEnvelope N hEven ε Z s A C ρ ≤ 4*(D19 N : ℝ) := by
  obtain ⟨B,C,z₀,hB,hC,K,hK,hpaid⟩ := goldbachG11GoodTotal_le_paidRosser A ρ hA hρ
  refine ⟨B,C,z₀,hB,hC,?_⟩
  intro ε hε hεu
  obtain ⟨L,_,hbase⟩ := goldbachWeight_g11GoodSwitched_consumed_eventually δ ε hδ hε hεu
  refine ⟨max K L,hK.trans (le_max_left _ _),?_⟩
  intro N hN hEven Zlow hZlow hZlowu Z Δ s hz hZ hΔ hs hslo hshi hlevel
  have hp : (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤ goldbachG11PaidRosserEnvelope N hEven ε Z s A C ρ :=
    hpaid N ((le_max_left _ _).trans hN) hEven ε Z Δ s hz hZ hΔ hs hslo hshi hlevel
  have hb := hbase N ((le_max_right _ _).trans hN) hEven Zlow hZlow hZlowu
  unfold goldbachWeightG11PaidBase
  push_cast
  linarith only [hb, hp]

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig