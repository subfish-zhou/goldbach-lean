import MathlibNt.SieveTheory.LiLiuGoldbachG11BuchstabSieve
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- The actual G11 count, with the finite Buchstab main sum and the exceptional
prime divisors of N retained explicitly. The sieve ratio is fixed at two. -/
theorem goldbachWeightG11_le_buchstabSieve (A ρ δ η : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ), 0 ≤ ε → ∀ Z Δ : ℝ,
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ → 2 = Real.log Δ/Real.log Z →
      Δ ≤ Real.sqrt N/Real.log (N : ℝ)^B →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      goldbachG11BuchstabSieveEnvelope N Z A C ρ η +
        δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨B,C,z₀,hB,hC,K,hK,hpaid⟩ := goldbachWeightG11_le_paidRosser A ρ δ hA hρ hδ
  obtain ⟨L,_,henv⟩ := goldbachG11PaidEnvelope_le_buchstab η hη
  refine ⟨B,C,z₀,hB,hC,max K L,hK.trans (le_max_left _ _),?_⟩
  intro N hN hEven ε hε Z Δ hz hZ hΔ hs hlevel
  have hp := hpaid N ((le_max_left _ _).trans hN) hEven ε hε Z Δ 2
    hz hZ hΔ hs (by norm_num) (by norm_num) hlevel
  exact hp.trans (add_le_add
    (henv N ((le_max_right _ _).trans hN) hEven ε Z A C ρ hρ.le) le_rfl)

/-- Actual D19 consumer: no prime-output count or unnormalized X remains in the
negative G11 envelope. The finite prime-label sum and other signed terms remain. -/
theorem goldbachWeight_g11BuchstabSieve_consumed (A ρ δ η : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B C z₀ : ℝ, 0 < B ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < (2 : ℝ)/15 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
      ∀ Zlow : ℝ, 1 ≤ Zlow → Zlow ≤ Real.sqrt (N : ℝ) →
      ∀ Z Δ : ℝ, z₀ ≤ Z → 2 ≤ Z → 0 < Δ → 2 = Real.log Δ/Real.log Z →
      Δ ≤ Real.sqrt N/Real.log (N : ℝ)^B →
      (goldbachWeightG11PaidBase N ε : ℝ) - (goldbachB9LowPositivePrefixSiftedCount N ε Zlow : ℝ) +
        (goldbachWeightHighFirstCoefficient ε - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) -
        goldbachG11BuchstabSieveEnvelope N Z A C ρ η ≤ 4*(D19 N : ℝ) := by
  obtain ⟨B,C,z₀,hB,hC,hpaid⟩ := goldbachWeight_g11PaidRosser_consumed A ρ δ hA hρ hδ
  obtain ⟨L,_,henv⟩ := goldbachG11PaidEnvelope_le_buchstab η hη
  refine ⟨B,C,z₀,hB,hC,?_⟩
  intro ε hε hεu
  obtain ⟨K,hK,hbase⟩ := hpaid ε hε hεu
  refine ⟨max K L,hK.trans (le_max_left _ _),?_⟩
  intro N hN hEven Zlow hZlow hZlowu Z Δ hz hZ hΔ hs hlevel
  have hb := hbase N ((le_max_left _ _).trans hN) hEven Zlow hZlow hZlowu Z Δ 2
    hz hZ hΔ hs (by norm_num) (by norm_num) hlevel
  exact (sub_le_sub_left
    (henv N ((le_max_right _ _).trans hN) hEven ε Z A C ρ hρ.le) _).trans hb

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig