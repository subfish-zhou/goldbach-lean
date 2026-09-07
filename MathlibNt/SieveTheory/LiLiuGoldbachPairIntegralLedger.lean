import MathlibNt.SieveTheory.LiLiuGoldbachG67ActualIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachActiveCrossLedger

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Choose the density tolerance before epsilon and N, paying all truncation losses. -/
theorem exists_goldbachG67_integral_tolerance (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 53/(2*Real.exp Real.eulerMascheroniConstant) ∧
      goldbachG67IntegralConstant - δ ≤
        (53/(2*Real.exp Real.eulerMascheroniConstant)-ρ)*
          (goldbachG67JRIntegral 0 - (2*ρ)*goldbachG67LogRectangleMass - ρ) := by
  let k : ℝ := 53/(2*Real.exp Real.eulerMascheroniConstant)
  let f : ℝ → ℝ := fun ρ => (k-ρ)*(goldbachG67JRIntegral 0 - (2*ρ)*goldbachG67LogRectangleMass - ρ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hcont : ContinuousAt f 0 := by dsimp [f]; fun_prop
  obtain ⟨r,hr,hf⟩ := Metric.continuousAt_iff.mp hcont δ hδ
  let ρ := min (r/2) (k/2)
  have hρ : 0 < ρ := lt_min (half_pos hr) (half_pos hk)
  have hρr : ρ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hρk : ρ < k := (min_le_right _ _).trans_lt (half_lt_self hk)
  have hdist : dist ρ 0 < r := by simpa only [Real.dist_eq,sub_zero,abs_of_pos hρ] using hρr
  have hh := hf hdist
  rw [Real.dist_eq] at hh
  have hleft := (abs_lt.mp hh).1
  refine ⟨ρ,hρ,hρk,?_⟩
  change k*goldbachG67JRIntegral 0 - δ ≤ f ρ
  have hzero : f 0 = k*goldbachG67JRIntegral 0 := by dsimp [f]; ring
  rw [hzero] at hleft
  linarith

/-- The actual G6/G7 pair sums are replaced by their fixed JR integrals.
The original G12 output-prime fibres remain explicit: no output upper sieve is assumed. -/
theorem goldbachWeight_pairIntegralLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachG67IntegralConstant + (124341093/200000000 : ℝ) -
          goldbachB9PaperSplitIntegral - 10385101/100000000 - δ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) -
          (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
            goldbachG12NormalizedCoefficient N m *
              ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤
          4*(D19 N : ℝ) := by
  obtain ⟨ρ,hρ,hρk,hpay⟩ := exists_goldbachG67_integral_tolerance (δ/2) (half_pos hδ)
  obtain ⟨ε₀,hε₀,hε₀u,hledger⟩ := goldbachWeight_activeCrossLedger ρ (δ/2) hρ hρk (half_pos hδ)
  obtain ⟨M,_,hpair⟩ := goldbachG67IdealSum_integral_lower (2*ρ) ρ (by positivity) hρ
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨L,hL4,hl⟩ := hledger ε hε hεlt
  refine ⟨max L M,by omega,?_⟩
  intro N hN hEven
  have h := hl N (by omega) hEven
  have hp := hpair N (by omega)
  have hs := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hρk.le)
  have hm : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hc : goldbachG67IntegralConstant + (124341093/200000000 : ℝ) -
      goldbachB9PaperSplitIntegral - 10385101/100000000 - δ ≤
      (53/(2*Real.exp Real.eulerMascheroniConstant)-ρ)*
        (goldbachPairIdealSum N (2*ρ)
          (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) +
        goldbachPairIdealSum N (2*ρ)
          (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)))) +
        (124341093/200000000 : ℝ) - goldbachB9PaperSplitIntegral - 10385101/100000000 - δ/2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hc hm
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
