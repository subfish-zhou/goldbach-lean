import MathlibNt.SieveTheory.LiLiuGoldbachG11NormalizedIntegralBound

open Set LiLiuPrereqBuchstab
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Real D19 consumer of the actual Buchstab-sieve predecessor. The old signed
base and low positive-prefix count are retained literally, without estimating
any other branch. Sieve constants and cutoffs have all been internalized. -/
theorem goldbachWeight_g11NormalizedIntegral_consumed
    (W δ ε : ℝ) (hW0 : 0 ≤ W) (hδ : 0 < δ)
    (hW : ∀ u ∈ Icc (17 / 4 : ℝ) (37 / 4), buchstab u ≤ W)
    (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
      ∀ Zlow : ℝ, 1 ≤ Zlow → Zlow ≤ Real.sqrt (N : ℝ) →
      (goldbachWeightG11PaidBase N ε : ℝ) -
        (goldbachB9LowPositivePrefixSiftedCount N ε Zlow : ℝ) +
        (goldbachWeightHighFirstCoefficient ε - 8*W*goldbachG11PrimeIntegral (fun _ => 1) - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        4*(D19 N : ℝ) := by
  obtain ⟨τ,hτ,_,henv⟩ := goldbachG11NormalizedIntegral_envelope W (δ/2) hW0 (by positivity) hW
  obtain ⟨B,C,z₀,hB,_,hconsumer⟩ := goldbachWeight_g11BuchstabSieve_consumed
    3 (τ*Real.exp Real.eulerMascheroniConstant) (δ/2) τ
    (by norm_num) (mul_pos hτ (Real.exp_pos _)) (by positivity) hτ
  obtain ⟨K,hK,hbase⟩ := hconsumer ε hε hεu
  obtain ⟨L,_,hbound⟩ := henv B C hB.le
  obtain ⟨G,_,hgeom⟩ := goldbachG11SieveParameters_eventually B z₀ 1 hB.le (by norm_num) le_rfl
  refine ⟨max K (max L G),by omega,?_⟩
  intro N hN hEven Zlow hZlow hZlowu
  obtain ⟨hZ,_,hΔ,hs,hlevel,_,_⟩ := hgeom N (by omega)
  have hb := hbase N (by omega) hEven Zlow hZlow hZlowu
    (goldbachG11SieveCutoff B N) (goldbachG11SieveLevel B N)
    ((le_max_right _ _).trans hZ) ((le_max_left _ _).trans hZ) hΔ hs hlevel
  have he := hbound N (by omega) hEven
  linarith only [hb,he]

/-- Unconditional integral D19 interface (W=1). It is a signed lower bound,
not a positivity theorem and not the sharper author-weight coefficient. -/
theorem goldbachWeight_g11NormalizedIntegral_one_consumed
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
      ∀ Zlow : ℝ, 1 ≤ Zlow → Zlow ≤ Real.sqrt (N : ℝ) →
      (goldbachWeightG11PaidBase N ε : ℝ) -
        (goldbachB9LowPositivePrefixSiftedCount N ε Zlow : ℝ) +
        (goldbachWeightHighFirstCoefficient ε - 8*goldbachG11PrimeIntegral (fun _ => 1) - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        4*(D19 N : ℝ) := by
  simpa only [mul_one] using goldbachWeight_g11NormalizedIntegral_consumed 1 δ ε
    zero_le_one hδ (fun _ hu => buchstab_le_one (by linarith [hu.1])) hε hεu

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig