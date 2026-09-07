import MathlibNt.SieveTheory.LiLiuGoldbachPairIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpOutputIntegral

open scoped BigOperators
open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Repackage the already proved pair estimates at their original actual counts.
No new pair estimate or integral certificate is assumed. -/
theorem goldbachG11Author_reused_pair_lower (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachG67IntegralConstant-δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        (goldbachWeightG6 (goldbachDifferenceCarrier N ε) N
          ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) +
        (goldbachWeightG7 (goldbachDifferenceCarrier N ε) N
          ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
          ((N : ℝ)^(3/11 : ℝ)) : ℝ) := by
  obtain ⟨ρ,hρ,hρk,hpay⟩ := exists_goldbachG67_integral_tolerance (δ/2) (half_pos hδ)
  obtain ⟨B,hB,C,_hC,hpaid⟩ := goldbachG67_movingKernel_paid 3 (by norm_num)
  obtain ⟨ε₀,he,heu,hnorm⟩ := goldbachG67_ideal_normalized B ρ hB hρ hρk
  obtain ⟨L,_,hpair⟩ := goldbachG67IdealSum_integral_lower (2*ρ) ρ (by positivity) hρ
  obtain ⟨E,herr⟩ := eventually_atTop.mp (goldbachBV_logCube_normalized C (δ/4) (by positivity))
  refine ⟨ε₀,he,heu,?_⟩
  intro ε hε hεu
  obtain ⟨P,hP,hp⟩ := hpaid ρ hρ ε hε (hεu.trans_le heu)
  obtain ⟨Q,_,hq⟩ := hnorm ε hε hεu
  refine ⟨max P (max Q (max L E)),by omega,?_⟩
  intro N hN hEven
  obtain ⟨h6,h7⟩ := hp N (by omega) hEven
  obtain ⟨hn6,hn7⟩ := hq N (by omega) hEven
  have hi := hpair N (by omega)
  have heN := herr N (by omega)
  simp only [Real.rpow_ofNat] at h6 h7
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hi' := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hρk.le)
  have hb := mul_le_mul_of_nonneg_right (hpay.trans hi') hs
  nlinarith only [hb,hn6,hn7,h6,h7,heN]

/-- Reuse both original G12 exception payments and the proved sharp output bound. -/
theorem goldbachG11Author_reused_cross_upper (δ ε : ℝ) (hδ : 0 < δ)
    (hε : 0 < ε) (hεu : ε ≤ 2/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightG12 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
        ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤
      (goldbachG12SharpIntegralConstant+δ)*
        (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨L,hL,hl⟩ := goldbachWeightG12_le_roughSum_add_normalized (δ/3) (by positivity)
  obtain ⟨M,_,hm⟩ := goldbachG12_roughSum_le_productPrime_normalized (δ/3) (by positivity)
  obtain ⟨K,_,hk⟩ := G12SharpOutput.original_total_integral (δ/3) (by positivity) ε hε hεu
  refine ⟨max L (max M K),by omega,?_⟩
  intro N hN hEven
  have h1 := hl N (by omega) ε hε.le ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))
  have h2 := hm N (by omega) ε hε.le ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))
  have h3 := hk N (by omega) hEven
  nlinarith only [h1,h2,h3]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig