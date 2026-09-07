import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorReusedCounts
import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorCountLedger
import MathlibNt.SieveTheory.LiLiuGoldbachOneNineUnconditional

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The author G11 estimate and the previously certified G67/G9/G12 estimates
are all applied to their original counts before the signed ledger is closed. -/
theorem goldbachWeight_authorG11_numericLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ((515093/200000000 : ℝ)-δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          4*(D19 N : ℝ) := by
  obtain ⟨εb,hεb,hεbu,hbase⟩ :=
    goldbachWeight_paperSplit_authorG11_consumed_small_epsilon (δ/3) (by positivity)
  obtain ⟨εp,hεp,_,hpair⟩ := goldbachG11Author_reused_pair_lower (δ/3) (by positivity)
  refine ⟨min εb εp,lt_min hεb hεp,(min_le_left _ _).trans hεbu,?_⟩
  intro ε hε hεu
  have hbε := hεu.trans_le (min_le_left εb εp)
  obtain ⟨L,hL,hl⟩ := hbase ε hε hbε
  obtain ⟨M,_,hm⟩ := hpair ε hε (hεu.trans_le (min_le_right _ _))
  obtain ⟨K,_,hk⟩ := goldbachG11Author_reused_cross_upper (δ/3) ε
    (by positivity) hε (hbε.le.trans hεbu)
  refine ⟨max L (max M K),by omega,?_⟩
  intro N hN hEven
  have hb := hl N (by omega) hEven
  have hp := hm N (by omega) hEven
  have hx := hk N (by omega) hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hc : (515093/200000000 : ℝ) ≤ goldbachG67IntegralConstant +
      124341093/200000000 - goldbachB9PaperSplitIntegral - 10191/100000 -
      goldbachG12SharpIntegralConstant := by
    have h67 := goldbachG67IntegralConstant_lower_certified
    have h9 := G9Analytic.actual_le_target
    have h12 := G12AnalyticCertificate.actual_le_target
    linarith only [h67,h9,h12]
  have hcm := mul_le_mul_of_nonneg_right hc hs
  push_cast at hb
  nlinarith only [hb,hp,hx,hcm]

/-- Any fixed coefficient strictly below the retained author-G11 ceiling.
The common natural threshold follows the coefficient, and no epsilon remains. -/
theorem goldbach_D19_author_lower_of_coefficient_lt (κ : ℝ)
    (hκ : κ < (515093/800000000 : ℝ)) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      κ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        (D19 N : ℝ) := by
  let δ : ℝ := (515093/200000000 : ℝ)-4*κ
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hκ]
  obtain ⟨ε₀,he,_,hl⟩ := goldbachWeight_authorG11_numericLedger δ hδ
  obtain ⟨K,hK,hk⟩ := hl (ε₀/2) (half_pos he) (half_lt_self he)
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have h := hk N hN hEven
  dsimp [δ] at h
  nlinarith only [h]

/-- The paper's strict 0.0004 bound for the original number of distinct primes.
A fixed stronger certified coefficient pays strictness; no limiting endpoint
coefficient is asserted. -/
theorem goldbach_D19_gt_paper_0004 :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (1/2500 : ℝ)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) <
        (D19 N : ℝ) := by
  obtain ⟨K,hK,hk⟩ := goldbach_D19_author_lower_of_coefficient_lt (1/2000) (by norm_num)
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have hs : 0 < SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_pos (mul_pos (SingularSeries.liuSingularSeries_pos N)
      (by exact_mod_cast (show 0 < N by omega)))
      (sq_pos_of_pos (Real.log_pos (by exact_mod_cast (show 1 < N by omega))))
  exact (mul_lt_mul_of_pos_right (by norm_num : (1/2500 : ℝ) < 1/2000) hs).trans_le
    (hk N hN hEven)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig