import Wu18938Campaign.M1.Confirmed.PairFiniteGain
import Wu18938Campaign.M1.Confirmed.PairMother
import Wu18938Campaign.M1.Confirmed.FirstFiniteUpdate
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledKernel

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical Interval

theorem roughBox_joint_theta {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    (∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
      secondFunctionalCombinedTheta N δ Δ V p ≤
      SecondFunctionalCoupled.jointSup p *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  rw [← SecondFunctionalCoupled.theta_exact]
  apply (roughBox_payload_theta_bounds hb hN hη hδ _ _).2
  intro d hd
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hh := roughBox_log_geometry hb (by omega) hη hδ hd
    linarith [hh.2.2.1]
  exact ⟨(SecondFunctionalCoupled.kernel_bounds p hp hs _).1,
    SecondFunctionalCoupled.kernel_le_jointSup p hp hs hphi⟩

theorem gamma_sum_dictionary (p : SecondFunctionalParameters) (N : ℕ) (δ : ℝ)
    {i : ℕ} (W : Fin i → Finset ℕ) :
    (∑ j ∈ Icc 5 8, secondFunctionalMotherGammaSum p N δ W j) =
      ∑ j : Term, secondFunctionalMotherGammaSum p N δ W j.index := by
  rw [show Icc 5 8 = {5,6,7,8} by decide,
    show (univ : Finset Term) = {Term.gammaFive,Term.gammaSix,Term.gammaSeven,Term.gammaEight} by
      ext j
      cases j <;> simp]
  simp only [sum_insert (by decide : (5 : ℕ) ∉ {6,7,8}),
    sum_insert (by decide : (6 : ℕ) ∉ {7,8}),
    sum_insert (by decide : (7 : ℕ) ∉ {8}),sum_singleton,
    sum_insert (by decide : Term.gammaFive ∉ {Term.gammaSix,Term.gammaSeven,Term.gammaEight}),
    sum_insert (by decide : Term.gammaSix ∉ {Term.gammaSeven,Term.gammaEight}),
    sum_insert (by decide : Term.gammaSeven ∉ {Term.gammaEight}),Term.index]

theorem roughBox_four_gamma_seed (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (hrs : r.sample ≤ 13 / 5)
    (m : ℕ) {η δ τ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (∑ k ∈ Icc 5 8, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) k) ≤
        ((1 + τ) ^ 2 * (∑ k : Term, Pair.classicalIntegral p k) -
          HighSixPhase7.seed * rectIntegral r.A r.B r.C r.D + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := Pair.gamma_rectangle_seed p hp j r hrs m hη hδ hδhi hτ
    (show 0 < ε / 4 by positivity)
  obtain ⟨T1,_,h1⟩ := Pair.gamma_integral p hp m hη hδ hτ (show 0 < ε / 4 by positivity)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hpoint (k : Term) :
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) k.index ≤
        ((1 + τ) ^ 2 * Pair.classicalIntegral p k -
          (if k = j then HighSixPhase7.seed * rectIntegral r.A r.B r.C r.D else 0) + ε / 4) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    by_cases hkj : k = j
    · subst k
      simpa using h0 N (by omega) heven i Δ V hb
    · rw [if_neg hkj,sub_zero,add_mul]
      exact h1 N (by omega) heven i Δ V hb k
  rw [gamma_sum_dictionary]
  have hsum := sum_le_sum (fun k (_ : k ∈ (univ : Finset Term)) => hpoint k)
  have hcard : Fintype.card Term = 4 := by decide
  simpa only [← sum_mul,sum_add_distrib,sum_sub_distrib,← mul_sum,
    sum_ite_eq',mem_univ,if_true,sum_const,card_univ,hcard,nsmul_eq_mul,Nat.cast_ofNat,
    show (4 : ℝ) * (ε / 4) = ε by ring] using hsum

theorem roughBox_second_finite_update (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (hratio : 2 ≤ p.S - p.S / p.s)
    (j : Term) (r : GainRectangle p j) (hrs : r.sample ≤ 13 / 5)
    (m : ℕ) {η δ τ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
          (∫ u in (1 - 1 / p.s)..(1 - 1 / p.S), log (p.S * u - 1) / (u * (1 - u))) -
          (∫ u in (1 - 1 / p.kappa2)..(1 - 1 / p.S), log (p.S * u - 1) / (u * (1 - u))) -
          (∫ u in (1 - 1 / p.kappa3)..(1 - 1 / p.S), log (p.S * u - 1) / (u * (1 - u))) +
          (1 + τ) ^ 2 * (∑ k : Term, Pair.classicalIntegral p k) -
          HighSixPhase7.seed * rectIntegral r.A r.B r.C r.D +
          (2 / (1 - 2 * δ)) * (omega3XIntegralEnvelope p.kappa3 p.kappa1 +
            SecondFunctionalCoupled.jointSup p) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_mother_thirteen_paid p hp.mother hp.two_lt_s hp.s_le_three
    m hη hδ (by linarith) (show 0 < ε / 10 by positivity)
  obtain ⟨T1,_,h1⟩ := roughBox_four_gamma_seed p hp j r hrs m hη hδ hδhi hτ
    (show 0 < ε / 10 by positivity)
  obtain ⟨T2,_,h2⟩ := Rebox.classical_omega2 m hη hδ (show 0 < ε / 10 by positivity)
  obtain ⟨T3,_,h3⟩ := roughBox_upper_leaf_bounded m hη hδ (show 0 < ε / 10 by positivity)
  refine ⟨max T0 (max T1 (max T2 T3)),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hks := hp.mother.s_le_kappa3
  have hk32 := hp.mother.kappa3_lt_kappa2.le
  have hk21 := hp.mother.kappa2_lt_kappa1.le
  have hk1S := hp.mother.kappa1_le_S
  have hratio' (u : ℝ) (hu : p.s ≤ u) : 2 ≤ p.S - p.S / u := by
    have hh := div_le_div_of_nonneg_left (show 0 ≤ p.S by linarith [hp.three_le_S])
      (show 0 < p.s by linarith [hp.two_lt_s]) hu
    linarith
  have hm := h0 N (by omega) heven i Δ V hb
  have hg := h1 N (by omega) heven i Δ V hb
  have hO1 := h2 N (by omega) heven i Δ V hb p.s p.S hp.two_lt_s.le
    (hks.trans (hk32.trans (hk21.trans hk1S))) hp.three_le_S hp.S_le_five hratio
  have hO2 := h2 N (by omega) heven i Δ V hb p.kappa2 p.S
    (hp.two_lt_s.le.trans (hks.trans hk32)) (hk21.trans hk1S) hp.three_le_S hp.S_le_five
    (hratio' _ (hks.trans hk32))
  have hO3 := h2 N (by omega) heven i Δ V hb p.kappa3 p.S
    (hp.two_lt_s.le.trans hks) (hk32.trans (hk21.trans hk1S)) hp.three_le_S hp.S_le_five
    (hratio' _ hks)
  have hP1 := h3 N (by omega) heven i Δ V hb p.S (by linarith [hp.three_le_S]) hp.mother.S_le_ten
  have hP2 := h3 N (by omega) heven i Δ V hb p.kappa1
    (hp.mother.one_le_s.trans (hks.trans (hk32.trans hk21))) (hk1S.trans hp.mother.S_le_ten)
  have hc := roughBox_joint_theta hb (by omega) hη hδ p hp.mother hp.two_lt_s.le
  have henv := Rebox.omega3_envelope hb (by omega) hη hδ
    (hp.two_lt_s.le.trans hks) (hk32.trans hk21) (hk1S.trans hp.mother.S_le_ten)
  have hcost := mul_le_mul_of_nonneg_left (add_le_add hc henv)
    (show 0 ≤ 2 / (1 - 2 * δ) from div_nonneg (by norm_num) (by linarith))
  have heq : secondFunctionalCombinedTheta N δ Δ V p =
      HighSourcePayload.pairedTheta N δ Δ V p +
        ∑ k : Fin 4, FourPrimeNonunit.sourceKTheta N δ Δ V p k := by
    exact secondFunctionalCombinedTheta_eq N δ Δ V p
  rw [heq] at hcost
  nlinarith only [hm,hg,hO1,hO2,hO3,hP1,hP2,hcost]

end Wu18938Campaign.M1.Confirmed
