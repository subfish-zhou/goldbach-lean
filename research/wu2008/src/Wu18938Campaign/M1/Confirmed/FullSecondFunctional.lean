import Wu18938Campaign.M1.Confirmed.FullPairActual

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullProfile

open Wu2008DoubleSieve MotherPair Finset Real NodeExtension ActualNineFeedback FiniteProfile
open scoped Classical

def coefficient (p : SecondFunctionalParameters) (δ : ℝ) (H : ℝ → ℝ) : ℝ :=
  4 * upperExtension H (aProfile H) p.S + upperExtension H (aProfile H) p.kappa1 -
    Rebox.profileJ (lowerExtension H (aProfile H)) p.s p.S -
    Rebox.profileJ (lowerExtension H (aProfile H)) p.kappa2 p.S -
    Rebox.profileJ (lowerExtension H (aProfile H)) p.kappa3 p.S +
    (∑ k : Term, (Pair.classicalIntegral p k - ∫ v : ℝ × ℝ, PairLiteral.kernel p k H v)) +
    2 / (1 - 2 * δ) *
      (omega3XIntegralEnvelope p.kappa3 p.kappa1 + SecondFunctionalCoupled.jointSup p)

def secondGain (p : SecondFunctionalParameters) (δ : ℝ) (H : ℝ → ℝ) : ℝ :=
  1 - coefficient p δ H / 5

theorem second_gain_actual (j : Fin 4) {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hn : UpperNodes δ (fun v => 1 - H v) 3)
    (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (coupledRow j).s ≤
        (1 - secondGain (coupledRow j) δ H + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let p := coupledRow j
  have hp : AnalyticParameters p := (coupledRow_geometry j).1
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  have ha := aProfile_bounds hH hb
  obtain ⟨hl,hu⟩ := full_extensions_actual hH hb hδ hn
  let e := ε / 13
  have he' : 0 < e := by dsimp [e]; positivity
  obtain ⟨T0,hT04,h0⟩ := roughBox_mother_thirteen_paid p hp.mother hp.two_lt_s hp.s_le_three
    m hη hδ (by linarith) he'
  obtain ⟨T1,_,h1⟩ := hu m η e hη he'
  obtain ⟨T2,_,h2⟩ := Rebox.profile_omega2_actual (lowerExtension H (aProfile H))
    ((lowerExtension_mono hH hb1 ha.1).monotoneOn _) (by
      intro v _
      have hh := lowerExtension_bounds hH hb1 ha.1 v
      exact ⟨hh.1,hh.2.trans (by linarith [ha.2,log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)])⟩)
    m hη hδ he' (fun ρ hρ => hl (m + 1) (η / 20) ρ (by positivity) hρ)
  choose TG hTG4 hTG using (fun k : Term =>
    FullFive.all_pair_actual j H hH hb1 hδ hn k m hη he')
  refine ⟨max T0 (max T1 (max T2 (univ.sup TG))),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hbox
  have hkS := hp.mother.kappa1_le_S
  have hk2S := hp.mother.kappa2_lt_kappa1.le.trans hkS
  have hk3S := hp.mother.kappa3_lt_kappa2.le.trans hk2S
  have hsS := hp.mother.s_le_kappa3.trans hk3S
  have hm := h0 N (by omega) heven i Δ V hbox
  have huS := h1 N (by omega) heven i Δ V hbox p.S (by linarith [hp.three_le_S]) hp.S_le_five
  have huk := h1 N (by omega) heven i Δ V hbox p.kappa1
    (hp.mother.one_le_s.trans (hp.mother.s_le_kappa3.trans
      (hp.mother.kappa3_lt_kappa2.le.trans hp.mother.kappa2_lt_kappa1.le)))
    (hkS.trans hp.S_le_five)
  have ho1 := h2 N (by omega) heven i Δ V hbox p.s p.S hp.two_lt_s.le hsS hp.three_le_S hp.S_le_five
  have ho2 := h2 N (by omega) heven i Δ V hbox p.kappa2 p.S
    (hp.two_lt_s.le.trans (hp.mother.s_le_kappa3.trans hp.mother.kappa3_lt_kappa2.le))
    hk2S hp.three_le_S hp.S_le_five
  have ho3 := h2 N (by omega) heven i Δ V hbox p.kappa3 p.S
    (hp.two_lt_s.le.trans hp.mother.s_le_kappa3) hk3S hp.three_le_S hp.S_le_five
  have hg (k : Term) := hTG k N (by have hh := le_sup (f := TG) (mem_univ k); omega)
    heven i Δ V hbox
  have hgs := sum_le_sum (fun k (_ : k ∈ (univ : Finset Term)) => hg k)
  rw [← gamma_sum_dictionary p N δ (convolutionWuWindows N Δ V)] at hgs
  have hcard : Fintype.card Term = 4 := by decide
  simp only [← sum_mul,sum_add_distrib,sum_const,card_univ,hcard,nsmul_eq_mul,Nat.cast_ofNat] at hgs
  have hc := roughBox_joint_theta hbox (by omega) hη hδ p hp.mother hp.two_lt_s.le
  have henv := Rebox.omega3_envelope hbox (by omega) hη hδ
    (hp.two_lt_s.le.trans hp.mother.s_le_kappa3)
    (hp.mother.kappa3_lt_kappa2.le.trans hp.mother.kappa2_lt_kappa1.le)
    (hkS.trans hp.mother.S_le_ten)
  have hcost := mul_le_mul_of_nonneg_left (add_le_add hc henv)
    (show 0 ≤ 2 / (1 - 2 * δ) from div_nonneg (by norm_num) (by linarith))
  rw [secondFunctionalCombinedTheta_eq] at hcost
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤ _
  unfold secondGain coefficient
  dsimp only [e] at hm huS huk ho1 ho2 ho3 hgs
  dsimp only [p] at hm huS huk ho1 ho2 ho3 hgs hcost ⊢
  nlinarith only [hm,huS,huk,ho1,ho2,ho3,hgs,hcost,he.le,Rebox.theta_nonneg hbox (by omega) hη hδ]

end Wu18938Campaign.M1.Confirmed.FullProfile
