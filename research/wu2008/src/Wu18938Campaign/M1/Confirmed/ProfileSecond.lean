import Wu18938Campaign.M1.Confirmed.PairFullProfile
import Wu18938Campaign.M1.Confirmed.ProfileOmega
import Wu18938Campaign.M1.Confirmed.SecondFiniteUpdate

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

def secondProfileCoefficient (p : SecondFunctionalParameters) (δ : ℝ)
    (u f H : ℝ → ℝ) : ℝ :=
  4 * u p.S + u p.kappa1 -
    Rebox.profileJ f p.s p.S - Rebox.profileJ f p.kappa2 p.S - Rebox.profileJ f p.kappa3 p.S +
    (∑ j : Term, Pair.classicalIntegral p j - ∫ v : ℝ × ℝ, ProfileGrid.kernel p j H v) +
    2 / (1 - 2 * δ) *
      (omega3XIntegralEnvelope p.kappa3 p.kappa1 + SecondFunctionalCoupled.jointSup p)

theorem second_profile_actual (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (u f H : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 1 10))
    (hfb : ∀ v ∈ Set.Icc (1 : ℝ) 10, 0 ≤ f v ∧ f v ≤ 10)
    (hH : Antitone H) (hHb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε)
    (hu : ∀ ρ : ℝ, 0 < ρ → ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) v ≤
        (u v + ρ) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V))
    (hl : ∀ ρ : ℝ, 0 < ρ → ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox (m + 1) (η / 20) δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
      (f v - ρ) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) v)
    (hpair : ∀ ρ : ℝ, 0 < ρ → ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ),
      RoughBox (m + 2) (Pair.childEta p η) δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ 3 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) v ≤
        (1 - H v + ρ) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        (secondProfileCoefficient p δ u f H + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hε : 0 < ε / 13 := by positivity
  obtain ⟨T0,hT04,h0⟩ := roughBox_mother_thirteen_paid p hp.mother hp.two_lt_s hp.s_le_three
    m hη hδ (by linarith) hε
  obtain ⟨T1,_,h1⟩ := hu (ε / 13) hε
  obtain ⟨T2,_,h2⟩ := Rebox.profile_omega2_actual f hf hfb m hη hδ hε hl
  choose TG hTG4 hTG using
    (fun j : Term => Pair.full_profile_actual p hp j H hH hHb m hη hδ hε hpair)
  refine ⟨max T0 (max T1 (max T2 (univ.sup TG))),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hkS := hp.mother.kappa1_le_S
  have hk2S := hp.mother.kappa2_lt_kappa1.le.trans hkS
  have hk3S := hp.mother.kappa3_lt_kappa2.le.trans hk2S
  have hsS := hp.mother.s_le_kappa3.trans hk3S
  have hm := h0 N (by omega) heven i Δ V hb
  have huS := h1 N (by omega) heven i Δ V hb p.S (by linarith [hp.three_le_S]) hp.mother.S_le_ten
  have huk := h1 N (by omega) heven i Δ V hb p.kappa1
    (hp.mother.one_le_s.trans (hp.mother.s_le_kappa3.trans
      (hp.mother.kappa3_lt_kappa2.le.trans hp.mother.kappa2_lt_kappa1.le)))
    (hkS.trans hp.mother.S_le_ten)
  have ho1 := h2 N (by omega) heven i Δ V hb p.s p.S hp.two_lt_s.le hsS hp.three_le_S hp.S_le_five
  have ho2 := h2 N (by omega) heven i Δ V hb p.kappa2 p.S
    (hp.two_lt_s.le.trans (hp.mother.s_le_kappa3.trans hp.mother.kappa3_lt_kappa2.le))
    hk2S hp.three_le_S hp.S_le_five
  have ho3 := h2 N (by omega) heven i Δ V hb p.kappa3 p.S
    (hp.two_lt_s.le.trans hp.mother.s_le_kappa3) hk3S hp.three_le_S hp.S_le_five
  have hg (j : Term) := hTG j N (by have hh := le_sup (f := TG) (mem_univ j); omega)
    heven i Δ V hb
  have hgs := sum_le_sum (fun j (_ : j ∈ (univ : Finset Term)) => hg j)
  rw [← gamma_sum_dictionary p N δ (convolutionWuWindows N Δ V)] at hgs
  have hcard : Fintype.card Term = 4 := by decide
  simp only [← sum_mul,sum_add_distrib,sum_const,card_univ,hcard,nsmul_eq_mul,Nat.cast_ofNat] at hgs
  have hc := roughBox_joint_theta hb (by omega) hη hδ p hp.mother hp.two_lt_s.le
  have henv := Rebox.omega3_envelope hb (by omega) hη hδ
    (hp.two_lt_s.le.trans hp.mother.s_le_kappa3)
    (hp.mother.kappa3_lt_kappa2.le.trans hp.mother.kappa2_lt_kappa1.le)
    (hkS.trans hp.mother.S_le_ten)
  have hcost := mul_le_mul_of_nonneg_left (add_le_add hc henv)
    (show 0 ≤ 2 / (1 - 2 * δ) from div_nonneg (by norm_num) (by linarith))
  rw [secondFunctionalCombinedTheta_eq] at hcost
  unfold secondProfileCoefficient
  nlinarith only [hm,huS,huk,ho1,ho2,ho3,hgs,hcost,Rebox.theta_nonneg hb (by omega) hη hδ]

end Wu18938Campaign.M1.Confirmed
