import Wu18938Campaign.M1.Confirmed.ProfileCycle
import Wu18938Campaign.M1.Confirmed.ProfileSecond

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension
open scoped Classical Interval

def secondGain (p : SecondFunctionalParameters) (δ : ℝ) (H : ℝ → ℝ) : ℝ :=
  1 - secondProfileCoefficient p δ (upperExtension H (aProfile H))
    (lowerExtension H (aProfile H)) H / 5

theorem second_gain_actual (p : SecondFunctionalParameters) (hp : MotherPair.AnalyticParameters p)
    {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hHnode : UpperNodes δ (fun v => 1 - H v) 3)
    (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        (1 - secondGain p δ H + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  have ha := aProfile_bounds hH hb
  obtain ⟨hl,hu⟩ := full_extensions_actual hH hb hδ hHnode
  obtain ⟨T,hT4,hT⟩ := second_profile_actual p hp _ _ H
    ((lowerExtension_mono hH hb1 ha.1).monotoneOn _) (by
      intro v _
      have hh := lowerExtension_bounds hH hb1 ha.1 v
      exact ⟨hh.1,hh.2.trans (by linarith [ha.2,log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)])⟩)
    hH hb1 m hη hδ hδhi (show 0 < 5 * ε by positivity)
    (fun ρ hρ => hu m η ρ hη hρ)
    (fun ρ hρ => hl (m + 1) (η / 20) ρ (by positivity) hρ)
    (fun ρ hρ => hHnode (m + 2) (Pair.childEta p η) ρ (Pair.childEta_pos hp hη) hρ)
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hbox
  have hh := hT N hN heven i Δ V hbox
  unfold secondGain
  nlinarith only [hh]

def firstCoefficient (δ s t : ℝ) (H : ℝ → ℝ) : ℝ :=
  upperExtension H (aProfile H) t -
    profileJ (lowerExtension H (aProfile H)) s t / 2 +
    omega3XIntegralEnvelope s t / (1 - 2 * δ)

def firstGain (δ s t : ℝ) (H : ℝ → ℝ) : ℝ := 1 - firstCoefficient δ s t H

theorem first_gain_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hHnode : UpperNodes δ (fun v => 1 - H v) 3)
    (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (1 - firstGain δ s t H + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  have ha := aProfile_bounds hH hb
  obtain ⟨hl,hu⟩ := full_extensions_actual hH hb hδ hHnode
  obtain ⟨T0,hT04,h0⟩ := roughBox_first_integral m hη hδ (by linarith) (half_pos he)
  obtain ⟨T1,_,h1⟩ := hu m η (ε / 2) hη (half_pos he)
  obtain ⟨T2,_,h2⟩ := profile_omega2_actual (lowerExtension H (aProfile H))
    ((lowerExtension_mono hH hb1 ha.1).monotoneOn _) (by
      intro v _
      have hh := lowerExtension_bounds hH hb1 ha.1 v
      exact ⟨hh.1,hh.2.trans (by linarith [ha.2,log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)])⟩)
    m hη hδ (half_pos he)
    (fun ρ hρ => hl (m + 1) (η / 20) ρ (by positivity) hρ)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hbox
  have hm := h0 N (by omega) heven i Δ V hbox s t hs hst (by linarith)
  have hpos := h1 N (by omega) heven i Δ V hbox t (by linarith) ht5
  have hneg := h2 N (by omega) heven i Δ V hbox s t hs hst ht ht5
  have henv := omega3_envelope hbox (by omega) hη hδ hs hst (by linarith : t ≤ 10)
  have hpay := mul_le_mul_of_nonneg_left henv
    (show 0 ≤ 2 / (1 - 2 * δ) by apply div_nonneg (by norm_num); linarith)
  have heq : 2 / (1 - 2 * δ) * (omega3XIntegralEnvelope s t *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) =
      2 * (omega3XIntegralEnvelope s t / (1 - 2 * δ)) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by ring
  rw [heq] at hpay
  unfold firstGain firstCoefficient
  nlinarith only [hm,hpos,hneg,hpay]

end Wu18938Campaign.M1.Confirmed.FiniteProfile
