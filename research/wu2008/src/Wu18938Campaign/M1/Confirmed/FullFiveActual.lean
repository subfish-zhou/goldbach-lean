import Wu18938Campaign.M1.Confirmed.FullFiveApproximation
import Wu18938Campaign.M1.Confirmed.ProfileActualExtension

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullFive

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem profile_upper (p : SecondFunctionalParameters) (hp : WuPaper.R2Gamma5.FullParameters p)
    (H : ℝ → ℝ) (hm : Antitone H)
    (hH : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 2) (Pair.childEta p η) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ 3 →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) v ≤
          (1 - H v + ρ) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 5 ≤
        (Pair.classicalIntegral p .gammaFive - (∫ v : ℝ × ℝ, kernel p H v) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨F,hF,hg⟩ := sufficient_family hp hm hH (half_pos he)
  obtain ⟨ρ,hρ,T,hT4,hT⟩ := finite_profile_upper p hp.toAnalyticParameters F hF m hη hδ (half_pos he)
  refine ⟨ρ,hρ,T,hT4,?_⟩
  intro N hN heven i Δ V hb hn
  have hc := hT N hN heven i Δ V hb (fun r => H r.sample)
    (fun r _ => hH r.sample ⟨r.sample_lower.le,r.sample_upper.le⟩)
    (fun r _ k U hu => hn k U hu r.sample r.sample_lower.le r.sample_upper.le)
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (Rebox.theta_nonneg hb (by omega) hη hδ)
  linarith only [hg]

theorem profile_actual (p : SecondFunctionalParameters) (hp : WuPaper.R2Gamma5.FullParameters p)
    (H : ℝ → ℝ) (hm : Antitone H)
    (hH : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hn : FiniteProfile.UpperNodes δ (fun v => 1 - H v) 3)
    (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 5 ≤
        (Pair.classicalIntegral p .gammaFive - (∫ v : ℝ × ℝ, kernel p H v) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ρ,hρ,T0,hT04,h0⟩ := profile_upper p hp H hm hH m hη hδ he
  obtain ⟨T1,_,h1⟩ := hn (m + 2) (Pair.childEta p η) ρ
    (Pair.childEta_pos hp.toAnalyticParameters hη) hρ
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  exact h0 N (by omega) heven i Δ V hb
    (fun k U hu v hv hv3 => h1 N (by omega) heven k Δ U hu v hv hv3)

end Wu18938Campaign.M1.Confirmed.FullFive
