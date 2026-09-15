import Wu18938Campaign.M1.Confirmed.PairProfileFamily
import Wu18938Campaign.M1.Confirmed.ProfileGrid

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem full_profile_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (H : ℝ → ℝ) (hm : Antitone H)
    (hH : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 2) (childEta p η) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ 3 →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) v ≤
          (1 - H v + ρ) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
        (Pair.classicalIntegral p j - (∫ v : ℝ × ℝ, ProfileGrid.kernel p j H v) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨F,hF,hg⟩ := ProfileGrid.sufficient_family hp j hm hH (half_pos he)
  obtain ⟨ρ,hρ,T,hT4,hT⟩ := finite_profile_upper p hp j F hF m hη hδ (half_pos he)
  refine ⟨ρ,hρ,T,hT4,?_⟩
  intro N hN heven i Δ V hb hn
  have hc := hT N hN heven i Δ V hb (fun r => H r.sample)
    (fun r _ => hH r.sample ⟨r.sample_lower.le,r.sample_upper.le⟩)
    (fun r _ k U hu => hn k U hu r.sample r.sample_lower.le r.sample_upper.le)
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (Rebox.theta_nonneg hb (by omega) hη hδ)
  linarith only [hg]

theorem full_profile_actual (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (H : ℝ → ℝ) (hm : Antitone H)
    (hH : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε)
    (hn : ∀ ρ : ℝ, 0 < ρ → ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox (m + 2) (childEta p η) δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ 3 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) v ≤
        (1 - H v + ρ) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
        (Pair.classicalIntegral p j - (∫ v : ℝ × ℝ, ProfileGrid.kernel p j H v) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ρ,hρ,T0,hT04,h0⟩ := full_profile_upper p hp j H hm hH m hη hδ he
  obtain ⟨T1,_,h1⟩ := hn ρ hρ
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  exact h0 N (by omega) heven i Δ V hb
    (fun k U hu v hv hv3 => h1 N (by omega) heven k Δ U hu v hv hv3)

end Wu18938Campaign.M1.Confirmed.Pair
