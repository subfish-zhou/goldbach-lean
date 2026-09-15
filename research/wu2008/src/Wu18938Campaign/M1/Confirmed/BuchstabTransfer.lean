import Wu18938Campaign.M1.Confirmed.BuchstabIntegral
import MathlibNt.Wu2008DoubleSieve.PhiBuchstab

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology Interval

theorem upper_node_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ (f : ℝ → ℝ) (vmax : ℝ), MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, 0 ≤ f v ∧ f v ≤ 11) →
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ vmax →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) v ≤
          f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → t - 1 ≤ vmax →
      reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
        ((∫ u in (s - 1)..(t - 1), f u / u) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := upper_node_to_raw m hη hδ (show 0 < ε / 3 by positivity)
  obtain ⟨T1,_,h1⟩ := upperMain_to_prime m hη hδ
  obtain ⟨T2,_,h2⟩ := shiftedPrime_to_source m hη hδ
  obtain ⟨T3,_,h3⟩ := shifted_boundary_relative m hη hδ (show 0 < ε / 3 by positivity)
  obtain ⟨T4,_,h4⟩ := shifted_prime_integral m hη hδ (show 0 < ε / 3 by positivity)
  refine ⟨max T0 (max T1 (max T2 (max T3 T4))),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb f vmax hf hfb hn s t hs hst ht htv
  have hf0 := fun v hv => (hfb v hv).1
  have hfa : ∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11 := fun v hv =>
    (abs_of_nonneg (hfb v hv).1).trans_le (hfb v hv).2
  obtain ⟨r,hr,_,hraw⟩ := h0 N (by omega) heven i Δ V hb f vmax hn s t hs hst ht htv
  have hnorm := h1 N (by omega) i Δ V hb f hf hf0 s t hs hst ht r hr
  have hsource := h2 N (by omega) i Δ V hb f hf0 s t hs hst ht r hr
  have hbound := h3 N (by omega) i Δ V hb f hfa t (hs.trans hst) ht
  have hint := (abs_le.mp (h4 N (by omega) i Δ V hb f hf hfa s t hs hst ht)).2
  nlinarith only [hraw,hnorm,hsource,hbound,hint]

theorem lower_node_update (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ (f : ℝ → ℝ) (vmax : ℝ), MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, 0 ≤ f v ∧ f v ≤ 11) →
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ vmax →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) v ≤
          f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → t - 1 ≤ vmax →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) t -
        ((∫ u in (s - 1)..(t - 1), f u / u) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  obtain ⟨T,hT4,hT⟩ := upper_node_integral m hη hδ he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb f vmax hf hfb hn s t hs hst ht htv
  have hu := hT N hN heven i Δ V hb f vmax hf hfb hn s t hs hst ht htv
  have hid := wuBoxPhi_buchstab (convolutionWuWindows N Δ V)
    (fun d hd => (hb.support_geometry (by omega) hη hδ hd).2.2.1.le)
    (by linarith : 0 < s) hst
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) t =
    wuBoxPhi N δ (convolutionWuWindows N Δ V) s +
      reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) at hid
  linarith only [hu,hid]

end Wu18938Campaign.M1.Confirmed.Rebox
