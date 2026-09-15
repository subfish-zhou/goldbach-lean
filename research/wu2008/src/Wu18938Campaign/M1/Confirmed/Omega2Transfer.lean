import Wu18938Campaign.M1.Confirmed.Omega2Boundary
import Wu18938Campaign.M1.Confirmed.FirstFunctional

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical Interval

theorem node_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
        f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ U) v) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      ((∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))) - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  have he5 : 0 < ε / 5 := by positivity
  obtain ⟨T0,hT04,h0⟩ := node_to_omega2 m hη hδ he5
  obtain ⟨T1,_,h1⟩ := geometric_to_node m hη hδ
  obtain ⟨T2,_,h2⟩ := repeated_relative m hη hδ (show 0 < η / 20 by positivity)
    (show 0 < ε / 55 by positivity)
  obtain ⟨T3,_,h3⟩ := absolute_boundary_relative m hη hδ he5
  obtain ⟨T4,_,h4⟩ := prime_integral m hη hδ he5
  obtain ⟨T5,_,h5⟩ := scale m hη hδ
  refine ⟨max T0 (max T1 (max T2 (max T3 (max T4 T5)))),
    hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb f hf hfb hn s t hs hst ht ht5
  obtain ⟨r,hrlo,hrhi,hraw⟩ := h0 N (by omega) heven i Δ V hb f hn s t hs hst ht ht5
  have hnorm := h1 N (by omega) i Δ V hb f hf hfb s t hs hst ht ht5 r hrlo
  have hrepeat := h2 N (by omega) i Δ V hb
  have hright := h3 N (by omega) i Δ V hb f hfb s t hs hst ht ht5 r ⟨hrlo,hrhi⟩
  have hwindow := prime_to_geometric hb (by omega) hη hδ f hs hst hrlo
  obtain ⟨hΔ,_,_,hq,_,_⟩ := h5 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hz : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp only [Nat.cast_zero,reboxingAlpha_zero,le_refl]
    · simpa [reboxingAlpha] using mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq0 (1 / t))
  have hleft := h3 N (by omega) i Δ V hb f hfb t t (by linarith) le_rfl ht ht5 0 hz
  have hmain := (abs_le.mp (h4 N (by omega) i Δ V hb f hf hfb s t hs hst ht ht5)).1
  linarith only [hraw,hnorm,hrepeat,hright,hwindow,hleft,hmain]

theorem first_node_update (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
        f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ U) v) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      2 * wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        2 * wuBoxPhi N δ (convolutionWuWindows N Δ V) t -
        (∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
        (2 / (1 - 2 * δ)) *
          HighSourcePayload.theta N δ Δ V (fun d => omega3XIntegral s t (omega3XPhi N d δ)) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := node_integral m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := roughBox_first_integral m hη hδ hδhi (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb f hf hfb hn s t hs hst ht ht5
  have ha := h0 N (by omega) heven i Δ V hb f hf hfb hn s t hs hst ht ht5
  have hb := h1 N (by omega) heven i Δ V hb s t hs hst (by linarith)
  linarith only [ha,hb]

end Wu18938Campaign.M1.Confirmed.Rebox
