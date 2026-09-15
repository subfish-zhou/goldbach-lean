import Wu18938Campaign.M1.Confirmed.UnitDensity
import Wu18938Campaign.M1.Confirmed.SourceGeometry

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighUnit Finset Real Filter
open scoped Classical Topology

theorem roughBox_boxed_unit_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ a2 a3 b : ℕ → ℝ,
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        1 / 10 ≤ a2 d ∧ 1 / 10 ≤ a3 d ∧ b d ≤ 1 / 2) →
      let W := convolutionWuWindows N Δ V
      |boxedSigma20 N δ W a2 a3 b + boxedSigma21 N δ W a3 b -
        (boxedIntegral20 N δ W a2 a3 b + boxedIntegral21 N δ W a3 b)| ≤
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨R0, _, hphysical⟩ := physical_pair_uniform (ε / 2 * η) (by positivity)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb a2 a3 b hw W
  have hN2 : 2 ≤ N := by omega
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      (|boxed20 N d δ (a2 d) (a3 d) (b d) -
        (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
          J20 (a2 d) (a3 d) (b d) (omega3XPhi N d δ)| ≤
        (ε / 2) * ((N : ℝ) / log N) / d) ∧
      (|boxed21 N d δ (a3 d) (b d) -
        (N : ℝ) / ((d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
          J21 (a3 d) (b d) (omega3XPhi N d δ)| ≤
        (ε / 2) * ((N : ℝ) / log N) / d) := by
    have hg := hb.support_geometry hN2 hη hδ hd
    have hscale := boxed_scale_identity (by omega : 0 < N) hg.1 hg.2.2.1
    have hlarge := (hT N (by omega)).trans (hb.remaining d hd)
    obtain ⟨ha2, ha3, hbs⟩ := hw d hd
    have hh := hphysical _ hlarge (a2 d) (a3 d) (b d) (omega3XPhi N d δ) ha2 ha3 hbs
    simp only [hscale] at hh
    have h20 : |log ((N : ℝ) ^ (1 / 2 - δ) / d) / ((N : ℝ) / d) *
        boxed20 N d δ (a2 d) (a3 d) (b d) - J20 (a2 d) (a3 d) (b d) (omega3XPhi N d δ)| <
        ε / 2 * η := hh.1
    have h21 : |log ((N : ℝ) ^ (1 / 2 - δ) / d) / ((N : ℝ) / d) *
        boxed21 N d δ (a3 d) (b d) - J21 (a3 d) (b d) (omega3XPhi N d δ)| <
        ε / 2 * η := hh.2
    have hpay := roughBox_log_scale hb hN2 hη hδ hd (half_pos he).le
    exact ⟨(unnormalize (by omega) hg.1 hg.2.2.1 h20).le.trans hpay,
      (unnormalize (by omega) hg.1 hg.2.2.1 h21).le.trans hpay⟩
  have h20 := sigma_abs_error W _ _ (fun d hd => (hpoint d hd).1)
  have h21 := sigma_abs_error W _ _ (fun d hd => (hpoint d hd).2)
  change |boxedSigma20 N δ W a2 a3 b - boxedIntegral20 N δ W a2 a3 b| ≤ _ at h20
  change |boxedSigma21 N δ W a3 b - boxedIntegral21 N δ W a3 b| ≤ _ at h21
  have ht := abs_add_le
    (boxedSigma20 N δ W a2 a3 b - boxedIntegral20 N δ W a2 a3 b)
    (boxedSigma21 N δ W a3 b - boxedIntegral21 N δ W a3 b)
  rw [show ∀ x y z w : ℝ, x - y + (z - w) = x + z - (y + w) by intros; ring] at ht
  linarith only [ht, h20, h21]

end Wu18938Campaign.M1.Confirmed
