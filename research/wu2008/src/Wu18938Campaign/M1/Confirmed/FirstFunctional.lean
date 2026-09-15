import Wu18938Campaign.M1.Confirmed.OmegaIntegral
import MathlibNt.Wu2008DoubleSieve.OmegaRepeated
import MathlibNt.Wu2008DoubleSieve.Omega1Upper

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem roughBox_first_repeated (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      wuOmegaRepeatedSum N δ s t (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := roughBox_power_mass_relative m hη hδ he
    (show 0 < 1 / (η / 10) by positivity) (show 0 < η / 10 by positivity)
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hfinite : wuOmegaRepeatedSum N δ s t (convolutionWuWindows N Δ V) ≤
      ((1 / (η / 10)) * ((N : ℝ) / (N : ℝ) ^ (η / 10))) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    unfold wuOmegaRepeatedSum boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hg := hb.support_geometry (by omega) hη hδ hd
    have hf := omega_repeated_fibre_le (M := d * N)
      (v := wuLocalCutoff N δ d t) (w := wuLocalCutoff N δ d s)
      (by omega) heven hg.1 hg.2.1 (show 0 < η / 10 by positivity)
      (roughBox_cutoff_lower hb (by omega) hη hδ hd (by linarith) ht)
    have hm := mul_le_mul_of_nonneg_left hf
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
    unfold wuOmegaRepeated
    convert hm using 1
    ring
  exact hfinite.trans (hT N hN i Δ V hb)

theorem roughBox_first_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      2 * wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        2 * wuBoxPhi N δ (convolutionWuWindows N Δ V) t -
        wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) +
        (2 / (1 - 2 * δ)) *
          HighSourcePayload.theta N δ Δ V (fun d => omega3XIntegral s t (omega3XPhi N d δ)) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_first_repeated m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := Omega.source_theta m hη hδ hδhi (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hf := wu_omega_weighted_box (N := N) (convolutionWuWindows N Δ V)
    (fun d hd => hb.cutoff_antitone (by omega) hη hδ hd (by linarith) hst)
  rw [wuOmega1Sum_eq_twice_Phi] at hf
  have hrep := h0 N (by omega) heven i Δ V hb s t hs hst ht
  have hI := h1 N (by omega) heven i Δ V hb s t hs hst ht
  linarith only [hf,hrep,hI]

end Wu18938Campaign.M1.Confirmed
