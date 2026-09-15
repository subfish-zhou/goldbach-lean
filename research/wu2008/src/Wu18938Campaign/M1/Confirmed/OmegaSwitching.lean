import Wu18938Campaign.M1.Confirmed.OmegaGeometry
import MathlibNt.Wu2008DoubleSieve.Omega3Relative

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Omega

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem badD_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3BadDCount N δ s t (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := roughBox_power_mass_relative m hη hδ he
    (show 0 < (1 / (η / 10)) ^ 4 by positivity) (show 0 < η / 10 by positivity)
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hf := omega3_badDCount_le_reciprocal_mass (s := s) (convolutionWuWindows N Δ V)
    (by omega) heven (show 0 < η / 10 by positivity) (by
      intro d hd
      have hg := hb.support_geometry (by omega) hη hδ hd
      exact ⟨hg.1,hg.2.1⟩)
    (fun d hd => roughBox_cutoff_lower hb (by omega) hη hδ hd (by linarith) ht) (by
      intro d hd q hq
      have hqp := Nat.mem_primeFactors.mp hq
      have hl := omega3_support_prime_lower _ hb.window_large hd hqp.1 hqp.2.1
      exact (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
        (by linarith : η / 10 ≤ η)).trans hl)
  exact hf.trans (hT N hN i Δ V hb)

theorem exceptional_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3ExceptionalOutputCount N δ s t (convolutionWuWindows N Δ V) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let C : ℝ := (1 / (η / 10)) ^ 3
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T,hT4,hT⟩ := roughBox_power_mass_relative m hη hδ he
    (show 0 < 4 * C by positivity) hδ
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  let W := convolutionWuWindows N Δ V
  have hf := omega3_exceptional_count_le (s := s) W (by omega) heven
    (show 0 < η / 10 by positivity)
    (fun d hd => roughBox_cutoff_lower hb (by omega) hη hδ hd (by linarith) ht)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ)) ≤
      (N : ℝ) ^ (1 / 2 - δ) * boxConvolutionReciprocalMass W := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hb.support_pos hd
    have hdQ : (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) := by
      have hh := (lt_div_iff₀ hd0).mp (hb.support_geometry (by omega) hη hδ hd).2.2.1
      simpa only [one_mul] using hh.le
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hd0).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdQ
      (Nat.cast_nonneg (convolutionCoeff W d))
  have hpow : sqrt (N : ℝ) * (N : ℝ) ^ (1 / 2 - δ) = (N : ℝ) / (N : ℝ) ^ δ := by
    rw [sqrt_eq_rpow,← rpow_add hNr,show (1 / 2 : ℝ) + (1 / 2 - δ) = 1 - δ by ring,
      rpow_sub hNr,rpow_one]
  have hbnd : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      (C * ((omega3ExceptionalOutputs N δ).card : ℝ))) ≤
      (4 * C * ((N : ℝ) / (N : ℝ) ^ δ)) * boxConvolutionReciprocalMass W := by
    calc
      _ = (C * ((omega3ExceptionalOutputs N δ).card : ℝ)) *
          ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) := by
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ => by ring)
      _ ≤ (C * (4 * sqrt (N : ℝ))) *
          ((N : ℝ) ^ (1 / 2 - δ) * boxConvolutionReciprocalMass W) :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (omega3ExceptionalOutputs_card_le (by omega) hδ.le) hC.le) hmass
          (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
      _ = _ := by rw [← hpow]; ring
  exact hf.trans (hbnd.trans (hT N hN i Δ V hb))

theorem source_switching (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      wuOmega3Sum N δ s t (convolutionWuWindows N Δ V) ≤
        omega3SwitchedSiftedCount N δ s t (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
          (convolutionWuWindows N Δ V) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := badD_relative m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := exceptional_relative m hη hδ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hf := wuOmega3Sum_le_switched_add_badD_add_exceptional (δ := δ) (s := s) (t := t)
    (W := convolutionWuWindows N Δ V) (by omega) heven (fun _ hd => hb.support_pos hd)
  have hbad := h0 N (by omega) heven i Δ V hb s t hs hst ht
  have hexc := h1 N (by omega) heven i Δ V hb s t hs hst ht
  linarith only [hf,hbad,hexc]

end Wu18938Campaign.M1.Confirmed.Omega
