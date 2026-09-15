import MathlibNt.Wu2008DoubleSieve.OmegaWeighted
import MathlibNt.Wu2008DoubleSieve.ReboxingRawTransport

/-!
# Payment of the actual repeated-d lane in the first weighted comparison

Positive-multiple counting is independent of the sifting cutoff. We retain
the reciprocal box mass in the error and the original Theta lower bound.
Thus the same threshold works for every legal box and both parameters.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.SingularSeries

theorem omega_repeated_fibre_le {N d M : ℕ} {η z w v : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (hdN : d ≤ N)
    (hη : 0 < η) (hz : (N : ℝ) ^ η ≤ z) :
    (∑ p ∈ (primeWindow N z w).filter (fun p => p ∣ d),
      (sourceSieveCount N (d * p) M v : ℝ)) ≤
        (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) * (1 / η) := by
  let P := (primeWindow N z w).filter (fun p => p ∣ d)
  have hY : 0 < (N : ℝ) ^ η :=
    rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsub : P ⊆ largePrimeDivisors d ((N : ℝ) ^ η) := by
    intro p hp
    obtain ⟨hp, hpd⟩ := mem_filter.mp hp
    have hwin := mem_primeWindow.mp hp
    exact mem_largePrimeDivisors.mpr
      ⟨hwin.1, hpd, hd.ne', hz.trans hwin.2.2.1⟩
  have hcard : (P.card : ℝ) ≤ 1 / η := by
    have hc : (P.card : ℝ) ≤ (largePrimeDivisors d ((N : ℝ) ^ η)).card := by
      exact_mod_cast card_le_card hsub
    exact hc.trans
      (largePrimeDivisors_card_le_inv (show 1 < N by omega) hd hdN hη)
  calc
    _ ≤ ∑ _p ∈ P, (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
      apply sum_le_sum
      intro p hp
      have hwin := mem_primeWindow.mp (mem_filter.mp hp).1
      have hc : (sourceSieveCount N (d * p) M v : ℝ) ≤ (N / (d * p) : ℕ) := by
        have hi := s3_source_count_le_positive_multiples hN he (d * p) M v
        unfold sourceSieveCount at hi ⊢
        push_cast
        exact_mod_cast hi
      refine hc.trans (Nat.cast_div_le.trans ?_)
      rw [Nat.cast_mul]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos hd0 hY)
        (mul_le_mul_of_nonneg_left (hz.trans hwin.2.2.1) hd0.le)
    _ = (P.card : ℝ) * ((N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η)) := by simp
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard
        (by positivity : 0 ≤ (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η))

theorem wuOmegaRepeatedSum_le_mass {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N) (he : Even N)
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    let W := convolutionWuWindows N Δ V
    let η := wuLocalExponent k δ / 10
    0 ≤ wuOmegaRepeatedSum N δ s t W ∧
      wuOmegaRepeatedSum N δ s t W ≤
        ((N : ℝ) / (η * (N : ℝ) ^ η)) * boxConvolutionReciprocalMass W := by
  dsimp only
  constructor
  · unfold wuOmegaRepeatedSum wuOmegaRepeated
    exact sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _)
      (sum_nonneg (fun p _ => by unfold sourceSieveCount; positivity)))
  · unfold wuOmegaRepeatedSum boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd' := wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
      hδ hδhi hb hs hst ht hd
    have hη : 0 < wuLocalExponent k δ / 10 :=
      div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
    have hf := omega_repeated_fibre_le (M := d * N)
      (v := wuLocalCutoff N δ d t) (w := wuLocalCutoff N δ d s)
      hN he hd'.1 hd'.2.1 hη hd'.2.2.2.1
    have hm := mul_le_mul_of_nonneg_left hf
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
    unfold wuOmegaRepeated
    convert hm using 1
    all_goals ring

/-- Epsilon precedes the common threshold, every legal box, and both parameters.
The original Theta, rather than a rescaled surrogate, pays the raw count. -/
theorem wu_omega_repeated_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        0 ≤ wuOmegaRepeatedSum N δ s t W ∧
          wuOmegaRepeatedSum N δ s t W ≤
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  have hδhalf : δ < 1 / 2 := by linarith
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhalf) (by norm_num)
  have hU := liuUniversalProduct_pos
  have hbudget := box_eventually_log_power_budget 2
    (show 0 < 1 / (2 * ε * liuUniversalProduct * η) by positivity) hη
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (4 : ℕ), hbudget] with N hN hpay
  intro he i Δ V hb s t hs hst ht
  dsimp only
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos hNr
  have hQN : Q ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNr.le
      (show 1 / 2 - δ ≤ 1 by linarith)
  have hsupport : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ 1 < Q / d ∧ Q / d ≤ N := by
    intro d hd
    have hd' := wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
      hδ hδhalf hb hs hst ht hd
    refine ⟨hd'.1, hd'.2.2.1, ?_⟩
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd'.1
    exact (div_le_self (rpow_nonneg (Nat.cast_nonneg N) _) hd1).trans hQN
  have hθ := boxTheta_lower_of_support W hN
    (fun d hd => (hsupport d hd).1) (fun d hd => (hsupport d hd).2)
  have hf := wuOmegaRepeatedSum_le_mass hN he hδ hδhalf hb hs hst ht
  refine ⟨hf.1, hf.2.trans ?_⟩
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d))
  have hcoef : (N : ℝ) / (η * (N : ℝ) ^ η) ≤
      ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) := by
    calc
      _ ≤ (N : ℝ) /
          (η * ((1 / (2 * ε * liuUniversalProduct * η)) * log (N : ℝ) ^ 2)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
          (mul_le_mul_of_nonneg_left hpay hη.le)
      _ = _ := by field_simp
  calc
    _ ≤ (ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2)) *
        boxConvolutionReciprocalMass W := mul_le_mul_of_nonneg_right hcoef hmass
    _ = ε * ((2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) *
        boxConvolutionReciprocalMass W) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hθ hε.le

/-- The actual first weighted comparison, uniformly paid on all source boxes.
No assertion about switching or bounding Omega3 is made. -/
theorem wu_omega_weighted_source (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        2 * wuBoxPhi N δ W s ≤
          wuOmega1Sum N δ t W - wuOmega2Sum N δ s t W +
            wuOmega3Sum N δ s t W +
              ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  obtain ⟨T, hT⟩ := wu_omega_repeated_relative k hδ hδhi hε
  refine ⟨max 4 T, ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  dsimp only
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have herr := (hT N ((le_max_right _ _).trans (hN0.trans hN)) he i Δ V hb s t hs hst ht).2
  have hw := wu_omega_weighted_box (convolutionWuWindows N Δ V) (s := s) (t := t)
    (δ := δ) (N := N) (by
      intro d hd
      have hd' := wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
        hδ (show δ < 1 / 2 by linarith) hb hs hst ht hd
      exact rpow_le_rpow_of_exponent_le hd'.2.2.1.le
        (one_div_le_one_div_of_le (by linarith : 0 < s) hst))
  exact hw.trans (add_le_add_right herr _)

end Wu2008DoubleSieve
