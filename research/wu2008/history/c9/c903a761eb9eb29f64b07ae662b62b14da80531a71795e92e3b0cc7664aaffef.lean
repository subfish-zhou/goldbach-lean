import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeTransport
import MathlibNt.Wu2008DoubleSieve.S3FourPrimeCompletion

/-!
# Repeated-prime payment for the raw Buchstab sieve sum

In the reverse comparison, changing P(dN) to P(N) adds actual sieve
counts, not only local main terms. Positive-multiple counting pays this
whole lane; the reciprocal source mass is retained in both sides.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries

theorem reboxing_raw_repeated_fibre_le {N d : ℕ} {η z w : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (hdN : d ≤ N)
    (hη : 0 < η) (hz : (N : ℝ) ^ η ≤ z) :
    (∑ p ∈ (primeWindow N z w).filter (fun p => p ∣ d),
      (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ)) ≤
        (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) * (1 / η) := by
  let P := (primeWindow N z w).filter (fun p => p ∣ d)
  have hY : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsub : P ⊆ largePrimeDivisors d ((N : ℝ) ^ η) := by
    intro p hp
    obtain ⟨hp, hpd⟩ := mem_filter.mp hp
    have hwin := mem_primeWindow.mp hp
    exact mem_largePrimeDivisors.mpr ⟨hwin.1, hpd, hd.ne', hz.trans hwin.2.2.1⟩
  have hcard : (P.card : ℝ) ≤ 1 / η := by
    have hc : (P.card : ℝ) ≤ (largePrimeDivisors d ((N : ℝ) ^ η)).card := by
      exact_mod_cast card_le_card hsub
    exact hc.trans (largePrimeDivisors_card_le_inv (show 1 < N by omega) hd hdN hη)
  calc
    _ ≤ ∑ _p ∈ P, (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
      apply sum_le_sum
      intro p hp
      have hwin := mem_primeWindow.mp (mem_filter.mp hp).1
      have hc : (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ) ≤ (N / (d * p) : ℕ) := by
        have hi := s3_source_count_le_positive_multiples hN he (d * p) ((d * p) * N) p
        unfold sourceSieveCount at hi ⊢
        push_cast
        exact_mod_cast hi
      refine hc.trans (Nat.cast_div_le.trans ?_)
      rw [Nat.cast_mul]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos hd0 hY)
        (mul_le_mul_of_nonneg_left (hz.trans hwin.2.2.1) hd0.le)
    _ = (P.card : ℝ) * ((N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η)) := by simp
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard (by positivity :
        0 ≤ (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η))

noncomputable def reboxingRawPrimeSum {i : ℕ} (selected : Bool) (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ primeWindow (if selected then d * N else N)
        (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ)

theorem reboxingRawPrimeSum_difference_le_mass {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N) (he : Even N)
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    let W := convolutionWuWindows N Δ V
    let η := wuLocalExponent k δ / 10
    0 ≤ reboxingRawPrimeSum false N δ s t W - reboxingRawPrimeSum true N δ s t W ∧
      reboxingRawPrimeSum false N δ s t W - reboxingRawPrimeSum true N δ s t W ≤
        ((N : ℝ) / (η * (N : ℝ) ^ η)) * boxConvolutionReciprocalMass W := by
  dsimp only
  unfold reboxingRawPrimeSum
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub, primeWindow_modulus_sum_difference]
  constructor
  · exact sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _)
      (sum_nonneg (fun p _ => by unfold sourceSieveCount; positivity)))
  · unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd' := wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
      hδ hδhi hb hs hst ht hd
    have hη : 0 < wuLocalExponent k δ / 10 :=
      div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
    have hf := reboxing_raw_repeated_fibre_le (w := wuLocalCutoff N δ d s)
      hN he hd'.1 hd'.2.1 hη hd'.2.2.2.1
    have hm := mul_le_mul_of_nonneg_left hf
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d) : (0 : ℝ) ≤ _)
    convert hm using 1
    ring

/-- The actual raw P(N)/P(dN) correction is uniformly negligible.
The same reciprocal mass occurs on both sides; no depth-dependent
log-power mass estimate is substituted. -/
theorem wu_raw_prime_transport_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        0 ≤ reboxingRawPrimeSum false N δ s t W - reboxingRawPrimeSum true N δ s t W ∧
          reboxingRawPrimeSum false N δ s t W - reboxingRawPrimeSum true N δ s t W ≤
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
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
      hδ hδhi hb hs hst ht hd
    refine ⟨hd'.1, hd'.2.2.1, ?_⟩
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd'.1
    exact (div_le_self (rpow_nonneg (Nat.cast_nonneg N) _) hd1).trans hQN
  have hθ := boxTheta_lower_of_support W hN
    (fun d hd => (hsupport d hd).1) (fun d hd => (hsupport d hd).2)
  have hf := reboxingRawPrimeSum_difference_le_mass hN he hδ hδhi hb hs hst ht
  refine ⟨hf.1, hf.2.trans ?_⟩
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d))
  have hcoef : (N : ℝ) / (η * (N : ℝ) ^ η) ≤
      ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) := by
    calc
      _ ≤ (N : ℝ) / (η * ((1 / (2 * ε * liuUniversalProduct * η)) * log (N : ℝ) ^ 2)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
          (mul_le_mul_of_nonneg_left hpay hη.le)
      _ = _ := by field_simp
  calc
    _ ≤ (ε * (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2)) *
        boxConvolutionReciprocalMass W := mul_le_mul_of_nonneg_right hcoef hmass
    _ = ε * ((2 * liuUniversalProduct * (N : ℝ) / log N ^ 2) *
        boxConvolutionReciprocalMass W) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hθ hε.le

end Wu2008DoubleSieve
