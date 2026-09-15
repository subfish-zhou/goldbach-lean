import MathlibNt.Wu2008DoubleSieve.ReboxingRepeatedPrimes
import MathlibNt.Wu2008DoubleSieve.PhiBuchstab

/-!
# Prime-modulus transport on the actual Buchstab window

The arithmetic reboxing windows use P(N), whereas the exact Buchstab
identity uses P(dN). Their difference is precisely the repeated-prime
lane. This module pays that lane with the actual moving cutoffs.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem primeWindow_mul_eq_filter (N d : ℕ) (z w : ℝ) :
    primeWindow (d * N) z w = (primeWindow N z w).filter (fun p => ¬p ∣ d) := by
  ext p
  simp only [mem_filter, mem_primeWindow, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨hp, ⟨hpd, hpN⟩, hz, hw⟩
    exact ⟨⟨hp, hpN, hz, hw⟩, hp.coprime_iff_not_dvd.mp hpd⟩
  · rintro ⟨⟨hp, hpN, hz, hw⟩, hpd⟩
    exact ⟨hp, ⟨hp.coprime_iff_not_dvd.mpr hpd, hpN⟩, hz, hw⟩

theorem primeWindow_modulus_sum_difference (N d : ℕ) (z w : ℝ) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N z w, f p) - (∑ p ∈ primeWindow (d * N) z w, f p) =
      ∑ p ∈ (primeWindow N z w).filter (fun p => p ∣ d), f p := by
  rw [primeWindow_mul_eq_filter]
  have h := sum_filter_add_sum_filter_not (primeWindow N z w) (fun p => p ∣ d) f
  linarith

/-- Uniform finite transport for bounded signed coefficients. The bound
is derived from the actual prime sum, not assumed as an error budget. -/
theorem reboxing_prime_transport_abs_le {N d : ℕ} {q η B z w : ℝ} {g : ℕ → ℝ}
    (hN : 1 < N) (hd : 0 < d) (hdN : d ≤ N) (hη : 0 < η)
    (hlarge : 4 ≤ (N : ℝ) ^ η) (hq : 1 < q) (hB : 0 ≤ B)
    (hz : (N : ℝ) ^ η ≤ z) (hw : w ≤ q ^ (1 / 2 : ℝ))
    (hg : ∀ p ∈ primeWindow N z w, |g p| ≤ B) :
    |(∑ p ∈ primeWindow N z w,
        g p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q))) -
      (∑ p ∈ primeWindow (d * N) z w,
        g p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q)))| ≤
      B * (4 / (η * (N : ℝ) ^ η)) := by
  let P := (primeWindow N z w).filter (fun p => p ∣ d)
  let T := (primeWindow N ((N : ℝ) ^ η) (q ^ (1 / 2 : ℝ))).filter (fun p => p ∣ d)
  have hsub : P ⊆ T := by
    intro p hp
    obtain ⟨hp, hpd⟩ := mem_filter.mp hp
    obtain ⟨hpp, hcop, hlow, hhigh⟩ := mem_primeWindow.mp hp
    exact mem_filter.mpr ⟨mem_primeWindow.mpr ⟨hpp, hcop, hz.trans hlow, hhigh.trans_le hw⟩, hpd⟩
  have hnon : ∀ p ∈ T,
      0 ≤ 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q)) := by
    intro p hp
    have hp' := mem_primeWindow.mp (mem_filter.mp hp).1
    exact (reboxing_prime_weight_le_four_div hq (hlarge.trans hp'.2.2.1) hp'.2.2.2.le).1
  rw [primeWindow_modulus_sum_difference]
  calc
    _ ≤ ∑ p ∈ P, |g p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, B * (1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q))) := by
      apply sum_le_sum
      intro p hp
      have hi : 0 ≤ (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q))⁻¹ := by
        simpa only [one_div] using hnon p (hsub hp)
      rw [div_eq_mul_inv, abs_mul, abs_of_nonneg hi]
      simpa only [one_div] using
        mul_le_mul_of_nonneg_right (hg p (mem_filter.mp hp).1) (hnon p (hsub hp))
    _ = B * ∑ p ∈ P, 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q)) :=
      (mul_sum _ _ _).symm
    _ ≤ B * ∑ p ∈ T, 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log q)) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnon p hp)) hB
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reboxing_repeated_prime_sum_le hN hd hdN hη hlarge hq) hB

/-- The actual moving Buchstab interval is in the paid polynomial-height
lane; no selected prime is substituted for an upper box endpoint. -/
theorem wu_buchstab_prime_window_bounds {i k N d : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ d ≤ N ∧ 1 < (N : ℝ) ^ (1 / 2 - δ) / d ∧
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ wuLocalCutoff N δ d t ∧
      wuLocalCutoff N δ d s ≤ (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / 2 : ℝ)) := by
  have hsp := wuLocal_support_bounds (show 1 ≤ N by omega) hδ hδhi
    hb.2.2.2.2.1 ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
  have hq : 1 < (N : ℝ) ^ (1 / 2 - δ) / d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega))
      (wuLocalExponent_pos k hδ hδhi)).trans_le hsp.2.2
  refine ⟨hsp.1, hsp.2.1, hq,
    wuLocalCutoff_lower (show 1 ≤ N by omega) hδ hδhi (by linarith) ht hsp.2.2, ?_⟩
  exact rpow_le_rpow_of_exponent_le hq.le
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)

/-- Every actual prime-sum coefficient is evaluated inside the proved
source domain. This also covers equal outer parameters, whose window
is empty, without assigning a spurious endpoint prime. -/
theorem wu_buchstab_prime_parameter_mem {i k N d p : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) :
    1 ≤ log (((N : ℝ) ^ (1 / 2 - δ) / d) / p) / log p ∧
      log (((N : ℝ) ^ (1 / 2 - δ) / d) / p) / log p ≤ 10 := by
  have hb' := wu_buchstab_prime_window_bounds hN hδ hδhi hb hs hst ht hd
  have hp' := mem_primeWindow.mp hp
  have hpr : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
  have hshift := buchstab_shifted_parameter hb'.2.2.1 hpr
    (show 0 < s by linarith) (show 0 < t by linarith) hp'.2.2.1 hp'.2.2.2
  constructor <;> linarith [hshift.1, hshift.2]

noncomputable def reboxingPrimeSum {i : ℕ} (selected : Bool) (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (g : ℕ → ℕ → ℝ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport W,
      ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow (if selected then d * N else N)
          (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        g d p / (((p : ℝ) - 2) *
          (1 - log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)))

/-- Summed transport preserves the exact C(dN)/phi(d) and li_2 normalizer,
and the full signed coefficient. The one constant is uniform in g. -/
theorem reboxingPrimeSum_transport_bound {i k N : ℕ} {δ Δ s t B : ℝ}
    {V : Fin i → ℝ} {g : ℕ → ℕ → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hB : 0 ≤ B) (hlarge : 4 ≤ (N : ℝ) ^ (wuLocalExponent k δ / 10))
    (hg : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), |g d p| ≤ B) :
    |reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V) g -
        reboxingPrimeSum true N δ s t (convolutionWuWindows N Δ V) g| ≤
      (B * (4 / ((wuLocalExponent k δ / 10) *
        (N : ℝ) ^ (wuLocalExponent k δ / 10)))) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let η := wuLocalExponent k δ / 10
  let c := B * (4 / (η * (N : ℝ) ^ η))
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans (box_trueLi_lower hN)
  have hf := fun d hd => wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
    hδ hδhi hb hs hst ht (d := d) hd
  have hw : ∀ d ∈ boxConvolutionSupport W,
      0 ≤ (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log (Q / d)) := by
    intro d hd
    have hd' := hf d hd
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos hd'.1 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hd'.2.2.1).le)
  unfold reboxingPrimeSum
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hli0)]
  unfold boxTheta
  rw [mul_left_comm c]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hli0)
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W,
        |((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
          ((Nat.totient d : ℝ) * log (Q / d))) *
          ((∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
              g d p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))) -
            (∑ p ∈ primeWindow (d * N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
              g d p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))))| := by
      simpa only [mul_sub] using
        (abs_sum_le_sum_abs
          (fun d => ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
            ((Nat.totient d : ℝ) * log (Q / d))) *
            ((∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
                g d p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))) -
              (∑ p ∈ primeWindow (d * N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
                g d p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d))))))
          (boxConvolutionSupport W))
    _ ≤ ∑ d ∈ boxConvolutionSupport W,
        ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
          ((Nat.totient d : ℝ) * log (Q / d))) * c := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul, abs_of_nonneg (hw d hd)]
      have hd' := hf d hd
      apply mul_le_mul_of_nonneg_left _ (hw d hd)
      exact reboxing_prime_transport_abs_le (show 1 < N by omega)
        hd'.1 hd'.2.1 hη hlarge hd'.2.2.1 hB hd'.2.2.2.1 hd'.2.2.2.2 (hg d hd)
    _ = _ := by rw [← sum_mul, mul_comm]

end Wu2008DoubleSieve
