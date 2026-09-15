import MathlibNt.Wu2008DoubleSieve.Omega3SourceBounds

/-!
# The same reciprocal mass with the full singular series retained

Wu04, TeX2255, uses C(N) <= C(d*N). This comparison needs no coprimality
between d and N, and no uniform upper bound for C(N).
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical
open MathlibNt.SieveTheory.SingularSeries
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem wuSingularSeries_le_of_dvd {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    wuSingularSeries m ≤ wuSingularSeries n := by
  rw [wuSingularSeries, wuSingularSeries,
    oddPrimeDivisors_eq m hm, oddPrimeDivisors_eq n hn, wu_universal_product_eq_liu]
  apply mul_le_mul_of_nonneg_left _ liuUniversalProduct_pos.le
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hp, hp2⟩ := mem_filter.mp hp
    obtain ⟨hpp, hpm, _⟩ := Nat.mem_primeFactors.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpm.trans hmn, hn.ne'⟩, hp2⟩
  · intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact div_nonneg (by linarith) (by linarith)
  · intro p hp _
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 2)).mpr
    linarith

theorem wuSingularSeries_le_mul {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    wuSingularSeries N ≤ wuSingularSeries (d * N) :=
  wuSingularSeries_le_of_dvd hN (Nat.mul_pos hd hN) (dvd_mul_left N d)

/-- The finite comparison keeps C(N) and exactly sum_d sigma(d)/d. -/
theorem boxTheta_lower_singular_of_support {i N : ℕ} {Q : ℝ}
    (W : Fin i → Finset ℕ) (hN : 4 ≤ N)
    (hpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 < Q / d ∧ Q / d ≤ N) :
    2 * wuSingularSeries N * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass W ≤ boxTheta N Q W := by
  have hN0 : 0 < N := by omega
  have hC0 := wuSingularSeries_pos N hN0
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hli := box_trueLi_lower hN
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans hli
  have hsum :
      wuSingularSeries N / log N * boxConvolutionReciprocalMass W ≤
        ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
            ((Nat.totient d : ℝ) * log (Q / d)) := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 := hpos d hd
    have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
    have ht0 : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have ht : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hu0 : 0 < log (Q / d) := log_pos (hQ d hd).1
    have hu : log (Q / d) ≤ log N :=
      log_le_log (by linarith [(hQ d hd).1]) (hQ d hd).2
    have hC := wuSingularSeries_le_mul hN0 hd0
    have hCd0 : 0 < wuSingularSeries (d * N) := hC0.trans_le hC
    calc
      _ = (convolutionCoeff W d : ℝ) * wuSingularSeries N /
          ((d : ℝ) * log N) := by ring
      _ ≤ _ := by gcongr
  calc
    _ = 4 * ((N : ℝ) / (2 * log N)) *
        (wuSingularSeries N / log N * boxConvolutionReciprocalMass W) := by ring
    _ ≤ 4 * logarithmicIntegral N *
        (wuSingularSeries N / log N * boxConvolutionReciprocalMass W) := by gcongr
    _ ≤ boxTheta N Q W :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hli0)

theorem omega3_source_theta_lower_singular {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    2 * wuSingularSeries N * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  apply boxTheta_lower_singular_of_support _ hN
  · intro d hd
    exact (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1
  · intro d hd
    have h := wu_buchstab_prime_window_bounds (s := 2) (t := 2)
      (show 2 ≤ N by omega) hδ hδhi hb le_rfl le_rfl (by norm_num) hd
    refine ⟨h.2.2.1, ?_⟩
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.1
    exact (div_le_self (rpow_nonneg (Nat.cast_nonneg N) _) hd1).trans
      (by
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ N by omega)) (show 1 / 2 - δ ≤ 1 by linarith))

end Wu2008DoubleSieve
