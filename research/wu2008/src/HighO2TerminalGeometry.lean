import HighOmega2Finite
import MathlibNt.Wu2008DoubleSieve.Omega2PrimeIntegral

namespace HighO2Terminal
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2
open scoped Classical
noncomputable section

/-- Exact local fixed-cutoff ratio. No cell endpoint or shifted kernel. -/
def ratio (N d p : ℕ) (δ t : ℝ) : ℝ :=
  t * (1 - log (p : ℝ) / log ((N : ℝ)^(1/2-δ)/d))

/-- The original two endpoints give a stronger gap than the generic
high-box API. This applies to all actual supported d, not a prefix square. -/
theorem original_support {N d : ℕ} {δ Δ : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hΔ : 0 < Δ)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hr : OriginalRectangles N V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ d ≤ N ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-100*highEta) ∧
      (N : ℝ)^(10*highEta) ≤ (N : ℝ)^(1/2-δ)/d ∧
      1 < (N : ℝ)^(1/2-δ)/d := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have he : 0 < highEta := by norm_num [highEta]
  have hVp : ∀ j, 0 < V j := fun j => (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hV j)
  have hb := reboxing_support_product_bounds hΔ (fun j => (hVp j).le) hd
  have hsize := hb.2.2.trans (original_rectangles_product hN (fun j => (hVp j).le) hr)
  have hlevel := (original_base_gap hN hδ hδhi hV hr).1.trans
    (reboxing_support_level_bounds (rpow_nonneg (Nat.cast_nonneg N) _) hΔ hVp hd).1
  refine ⟨hb.1,?_,hsize,hlevel,?_⟩
  · exact_mod_cast hsize.trans (show (N : ℝ)^(1/2-100*highEta) ≤ N by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNr.le (show 1/2-100*highEta ≤ (1 : ℝ) by linarith))
  · exact (one_lt_rpow hNr (by positivity : 0 < 10*highEta)).trans_le hlevel

/-- Every prime of the full literal Omega2 interval has sufficient dp slack,
including repeats. Endpoints are exactly the original half-open interval. -/
theorem full_prime_geometry {N d p : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hΔ : 0 < Δ)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hr : OriginalRectangles N V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hp : p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) :
    (N : ℝ)^highEta ≤ p ∧ (p : ℝ) ≤ N ∧
      ((d*p : ℕ) : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
  have hh := original_support hN hδ hδhi hΔ hV hr hd
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := by linarith
  have he : 0 < highEta := by norm_num [highEta]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hh.1
  have hq0 : 0 < (N : ℝ)^(1/2-δ)/d := by linarith [hh.2.2.2.2]
  have hp' := mem_primeWindow.mp hp
  have hhalf : (p : ℝ) ≤ ((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ) :=
    hp'.2.2.2.le.trans (rpow_le_rpow_of_exponent_le hh.2.2.2.2.le
      (one_div_le_one_div_of_le (by norm_num) hs))
  have hdp : ((d*p : ℕ) : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
    have hpow : (N : ℝ)^(1/2-δ)*d ≤ ((N : ℝ)^(1/2-δ-10*highEta))^2 := by
      calc
        _ ≤ (N : ℝ)^(1/2-δ)*(N : ℝ)^(1/2-100*highEta) :=
          mul_le_mul_of_nonneg_left hh.2.2.1 (by positivity)
        _ = (N : ℝ)^((1/2-δ)+(1/2-100*highEta)) := (rpow_add hNp _ _).symm
        _ ≤ (N : ℝ)^((1/2-δ-10*highEta)*2) :=
          rpow_le_rpow_of_exponent_le hNr.le (by linarith)
        _ = _ := by rw [rpow_mul (Nat.cast_nonneg N),rpow_two]
    have hsquare : (p : ℝ)^2 ≤ (N : ℝ)^(1/2-δ)/d := by
      have hpnon : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have hsq := pow_le_pow_left₀ hpnon hhalf 2
      have heq : (((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ))^2 = (N : ℝ)^(1/2-δ)/d := by
        rw [← rpow_two,← rpow_mul hq0.le]
        norm_num
      rwa [heq] at hsq
    have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hd0).mp hsquare) hd0.le
    rw [Nat.cast_mul]
    nlinarith [rpow_nonneg (Nat.cast_nonneg N) (1/2-δ-10*highEta)]
  refine ⟨?_,?_,hdp⟩
  · apply le_trans _ hp'.2.2.1
    change (N : ℝ)^highEta ≤ ((N : ℝ)^(1/2-δ)/d)^(1/t)
    calc
      _ ≤ (N : ℝ)^((10*highEta)*(1/t)) := rpow_le_rpow_of_exponent_le hNr.le (by
        rw [mul_one_div]; apply (le_div_iff₀ (show 0 < t by linarith)).mpr; nlinarith)
      _ = ((N : ℝ)^(10*highEta))^(1/t) := rpow_mul (Nat.cast_nonneg N) _ _
      _ ≤ _ := rpow_le_rpow (by positivity) hh.2.2.2.1 (by positivity)
  · have hpdp : (p : ℝ) ≤ d*p := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hh.1
      nlinarith [Nat.cast_nonneg (α := ℝ) p]
    rw [Nat.cast_mul] at hdp
    apply hpdp.trans (hdp.trans ?_)
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNr.le
      (show 1/2-δ-10*highEta ≤ (1 : ℝ) by linarith)

/-- The exact d-dependent parameter lies in the classical lower strip. -/
theorem ratio_domain {N d p : ℕ} {δ s t : ℝ}
    (hq : 1 < (N : ℝ)^(1/2-δ)/d) (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hc : 2 ≤ t-t/s)
    (hp : p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) :
    2 ≤ ratio N d p δ t ∧ ratio N d p δ t ≤ 4 := by
  have h := omega2_fixed_cutoff_domain hq hs ht hc
    (mem_primeWindow.mp hp).2.2.1 (mem_primeWindow.mp hp).2.2.2.le
  exact ⟨h.1,h.2.trans (by linarith)⟩

/-- Exact cutoff equality removes the kernel displacement altogether. -/
theorem ratio_cutoff {N d p : ℕ} {δ t : ℝ}
    (hq : 1 < (N : ℝ)^(1/2-δ)/d) (hp : 0 < p) (ht : 0 < t)
    (hu : 0 < ratio N d p δ t) :
    wuLocalCutoff N δ (d*p) (ratio N d p δ t) = wuLocalCutoff N δ d t := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : 0 < (N : ℝ)^(1/2-δ)/d := by linarith
  have h := omega2_fixed_cutoff_ratio hq hp0 ht
  have hz : 0 < log (((N : ℝ)^(1/2-δ)/d)^(1/t)) :=
    log_pos (one_lt_rpow hq (by positivity))
  unfold wuLocalCutoff
  rw [Nat.cast_mul,← div_div]
  apply (log_injOn_pos (rpow_pos_of_pos (div_pos hq0 hp0) _)
    (rpow_pos_of_pos hq0 _))
  rw [log_rpow (div_pos hq0 hp0),one_div_mul_eq_div]
  apply (div_eq_iff hu.ne').mpr
  have hx := (div_eq_iff hz.ne').mp h
  change _ = _ * ratio N d p δ t
  simpa only [ratio,mul_comm] using hx

end
end HighO2Terminal
