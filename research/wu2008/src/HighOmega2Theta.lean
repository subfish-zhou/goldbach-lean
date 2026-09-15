import HighOmega2Interior
import MathlibNt.Wu2008DoubleSieve.ReboxingRepeatedPrimes
import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeMass

namespace HighOmega2
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- A union of insertion windows costs a fixed prime-tail constant, not the
number of windows. Repeated p|d uses its exact 1/p local multiplier. -/
theorem inserted_theta_bound {N : ℕ} {Q η : ℝ} {i : ℕ}
    (W : Fin i → Finset ℕ) (P : Finset ℕ)
    (hN : 4 ≤ N) (hη : 0 < η)
    (hlarge : 4 ≤ (N : ℝ)^η)
    (hstart : LiLiuPrereqBuchstab.primeErrorStart ≤ (N : ℝ)^η)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d ∧ 1 < Q/d)
    (hP : ∀ p ∈ P, p.Prime ∧ p.Coprime N ∧ (N : ℝ)^η ≤ p ∧ (p : ℝ) ≤ N)
    (hu : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P, (p : ℝ) ≤ (Q/d)^(1/2 : ℝ)) :
    boxTheta N Q (Fin.cons P W) ≤ (20/η)*boxTheta N Q W := by
  have hli : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N/(2*log N)).trans (box_trueLi_lower hN)
  have hsum : (∑ p ∈ P, 1/(p : ℝ)) ≤ 5/η := by
    apply le_trans _ (omega3X_prime_interval_reciprocal_le (by omega) hη hstart)
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hh := hP p hp
      exact (LiLiuPrereqBuchstab.mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨hh.1,hh.2.2.1,hh.2.2.2⟩
    · intro p _ _
      positivity
  have hpoint : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ P, wuSingularSeries ((d*p)*N)/((Nat.totient (d*p) : ℝ)*log (Q/((d : ℝ)*p)))) ≤
        (20/η)*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d))) := by
    intro d hdm
    let a := wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d))
    have ha : 0 ≤ a := div_nonneg
      (wuSingularSeries_pos _ (Nat.mul_pos (hd d hdm).1 (by omega))).le
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hd d hdm).2).le)
    have hatom : ∀ p ∈ P,
        wuSingularSeries ((d*p)*N)/((Nat.totient (d*p) : ℝ)*log (Q/((d : ℝ)*p))) ≤ a*(4/(p : ℝ)) := by
      intro p hp
      have hh := hP p hp
      have hp4 : (4 : ℝ) ≤ p := hlarge.trans hh.2.2.1
      have hp2 : 2 < p := by exact_mod_cast (show (2 : ℝ) < p by linarith)
      rw [wu_inserted_theta_weight (by omega) (hd d hdm).1 hh.1 hp2 hh.2.1 (hd d hdm).2]
      apply mul_le_mul_of_nonneg_left _ ha
      have hhalf := reboxing_log_ratio_half (hd d hdm).2 (by linarith : (0 : ℝ) < p) (hu d hdm p hp)
      have hmult : (if p ∣ d then 1/(p : ℝ) else 1/((p : ℝ)-2)) ≤ 1/((p : ℝ)-2) := by
        split_ifs
        · exact one_div_le_one_div_of_le (by linarith) (by linarith)
        · exact le_rfl
      calc
        _ ≤ (1/((p : ℝ)-2))/(1-log (p : ℝ)/log (Q/d)) :=
          div_le_div_of_nonneg_right hmult (by linarith)
        _ = 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d))) := div_div _ _ _
        _ ≤ _ := (reboxing_prime_weight_le_four_div (hd d hdm).2 hp4 (hu d hdm p hp)).2
    calc
      _ ≤ ∑ p ∈ P, a*(4/(p : ℝ)) := sum_le_sum hatom
      _ = (4*a)*(∑ p ∈ P, 1/(p : ℝ)) := by rw [mul_sum]; apply sum_congr rfl; intro p _; ring
      _ ≤ (4*a)*(5/η) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  rw [boxTheta_cons]
  unfold boxTheta
  rw [mul_left_comm (20/η)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4*logarithmicIntegral N)
  rw [mul_sum]
  apply sum_le_sum
  intro d hdm
  have hh := mul_le_mul_of_nonneg_left (hpoint d hdm) (Nat.cast_nonneg (convolutionCoeff W d))
  convert hh using 1
  ring

/-- Source high boxes have a uniform base gap before any d or prime is
selected. This pays the mesh-wide prime-tail normalization. -/
theorem original_base_gap {N : ℕ} {δ : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hr : OriginalRectangles N V) :
    (N : ℝ)^(10*highEta) ≤ (N : ℝ)^(1/2-δ)/(∏ j, V j) ∧
      (N : ℝ)^(1/2-δ)/(∏ j, V j) ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hv : ∀ j, 1 ≤ V j := fun j =>
    (one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 100/1327)).trans (hV j)
  have hprod1 : 1 ≤ ∏ j, V j := one_le_prod (fun j _ => hv j)
  have hprod := original_rectangles_product hN (fun j => (by linarith [hv j] : 0 ≤ V j)) hr
  constructor
  · apply (le_div_iff₀ (by linarith : 0 < ∏ j, V j)).mpr
    calc
      _ ≤ (N : ℝ)^(10*highEta)*(N : ℝ)^(1/2-100*highEta) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (N : ℝ)^(1/2-90*highEta) := by rw [← rpow_add hNp]; congr 1; ring
      _ ≤ _ := rpow_le_rpow_of_exponent_le hN1 (by
        have he : 0 < highEta := by norm_num [highEta]
        linarith)
  · apply (div_le_self (by positivity) hprod1).trans
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1 (show 1/2-δ ≤ (1 : ℝ) by linarith)

/-- All r complete source cells have bounded total inserted Theta; therefore
so do the inner cells. This is an actual original-high-box bound. -/
theorem original_grid_theta {N r : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hΔ : 1 < Δ)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hrect : OriginalRectangles N V)
    (hlarge : 4 ≤ (N : ℝ)^highEta)
    (hstart : LiLiuPrereqBuchstab.primeErrorStart ≤ (N : ℝ)^highEta)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 5)
    (hr : reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ j, V j)) Δ t r ≤
      ((N : ℝ)^(1/2-δ)/(∏ j, V j))^(1/s)) :
    (∑ j ∈ range r, boxTheta N ((N : ℝ)^(1/2-δ))
      (Fin.cons (cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t j) (convolutionWuWindows N Δ V))) ≤
        (20/highEta)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let q := (N : ℝ)^(1/2-δ)/(∏ j, V j)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hVp : ∀ j, 0 < V j := fun j => (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hV j)
  have he : 0 < highEta := by norm_num [highEta]
  have hb := original_base_gap (show 2 ≤ N by omega) hδ hδhi hV hrect
  have hq : 1 < q := (one_lt_rpow hN1 (by positivity : 0 < 10*highEta)).trans_le hb.1
  have hQ : 0 < (N : ℝ)^(1/2-δ) := rpow_pos_of_pos (by linarith) _
  have hsp := fun (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) =>
    reboxing_support_level_bounds hQ.le (show 0 < Δ by linarith) hVp hd
  rw [theta_grid_exact _ (by linarith : 0 < q) hΔ]
  apply inserted_theta_bound _ _ hN he hlarge hstart
  · intro d hd
    exact ⟨(reboxing_support_product_bounds (show 0 < Δ by linarith) (fun j => (hVp j).le) hd).1,
      hq.trans_le (hsp d hd).1⟩
  · intro p hp
    have hh := mem_primeWindow.mp hp
    refine ⟨hh.1,hh.2.1,?_,?_⟩
    · apply le_trans _ hh.2.2.1
      rw [reboxingAlpha_zero]
      calc
        _ ≤ (N : ℝ)^((10*highEta)*(1/t)) := by
          apply rpow_le_rpow_of_exponent_le hN1.le
          rw [mul_one_div]
          apply (le_div_iff₀ (show 0 < t by linarith)).mpr
          nlinarith
        _ = ((N : ℝ)^(10*highEta))^(1/t) := rpow_mul (by positivity) _ _
        _ ≤ _ := rpow_le_rpow (by positivity) hb.1 (one_div_nonneg.mpr (by linarith))
    · apply (hh.2.2.2.le.trans hr).trans
      have hexp : 1/s ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      have hqq : q^(1/s) ≤ q := by
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hq.le hexp
      exact hqq.trans hb.2
  · intro d hd p hp
    have hpq := (mem_primeWindow.mp hp).2.2.2.le.trans hr
    apply hpq.trans
    calc
      _ ≤ q^(1/2 : ℝ) := rpow_le_rpow_of_exponent_le hq.le (one_div_le_one_div_of_le (by norm_num) hs)
      _ ≤ _ := rpow_le_rpow (by linarith : 0 ≤ q) (hsp d hd).1 (by norm_num)

end
end HighOmega2
