import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBaseEstimate
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformAbel

/-!
# Finite-band estimates for the actual rough-integer count

The error function is constructed from the actual PNT envelope. Constants are
independent of both real parameters, and the boundary term retains the unit
when the two parameters are close.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace LiLiuPrereqBuchstab

noncomputable def buchstabRemainder (y : ℝ) : ℝ :=
  primeErrorEnvelope y + 1 / Real.log y

theorem buchstabRemainder_nonneg {y : ℝ} (hy : primeErrorStart ≤ y) :
    0 ≤ buchstabRemainder y := by
  have hl : 0 < Real.log y := lt_of_lt_of_le zero_lt_one (one_le_log_of_start_le hy)
  exact add_nonneg (primeErrorEnvelope_nonneg y) (by positivity)

theorem antitoneOn_buchstabRemainder :
    AntitoneOn buchstabRemainder (Set.Ici primeErrorStart) := by
  intro a ha b _ hab
  change primeErrorStart ≤ a at ha
  apply add_le_add (antitone_primeErrorEnvelope hab)
  have ha0 : 0 < a := by linarith [primeErrorStart_spec.1]
  exact one_div_le_one_div_of_le
    (lt_of_lt_of_le zero_lt_one (one_le_log_of_start_le ha))
    (Real.log_le_log ha0 hab)

theorem tendsto_buchstabRemainder :
    Tendsto buchstabRemainder atTop (𝓝 0) := by
  unfold buchstabRemainder
  simpa only [add_zero] using
    tendsto_primeErrorEnvelope.add
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
        Tendsto (fun y : ℝ => 1 / Real.log y) atTop (𝓝 0))

private theorem bands_pos {y : ℝ} (hy : primeErrorStart ≤ y) :
    0 < y ∧ 0 < Real.log y := by
  exact ⟨by linarith [primeErrorStart_spec.1],
    lt_of_lt_of_le zero_lt_one (one_le_log_of_start_le hy)⟩

theorem buchstabRemainder_inv_log_le {y : ℝ} :
    1 / Real.log y ≤ buchstabRemainder y := by
  unfold buchstabRemainder
  linarith [primeErrorEnvelope_nonneg y]

theorem buchstabRemainder_envelope_le {y : ℝ} (hy : primeErrorStart ≤ y) :
    primeErrorEnvelope y ≤ buchstabRemainder y := by
  have hl := (bands_pos hy).2
  unfold buchstabRemainder
  have h : 0 ≤ 1 / Real.log y := by positivity
  linarith

theorem buchstabRemainder_log_sq_bound {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hx : 0 ≤ x) :
    x / Real.log y ^ 2 ≤ buchstabRemainder y * (x / Real.log y) := by
  calc
    _ = (1 / Real.log y) * (x / Real.log y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right buchstabRemainder_inv_log_le
      (div_nonneg hx (bands_pos hy).2.le)

theorem sievingPrimes_sqrt_eq_primesIco {x y : ℝ}
    (hx : 1 ≤ x) :
    sievingPrimes x y (Real.sqrt x) = primesIco y (Real.sqrt x) := by
  ext p
  rw [mem_sievingPrimes, mem_primesIco (Real.sqrt_nonneg x)]
  constructor
  · rintro ⟨hp, _, hpy, hpb⟩
    exact ⟨hp, hpy, hpb⟩
  · rintro ⟨hp, hpy, hpb⟩
    have hs : Real.sqrt x ≤ x := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x), Real.sqrt_nonneg x]
    exact ⟨hp, hpb.le.trans hs, hpy, hpb⟩

theorem roughCount_buchstab_sqrt {x y : ℝ}
    (hx : 1 ≤ x) (hy : y ≤ Real.sqrt x) :
    (roughCount x y : ℝ) = (roughCount x (Real.sqrt x) : ℝ) +
      ∑ p ∈ primesIco y (Real.sqrt x), (roughCount (x / p) p : ℝ) := by
  rw [roughCount_buchstab hy, sievingPrimes_sqrt_eq_primesIco hx]
  push_cast
  rfl

theorem buchstabPrimeKernel_eq_subproblem {x p : ℝ}
    (hx : 0 < x) (hp : 1 < p) :
    buchstabPrimeKernel x p =
      (x / p) * buchstab (Real.log (x / p) / Real.log p) / Real.log p := by
  have hl := (Real.log_pos hp).ne'
  rw [Real.log_div hx.ne' (by linarith : p ≠ 0)]
  have he : (Real.log x - Real.log p) / Real.log p =
      Real.log x / Real.log p - 1 := by field_simp
  rw [he]
  unfold buchstabPrimeKernel
  ring

private theorem primesIco_subset_primesIcc {y b : ℝ} (hb : 0 ≤ b) :
    primesIco y b ⊆ primesIcc y b := by
  intro p hp
  obtain ⟨hp, hyp, hpb⟩ := (mem_primesIco hb).1 hp
  exact (mem_primesIcc hb).2 ⟨hp, hyp, hpb.le⟩

theorem sum_primesIco_inv_mul_log_le {y b : ℝ}
    (hy : primeErrorStart ≤ y) (hyb : y ≤ b) :
    ∑ p ∈ primesIco y b, 1 / ((p : ℝ) * Real.log p) ≤ 5 / Real.log y := by
  have hb0 := (bands_pos (hy.trans hyb)).1.le
  refine (Finset.sum_le_sum_of_subset_of_nonneg
    (primesIco_subset_primesIcc hb0) ?_).trans
      (sum_primesIcc_inv_mul_log_le hy hyb)
  intro p hp _
  have hpl := (bands_pos (hy.trans ((mem_primesIcc hb0).1 hp).2.1)).2
  positivity

theorem sum_primesIco_div_log_le {y b : ℝ}
    (hy : primeErrorStart ≤ y) (hyb : y ≤ b) :
    ∑ p ∈ primesIco y b, (p : ℝ) / Real.log p ≤ 2 * b ^ 2 / Real.log b ^ 2 := by
  have hb0 := (bands_pos (hy.trans hyb)).1.le
  refine (Finset.sum_le_sum_of_subset_of_nonneg
    (primesIco_subset_primesIcc hb0) ?_).trans
      (sum_primesIcc_div_log_le hy (hy.trans hyb))
  intro p hp _
  have hpl := (bands_pos (hy.trans ((mem_primesIcc hb0).1 hp).2.1)).2
  positivity

private theorem bands_log_sq_mono {x y b : ℝ}
    (hy : primeErrorStart ≤ y) (hyb : y ≤ b) (hx : 0 ≤ x) :
    x / Real.log b ^ 2 ≤ x / Real.log y ^ 2 := by
  have hly := (bands_pos hy).2
  have hlog := Real.log_le_log (bands_pos hy).1 hyb
  apply div_le_div_of_nonneg_left hx (sq_pos_of_pos hly)
  nlinarith

/-- The square-root terminal count costs only five copies of the common error. -/
theorem roughCount_sqrt_error_le {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x) :
    |(roughCount x (Real.sqrt x) : ℝ) - x / Real.log x| ≤
      5 * (buchstabRemainder y * (x / Real.log y)) := by
  have hy0 := (bands_pos hy).1
  have hly := (bands_pos hy).2
  have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  have hyb : y ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hxy
  have hb := hy.trans hyb
  have hb0 := (bands_pos hb).1
  have hlb := (bands_pos hb).2
  have hb2 := Real.sq_sqrt hx0
  have hbx : Real.sqrt x ≤ x := by nlinarith
  have hyx := hyb.trans hbx
  have hlog := Real.log_le_log hy0 hyx
  have hbase := roughCount_base_error hb hbx hb2.ge
  have herr :
      primeErrorEnvelope (Real.sqrt x) * (x / Real.log x) ≤
        buchstabRemainder y * (x / Real.log y) := by
    apply mul_le_mul
      ((antitone_primeErrorEnvelope hyb).trans (buchstabRemainder_envelope_le hy))
      (div_le_div_of_nonneg_left hx0 hly hlog)
      (div_nonneg hx0 (hly.le.trans hlog))
      (buchstabRemainder_nonneg hy)
  have hboundary : Real.sqrt x / Real.log (Real.sqrt x) ≤
      buchstabRemainder y * (x / Real.log y) := by
    calc
      _ = (Real.sqrt x * Real.log (Real.sqrt x)) / Real.log (Real.sqrt x) ^ 2 := by
        field_simp
      _ ≤ x / Real.log (Real.sqrt x) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        have hh := Real.log_le_sub_one_of_pos hb0
        nlinarith
      _ ≤ x / Real.log y ^ 2 := bands_log_sq_mono hy hyb hx0
      _ ≤ _ := buchstabRemainder_log_sq_bound hy hx0
  linarith

/-- Summing the recursively generated errors has the uniform multiplier seven. -/
theorem sum_buchstabRemainder_errors_le {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hxy : y ^ 2 ≤ x) :
    ∑ p ∈ primesIco y (Real.sqrt x),
      (buchstabRemainder p * ((x / p) / Real.log p) + (p : ℝ) / Real.log p) ≤
        7 * (buchstabRemainder y * (x / Real.log y)) := by
  have hx0 : 0 ≤ x := (sq_nonneg y).trans hxy
  have hyb : y ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hxy
  have hly := (bands_pos hy).2
  have hr := buchstabRemainder_nonneg hy
  have hfirst :
      ∑ p ∈ primesIco y (Real.sqrt x), buchstabRemainder p * ((x / p) / Real.log p) ≤
        5 * (buchstabRemainder y * (x / Real.log y)) := by
    calc
      _ ≤ ∑ p ∈ primesIco y (Real.sqrt x),
          (buchstabRemainder y * x) * (1 / ((p : ℝ) * Real.log p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hyp := ((mem_primesIco (Real.sqrt_nonneg x)).1 hp).2.1
        have hpl := (bands_pos (hy.trans hyp)).2
        have hrem := antitoneOn_buchstabRemainder hy (hy.trans hyp) hyp
        have hh := mul_le_mul_of_nonneg_right hrem
          (show 0 ≤ (x / p) / Real.log p by positivity)
        convert hh using 1
        ring
      _ = (buchstabRemainder y * x) *
          ∑ p ∈ primesIco y (Real.sqrt x), 1 / ((p : ℝ) * Real.log p) := by
        rw [Finset.mul_sum]
      _ ≤ (buchstabRemainder y * x) * (5 / Real.log y) :=
        mul_le_mul_of_nonneg_left (sum_primesIco_inv_mul_log_le hy hyb) (mul_nonneg hr hx0)
      _ = _ := by ring
  have hsecond :
      ∑ p ∈ primesIco y (Real.sqrt x), (p : ℝ) / Real.log p ≤
        2 * (buchstabRemainder y * (x / Real.log y)) := by
    calc
      _ ≤ 2 * Real.sqrt x ^ 2 / Real.log (Real.sqrt x) ^ 2 :=
        sum_primesIco_div_log_le hy hyb
      _ = 2 * (x / Real.log (Real.sqrt x) ^ 2) := by rw [Real.sq_sqrt hx0]; ring
      _ ≤ 2 * (x / Real.log y ^ 2) :=
        mul_le_mul_of_nonneg_left (bands_log_sq_mono hy hyb hx0) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (buchstabRemainder_log_sq_bound hy hx0) (by norm_num)
  rw [Finset.sum_add_distrib]
  linarith

theorem buchstab_subproblem_band {x y : ℝ} {k p : ℕ}
    (hy : primeErrorStart ≤ y) (hxy : x ≤ y ^ (k + 1))
    (hp : p ∈ primesIco y (Real.sqrt x)) :
    primeErrorStart ≤ (p : ℝ) ∧ (p : ℝ) ≤ x / p ∧ x / p ≤ (p : ℝ) ^ k := by
  obtain ⟨_, hyp, hpb⟩ := (mem_primesIco (Real.sqrt_nonneg x)).1 hp
  have hp0 := (bands_pos (hy.trans hyp)).1
  have hy0 := (bands_pos hy).1
  have hx0 : 0 ≤ x := by
    by_contra hx
    have hs : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [hs] at hpb
    linarith
  refine ⟨hy.trans hyp, ?_, ?_⟩
  · apply (le_div_iff₀ hp0).2
    nlinarith [Real.sq_sqrt hx0]
  · apply (div_le_iff₀ hp0).2
    calc
      x ≤ y ^ (k + 1) := hxy
      _ ≤ (p : ℝ) ^ (k + 1) := pow_le_pow_left₀ hy0.le hyp _
      _ = (p : ℝ) ^ k * p := pow_succ _ _

theorem log_ratio_le_of_le_pow {x y : ℝ} {k : ℕ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ k) :
    Real.log x / Real.log y ≤ (k : ℝ) := by
  apply (div_le_iff₀ (bands_pos hy).2).2
  have h := Real.log_le_log ((bands_pos hy).1.trans_le hyx) hxy
  simpa only [Real.log_pow] using h

private theorem buchstab_main_decomposition {x y : ℝ}
    (hx : 1 < x) (hy : 1 < y) :
    x * buchstab (Real.log x / Real.log y) / Real.log y =
      x / Real.log x + x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1) := by
  have hlx := (Real.log_pos hx).ne'
  have hly := (Real.log_pos hy).ne'
  field_simp
  ring

/-- An explicit finite-band constant, depending only on the integer band. -/
def buchstabBandConstant (k : ℕ) : ℝ := 112 * 8 ^ k

theorem buchstabBandConstant_ge (k : ℕ) : 112 ≤ buchstabBandConstant k := by
  have h : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
  unfold buchstabBandConstant
  linarith

theorem buchstabBandConstant_succ (k : ℕ) :
    buchstabBandConstant (k + 1) = 8 * buchstabBandConstant k := by
  unfold buchstabBandConstant
  rw [pow_succ]
  ring

theorem roughCount_base_remainder_error {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ 2) :
    |(roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
      4 * (buchstabRemainder y * (x / Real.log y) + y / Real.log y) := by
  have hx0 := ((bands_pos hy).1.trans_le hyx).le
  have hxlog : 0 ≤ x / Real.log y := div_nonneg hx0 (bands_pos hy).2.le
  have hr := mul_le_mul_of_nonneg_right (buchstabRemainder_envelope_le hy) hxlog
  have hn := mul_nonneg (buchstabRemainder_nonneg hy) hxlog
  have hh := roughCount_base_buchstab_error hy hyx hxy
  linarith

private theorem roughCount_base_band_error (n : ℕ) {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hsq : x ≤ y ^ 2) :
    |(roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
      buchstabBandConstant n *
        (buchstabRemainder y * (x / Real.log y) + y / Real.log y) := by
  have hy0 := (bands_pos hy).1
  have hly := (bands_pos hy).2
  have hx0 := hy0.trans_le hyx
  have hr := buchstabRemainder_nonneg hy
  exact (roughCount_base_remainder_error hy hyx hsq).trans
    (mul_le_mul_of_nonneg_right (by linarith [buchstabBandConstant_ge n]) (by positivity))

/-- The actual finite-band induction, with no rough-count estimate among its
hypotheses. The same explicit constant works for all real `x,y` in the band. -/
theorem roughCount_buchstab_band_error (k : ℕ) (hk : k ≤ 100) {x y : ℝ}
    (hy : primeErrorStart ≤ y) (hyx : y ≤ x) (hxy : x ≤ y ^ k) :
    |(roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
      buchstabBandConstant k *
        (buchstabRemainder y * (x / Real.log y) + y / Real.log y) := by
  induction k generalizing x y with
  | zero =>
    apply roughCount_base_band_error 0 hy hyx
    have hy1 : 1 ≤ y := by linarith [primeErrorStart_spec.1]
    exact hxy.trans (pow_le_pow_right₀ hy1 (by omega))
  | succ k ih =>
    by_cases hsq : x ≤ y ^ 2
    · exact roughCount_base_band_error (k + 1) hy hyx hsq
    have hxy2 : y ^ 2 ≤ x := (lt_of_not_ge hsq).le
    have hy0 := (bands_pos hy).1
    have hly := (bands_pos hy).2
    have hy1 : 1 < y := by linarith [primeErrorStart_spec.1]
    have hx1 := hy1.trans_le hyx
    have hx0 : 0 < x := hy0.trans_le hyx
    have hyb : y ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hxy2
    have hC : 0 ≤ buchstabBandConstant k := by linarith [buchstabBandConstant_ge k]
    have hr := buchstabRemainder_nonneg hy
    have hcommon : 0 ≤ buchstabRemainder y * (x / Real.log y) := by positivity
    have hU : Real.log x / Real.log y ≤ 100 :=
      (log_ratio_le_of_le_pow hy hyx hxy).trans (by exact_mod_cast hk)
    have hrec :
        |(∑ p ∈ primesIco y (Real.sqrt x), (roughCount (x / p) p : ℝ)) -
          ∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p| ≤
        buchstabBandConstant k * (7 * (buchstabRemainder y * (x / Real.log y))) := by
      calc
        _ = |∑ p ∈ primesIco y (Real.sqrt x),
            ((roughCount (x / p) p : ℝ) - buchstabPrimeKernel x p)| := by
          rw [Finset.sum_sub_distrib]
        _ ≤ ∑ p ∈ primesIco y (Real.sqrt x),
            |(roughCount (x / p) p : ℝ) - buchstabPrimeKernel x p| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ primesIco y (Real.sqrt x), buchstabBandConstant k *
            (buchstabRemainder p * ((x / p) / Real.log p) + (p : ℝ) / Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpstart, hpx, hxp⟩ := buchstab_subproblem_band hy hxy hp
          have hp1 : 1 < (p : ℝ) := by linarith [primeErrorStart_spec.1]
          rw [buchstabPrimeKernel_eq_subproblem hx0 hp1]
          exact ih (by omega) hpstart hpx hxp
        _ = buchstabBandConstant k *
            ∑ p ∈ primesIco y (Real.sqrt x),
              (buchstabRemainder p * ((x / p) / Real.log p) + (p : ℝ) / Real.log p) := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_buchstabRemainder_errors_le hy hxy2) hC
    have hterminal := roughCount_sqrt_error_le hy hxy2
    have hkernel := buchstabPrimeKernel_sum_Ico_error_le hy hxy2 hU
    change _ ≤ 106 * buchstabRemainder y * (x / Real.log y) at hkernel
    have he :
        (roughCount x y : ℝ) - x * buchstab (Real.log x / Real.log y) / Real.log y =
        ((roughCount x (Real.sqrt x) : ℝ) - x / Real.log x) +
        ((∑ p ∈ primesIco y (Real.sqrt x), (roughCount (x / p) p : ℝ)) -
          ∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) +
        ((∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
          x / Real.log x *
            ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)) := by
      rw [roughCount_buchstab_sqrt hx1.le hyb, buchstab_main_decomposition hx1 hy1]
      ring
    have htotal :
        |(roughCount x y : ℝ) -
          x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
        (7 * buchstabBandConstant k + 111) *
          (buchstabRemainder y * (x / Real.log y)) := by
      rw [he]
      calc
        _ ≤ |(roughCount x (Real.sqrt x) : ℝ) - x / Real.log x| +
            |(∑ p ∈ primesIco y (Real.sqrt x), (roughCount (x / p) p : ℝ)) -
              ∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p| +
            |(∑ p ∈ primesIco y (Real.sqrt x), buchstabPrimeKernel x p) -
              x / Real.log x *
                ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ 5 * (buchstabRemainder y * (x / Real.log y)) +
            buchstabBandConstant k * (7 * (buchstabRemainder y * (x / Real.log y))) +
            106 * buchstabRemainder y * (x / Real.log y) :=
          add_le_add (add_le_add hterminal hrec) hkernel
        _ = _ := by ring
    apply htotal.trans
    rw [buchstabBandConstant_succ]
    have hboundary : 0 ≤ y / Real.log y := by positivity
    have hconstant := buchstabBandConstant_ge k
    nlinarith

/-- In particular, there is one constant for the entire band through `100`. -/
theorem roughCount_buchstab_band_100 :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      primeErrorStart ≤ y → y ≤ x → x ≤ y ^ (100 : ℕ) →
      |(roughCount x y : ℝ) -
        x * buchstab (Real.log x / Real.log y) / Real.log y| ≤
      C * (buchstabRemainder y * (x / Real.log y) + y / Real.log y) := by
  refine ⟨buchstabBandConstant 100, by linarith [buchstabBandConstant_ge 100], ?_⟩
  intro x y hy hyx hxy
  exact roughCount_buchstab_band_error 100 (by omega) hy hyx hxy

end LiLiuPrereqBuchstab