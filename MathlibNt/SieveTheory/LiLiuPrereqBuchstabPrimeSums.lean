import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT
import Mathlib.NumberTheory.AbelSummation

/-!
# Abel summation and elementary weighted sums over actual primes

All endpoints are real. `primesIoc a b` excludes the lower endpoint and
includes the upper endpoint; `primesIcc a b` includes both.

The finite tails of `1 / (p log p)` are bounded by `4 / log a` or
`5 / log a`, respectively. The sum of `p / log p` is at most
`2 b² / log² b`. These estimates use the imported actual PNT, not
prime-distribution hypotheses supplied to the sum theorems.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace LiLiuPrereqBuchstab

noncomputable def primesIoc (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter (fun p => a < (p : ℝ))

noncomputable def primesIcc (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter (fun p => a ≤ (p : ℝ))

theorem mem_primesIoc {a b : ℝ} (hb : 0 ≤ b) {p : ℕ} :
    p ∈ primesIoc a b ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  simp only [primesIoc, Finset.mem_filter, Nat.mem_primesLE,
    Nat.le_floor_iff hb]
  tauto

theorem mem_primesIcc {a b : ℝ} (hb : 0 ≤ b) {p : ℕ} :
    p ∈ primesIcc a b ↔ p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b := by
  simp only [primesIcc, Finset.mem_filter, Nat.mem_primesLE,
    Nat.le_floor_iff hb]
  tauto

theorem primePi_eq_sum_indicator (t : ℝ) :
    primePi t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, if k.Prime then (1 : ℝ) else 0 := by
  rw [primePi, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range,
    Nat.range_succ_eq_Icc_zero]
  simp

private theorem primesIoc_eq_filter (a b : ℝ) (ha : 0 ≤ a) :
    primesIoc a b = (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
  ext p
  simp only [primesIoc, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Ioc,
    Nat.floor_lt ha]
  tauto

/-- Exact prime Abel summation, with the endpoint at `a` excluded. -/
theorem prime_abel {a b : ℝ} {f : ℝ → ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ p ∈ primesIoc a b, f p =
      f b * primePi b - f a * primePi a -
        ∫ t in a..b, deriv f t * primePi t := by
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) ha hab hf hi
  simp only [← primePi_eq_sum_indicator, ← intervalIntegral.integral_of_le hab] at h
  rw [primesIoc_eq_filter a b ha, Finset.sum_filter]
  simpa only [mul_ite, mul_one, mul_zero] using h

/-- The step-function factor `pi(t)` preserves integrability on finite intervals. -/
theorem integrableOn_mul_primePi {a b : ℝ} {g : ℝ → ℝ} (ha : 0 ≤ a)
    (hg : IntegrableOn g (Set.Icc a b)) :
    IntegrableOn (fun t => g t * primePi t) (Set.Icc a b) := by
  simpa only [← primePi_eq_sum_indicator] using
    integrableOn_mul_sum_Icc
      (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) (m := 0) ha hg

private theorem start_pos {t : ℝ} (ht : primeErrorStart ≤ t) : 0 < t := by
  linarith [primeErrorStart_spec.1]

theorem one_le_log_of_start_le {t : ℝ} (ht : primeErrorStart ≤ t) :
    1 ≤ Real.log t :=
  (Real.le_log_iff_exp_le (start_pos ht)).2 (primeErrorStart_spec.2.1.trans ht)

private theorem log_pos_of_start_le {t : ℝ} (ht : primeErrorStart ≤ t) :
    0 < Real.log t := lt_of_lt_of_le zero_lt_one (one_le_log_of_start_le ht)

private theorem hasDerivAt_primeTailWeight {t : ℝ} (ht : primeErrorStart ≤ t) :
    HasDerivAt (fun s : ℝ => 1 / (s * Real.log s))
      (-((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2))) t := by
  have ht0 := (start_pos ht).ne'
  have hl0 := (log_pos_of_start_le ht).ne'
  convert! (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)) (mul_ne_zero ht0 hl0) using 1
  dsimp
  field_simp
  ring

private theorem hasDerivAt_logTailPrimitive {t : ℝ} (ht : primeErrorStart ≤ t) :
    HasDerivAt (fun s : ℝ => -4 / Real.log s)
      (4 / (t * Real.log t ^ 2)) t := by
  have ht0 := (start_pos ht).ne'
  have hl0 := (log_pos_of_start_le ht).ne'
  convert! (hasDerivAt_const t (-4 : ℝ)).div
    (Real.hasDerivAt_log ht0) hl0 using 1
  field_simp
  ring

private theorem continuousOn_primeTailKernel {a b : ℝ} (ha : primeErrorStart ≤ a) :
    ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2))
      (Set.Icc a b) := by
  intro t ht
  have ht0 := (start_pos (ha.trans ht.1)).ne'
  have hl0 := (log_pos_of_start_le (ha.trans ht.1)).ne'
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp_all)

private theorem continuousOn_logTailKernel {a b : ℝ} (ha : primeErrorStart ≤ a) :
    ContinuousOn (fun t : ℝ => 4 / (t * Real.log t ^ 2)) (Set.Icc a b) := by
  intro t ht
  have ht0 := (start_pos (ha.trans ht.1)).ne'
  have hl0 := (log_pos_of_start_le (ha.trans ht.1)).ne'
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp_all)

private theorem primeTailKernel_mul_primePi_le {t : ℝ} (ht : primeErrorStart ≤ t) :
    (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) * primePi t ≤
      4 / (t * Real.log t ^ 2) := by
  have ht0 := start_pos ht
  have hl0 := log_pos_of_start_le ht
  have hl1 := one_le_log_of_start_le ht
  have hk : 0 ≤ (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by positivity
  have hk' : (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) ≤
      2 / (t ^ 2 * Real.log t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have h := mul_le_mul_of_nonneg_left (show Real.log t + 1 ≤ 2 * Real.log t by linarith)
      (show 0 ≤ t ^ 2 * Real.log t by positivity)
    nlinarith
  calc
    _ ≤ (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) * (2 * (t / Real.log t)) :=
      mul_le_mul_of_nonneg_left (primePi_le_two_mul ht) hk
    _ ≤ (2 / (t ^ 2 * Real.log t)) * (2 * (t / Real.log t)) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    _ = 4 / (t * Real.log t ^ 2) := by field_simp; ring

/-- The elementary logarithmic integral used to bound every finite prime tail. -/
theorem integral_logTailKernel {a b : ℝ} (ha : primeErrorStart ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, 4 / (t * Real.log t ^ 2)) =
      4 / Real.log a - 4 / Real.log b := by
  have hi : IntervalIntegrable (fun t : ℝ => 4 / (t * Real.log t ^ 2)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (continuousOn_logTailKernel ha).integrableOn_Icc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (ht : t ∈ Set.uIcc a b) =>
      hasDerivAt_logTailPrimitive (ha.trans ((Set.uIcc_of_le hab ▸ ht).1))) hi
  convert h using 1
  ring

private theorem primeTailEndpoint_le {t : ℝ} (ht : primeErrorStart ≤ t) :
    1 / (t * Real.log t) * primePi t ≤ 4 / Real.log t := by
  have ht0 := start_pos ht
  have hl0 := log_pos_of_start_le ht
  have hl1 := one_le_log_of_start_le ht
  calc
    _ ≤ 1 / (t * Real.log t) * (2 * (t / Real.log t)) :=
      mul_le_mul_of_nonneg_left (primePi_le_two_mul ht) (by positivity)
    _ = 2 / Real.log t ^ 2 := by field_simp
    _ ≤ 4 / Real.log t := by
      apply (div_le_div_iff₀ (by positivity) hl0).2
      nlinarith

/-- (E), excluding the lower endpoint: the constant is independent of both endpoints. -/
theorem sum_primesIoc_inv_mul_log_le {y b : ℝ}
    (hy : primeErrorStart ≤ y) (hyb : y ≤ b) :
    ∑ p ∈ primesIoc y b, 1 / ((p : ℝ) * Real.log p) ≤ 4 / Real.log y := by
  let k : ℝ → ℝ := fun t => (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)
  have hy0 := (start_pos hy).le
  have hk : IntegrableOn k (Set.Icc y b) :=
    (continuousOn_primeTailKernel hy).integrableOn_Icc
  have hd : IntegrableOn (deriv (fun t : ℝ => 1 / (t * Real.log t))) (Set.Icc y b) := by
    refine hk.neg.congr_fun ?_ measurableSet_Icc
    intro t ht
    exact (hasDerivAt_primeTailWeight (hy.trans ht.1)).deriv.symm
  have hab := prime_abel hy0 hyb
    (fun t ht => (hasDerivAt_primeTailWeight (hy.trans ht.1)).differentiableAt) hd
  have heq :
      (∫ t in y..b, deriv (fun s : ℝ => 1 / (s * Real.log s)) t * primePi t) =
        -(∫ t in y..b, k t * primePi t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have hdt : deriv (fun s : ℝ => 1 / (s * Real.log s)) t = -k t :=
      (hasDerivAt_primeTailWeight (hy.trans ((Set.uIcc_of_le hyb ▸ ht).1))).deriv
    change deriv (fun s : ℝ => 1 / (s * Real.log s)) t * primePi t = -(k t * primePi t)
    rw [hdt]
    exact neg_mul _ _
  have hkpi : IntervalIntegrable (fun t => k t * primePi t) volume y b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyb).2 (integrableOn_mul_primePi hy0 hk)
  have hg : IntervalIntegrable (fun t : ℝ => 4 / (t * Real.log t ^ 2)) volume y b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyb).2
      (continuousOn_logTailKernel hy).integrableOn_Icc
  have hle := intervalIntegral.integral_mono_on hyb hkpi hg
    (fun t ht => primeTailKernel_mul_primePi_le (hy.trans ht.1))
  rw [integral_logTailKernel hy hyb] at hle
  have hb := primeTailEndpoint_le (hy.trans hyb)
  have hnonneg : 0 ≤ 1 / (y * Real.log y) * primePi y := by
    have hylog := log_pos_of_start_le hy
    unfold primePi
    positivity
  rw [heq] at hab
  linarith

/-- Exact lower-endpoint correction; it is present only when the real endpoint is a prime. -/
theorem sum_primesIcc_eq_sum_primesIoc_add {y b : ℝ} (hb : 0 ≤ b) (f : ℝ → ℝ) :
    ∑ p ∈ primesIcc y b, f p =
      (∑ p ∈ primesIoc y b, f p) +
        if ∃ p ∈ primesIcc y b, (p : ℝ) = y then f y else 0 := by
  classical
  by_cases he : ∃ p ∈ primesIcc y b, (p : ℝ) = y
  · obtain ⟨p, hp, hpy⟩ := he
    have hs : primesIcc y b = insert p (primesIoc y b) := by
      ext q
      rw [mem_primesIcc hb, Finset.mem_insert, mem_primesIoc hb]
      constructor
      · intro hq
        by_cases hqp : q = p
        · exact Or.inl hqp
        · refine Or.inr ⟨hq.1, lt_of_le_of_ne hq.2.1 ?_, hq.2.2⟩
          intro hyq
          exact hqp (Nat.cast_injective (hyq.symm.trans hpy.symm))
      · rintro (rfl | hq)
        · exact (mem_primesIcc hb).1 hp
        · exact ⟨hq.1, hq.2.1.le, hq.2.2⟩
    have hn : p ∉ primesIoc y b := by
      intro h
      have hlt := ((mem_primesIoc hb).1 h).2.1
      simp [hpy] at hlt
    rw [if_pos ⟨p, hp, hpy⟩, hs, Finset.sum_insert hn, hpy, add_comm]
  · have hs : primesIcc y b = primesIoc y b := by
      ext p
      rw [mem_primesIcc hb, mem_primesIoc hb]
      constructor
      · intro hp
        refine ⟨hp.1, lt_of_le_of_ne hp.2.1 ?_, hp.2.2⟩
        intro hyp
        exact he ⟨p, (mem_primesIcc hb).2 hp, hyp.symm⟩
      · intro hp
        exact ⟨hp.1, hp.2.1.le, hp.2.2⟩
    rw [if_neg he, hs, add_zero]

/-- (E), with both endpoints included and an explicit absolute constant. -/
theorem sum_primesIcc_inv_mul_log_le {y b : ℝ}
    (hy : primeErrorStart ≤ y) (hyb : y ≤ b) :
    ∑ p ∈ primesIcc y b, 1 / ((p : ℝ) * Real.log p) ≤ 5 / Real.log y := by
  classical
  have hy0 := start_pos hy
  have hyl := log_pos_of_start_le hy
  have hy1 : 1 ≤ y := by linarith [primeErrorStart_spec.1]
  have hc : 1 / (y * Real.log y) ≤ 1 / Real.log y := by
    apply one_div_le_one_div_of_le hyl
    nlinarith
  rw [sum_primesIcc_eq_sum_primesIoc_add (y := y) (start_pos (hy.trans hyb)).le
    (fun t : ℝ => 1 / (t * Real.log t))]
  have hsum := sum_primesIoc_inv_mul_log_le hy hyb
  have he : 5 / Real.log y = 4 / Real.log y + 1 / Real.log y := by ring
  rw [he]
  split_ifs
  · exact add_le_add hsum hc
  · exact add_le_add hsum (by positivity)

/-- (F), with real endpoints and the fixed constant from the actual PNT bound. -/
theorem sum_primesIcc_div_log_le {y b : ℝ}
    (hy : primeErrorStart ≤ y) (hb : primeErrorStart ≤ b) :
    ∑ p ∈ primesIcc y b, (p : ℝ) / Real.log p ≤ 2 * b ^ 2 / Real.log b ^ 2 := by
  have hb0 := start_pos hb
  have hbl := log_pos_of_start_le hb
  have hc : ((primesIcc y b).card : ℝ) ≤ primePi b := by
    rw [primePi, ← Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset
      (fun p : ℕ => y ≤ (p : ℝ)) (Nat.primesLE ⌊b⌋₊))
  calc
    _ ≤ ∑ _p ∈ primesIcc y b, b / Real.log b := by
      apply Finset.sum_le_sum
      intro p hp
      have h := (mem_primesIcc hb0.le).1 hp
      exact div_log_mono (hy.trans h.2.1) h.2.2
    _ = ((primesIcc y b).card : ℝ) * (b / Real.log b) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ primePi b * (b / Real.log b) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (2 * (b / Real.log b)) * (b / Real.log b) :=
      mul_le_mul_of_nonneg_right (primePi_le_two_mul hb) (by positivity)
    _ = 2 * b ^ 2 / Real.log b ^ 2 := by ring

end LiLiuPrereqBuchstab