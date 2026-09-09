import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-!
# Finite logarithmic lcm-weight bounds

These finite arithmetic estimates depend only on divisor moments and harmonic
sums, not on smoothing, Poisson summation, or dispersion estimates.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds

open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

noncomputable section

theorem sum_div_multiples_le_log {L : ℝ} (hL : 1 ≤ L)
    {d : ℕ} (hd : 0 < d) :
    (∑ r ∈ Ioc 0 ⌊L⌋₊, if d ∣ r then (d : ℝ) / r else 0) ≤ 1 + Real.log L := by
  classical
  let S := (Ioc 0 ⌊L⌋₊).filter (fun r => d ∣ r)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hi : Set.InjOn (fun r => r / d) (↑S : Set ℕ) := by
    intro r hr s hs he
    change r / d = s / d at he
    have hr' := (mem_filter.mp hr).2
    have hs' := (mem_filter.mp hs).2
    calc
      r = d * (r / d) := (Nat.mul_div_cancel' hr').symm
      _ = d * (s / d) := by rw [he]
      _ = s := Nat.mul_div_cancel' hs'
  have hsub : S.image (fun r => r / d) ⊆ Ioc 0 ⌊L⌋₊ := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hm
    obtain ⟨hr, hdr⟩ := mem_filter.mp hr
    obtain ⟨hr0, hrL⟩ := mem_Ioc.mp hr
    exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hr0 hdr) hd,
      (Nat.div_le_self _ _).trans hrL⟩
  calc
    _ = ∑ r ∈ S, (d : ℝ) / r := (sum_filter _ _).symm
    _ = ∑ m ∈ S.image (fun r => r / d), (1 : ℝ) / m := by
      rw [sum_image hi]
      apply sum_congr rfl
      intro r hr
      rw [Nat.cast_div (mem_filter.mp hr).2 hd0]
      field_simp
    _ ≤ ∑ m ∈ Ioc 0 ⌊L⌋₊, (1 : ℝ) / m :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ m ∈ Ioc 0 ⌊L⌋₊, (fouvryTau 1 m : ℝ) / m := by
      apply sum_congr rfl
      intro m hm
      rw [fouvryTau_order_one (mem_Ioc.mp hm).1.ne', Nat.cast_one]
    _ ≤ _ := by simpa using sum_fouvryTau_div_le_real 1 hL

/-- The gcd harmonic row sum is paid by `tau_2(q)`, independently of
any modulus coefficient or coprimality restriction. -/
theorem sum_gcd_div_le_tau_log {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) {q : ℕ} (hq : 0 < q) :
    (∑ r ∈ Q, (q.gcd r : ℝ) / r) ≤
      (fouvryTau 2 q : ℝ) * (1 + Real.log L) := by
  classical
  calc
    _ ≤ ∑ r ∈ Q, ∑ d ∈ q.divisors, if d ∣ r then (d : ℝ) / r else 0 := by
      apply sum_le_sum
      intro r _
      calc
        _ = (if q.gcd r ∣ r then (q.gcd r : ℝ) / r else 0) := by
          rw [if_pos (Nat.gcd_dvd_right q r)]
        _ ≤ _ := single_le_sum
          (f := fun d => if d ∣ r then (d : ℝ) / r else 0)
          (fun d _ => by split_ifs <;> positivity)
          (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q r, hq.ne'⟩)
    _ = ∑ d ∈ q.divisors, ∑ r ∈ Q, if d ∣ r then (d : ℝ) / r else 0 := sum_comm
    _ ≤ ∑ _d ∈ q.divisors, (1 + Real.log L) := by
      apply sum_le_sum
      intro d hd
      apply le_trans (sum_le_sum_of_subset_of_nonneg hQ
        (fun r _ _ => by split_ifs <;> positivity))
      exact sum_div_multiples_le_log hL (Nat.pos_of_mem_divisors hd)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, fouvryTau_two]

theorem one_div_lcm_eq_gcd_div {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    (1 : ℝ) / (q.lcm r : ℝ) = (q.gcd r : ℝ) / ((q : ℝ) * r) := by
  have he : (q.gcd r : ℝ) * (q.lcm r : ℝ) = (q : ℝ) * r := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero hq hr))
    (mul_ne_zero (Nat.cast_ne_zero.mpr hq) (Nat.cast_ne_zero.mpr hr))).mpr
  simpa only [one_mul] using he.symm

theorem sum_one_div_lcm_le_tau_log {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) {q : ℕ} (hq : 0 < q) :
    (∑ r ∈ Q, (1 : ℝ) / (q.lcm r : ℝ)) ≤
      (fouvryTau 2 q : ℝ) / q * (1 + Real.log L) := by
  calc
    _ = (1 : ℝ) / q * ∑ r ∈ Q, (q.gcd r : ℝ) / r := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [one_div_lcm_eq_gcd_div hq.ne' (mem_Ioc.mp (hQ hr)).1.ne']
      ring
    _ ≤ (1 : ℝ) / q * ((fouvryTau 2 q : ℝ) * (1 + Real.log L)) :=
      mul_le_mul_of_nonneg_left (sum_gcd_div_le_tau_log hL Q hQ hq) (by positivity)
    _ = _ := by ring

/-- Fully evaluated double lcm sum for arbitrary signed fixed-order
modulus weights. Even order zero is allowed. -/
theorem sum_abs_lcm_weight_le_log (j : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) :
    (∑ q ∈ Q, ∑ r ∈ Q, |c q * c r / (q.lcm r : ℝ)|) ≤
      (1 + Real.log L) ^ (2 * j ^ 2 + 1) := by
  let E := ∑ q ∈ Q, c q ^ 2 * ∑ r ∈ Q, (1 : ℝ) / (q.lcm r : ℝ)
  have hsym :
      (∑ q ∈ Q, ∑ r ∈ Q, c r ^ 2 / (q.lcm r : ℝ)) = E := by
    rw [sum_comm]
    simp only [E, mul_sum, div_eq_mul_inv, one_mul, Nat.lcm_comm]
  have hbound :
      (∑ q ∈ Q, ∑ r ∈ Q, |c q * c r / (q.lcm r : ℝ)|) ≤ E := by
    calc
      _ ≤ ∑ q ∈ Q, ∑ r ∈ Q,
          (c q ^ 2 / (q.lcm r : ℝ) + c r ^ 2 / (q.lcm r : ℝ)) / 2 := by
        apply sum_le_sum
        intro q _
        apply sum_le_sum
        intro r _
        rw [abs_div, abs_mul, Nat.abs_cast, ← add_div, div_right_comm]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        nlinarith [sq_nonneg (|c q| - |c r|), sq_abs (c q), sq_abs (c r)]
      _ = E := by
        simp only [← sum_div, sum_add_distrib]
        rw [hsym]
        have he : (∑ q ∈ Q, ∑ r ∈ Q, c q ^ 2 / (q.lcm r : ℝ)) = E := by
          simp only [E, mul_sum, div_eq_mul_inv, one_mul]
        rw [he]
        ring
  apply hbound.trans
  calc
    E ≤ ∑ q ∈ Q, c q ^ 2 * ((fouvryTau 2 q : ℝ) / q * (1 + Real.log L)) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (sum_one_div_lcm_le_tau_log hL Q hQ (mem_Ioc.mp (hQ hq)).1) (sq_nonneg _)
    _ = (∑ q ∈ Q, c q ^ 2 * (fouvryTau 2 q : ℝ) / q) * (1 + Real.log L) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (1 + Real.log L) ^ (2 * j ^ 2) * (1 + Real.log L) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith [Real.log_nonneg hL])
      calc
        _ ≤ ∑ q ∈ Q, (fouvryTau (2 * j ^ 2) q : ℝ) / q := by
          apply sum_le_sum
          intro q hq
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          have hs : c q ^ 2 ≤ (fouvryTau (j ^ 2) q : ℝ) := by
            calc
              _ ≤ (fouvryTau j q : ℝ) ^ 2 := by
                simpa only [sq_abs] using
                  pow_le_pow_left₀ (abs_nonneg (c q)) (hc q hq) 2
              _ ≤ _ := by exact_mod_cast fouvryTau_sq_le j q
          calc
            _ ≤ (fouvryTau (j ^ 2) q : ℝ) * fouvryTau 2 q :=
              mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)
            _ ≤ _ := by
              rw [mul_comm]
              exact_mod_cast fouvryTau_mul_le 2 (j ^ 2) q
        _ ≤ ∑ q ∈ Ioc 0 ⌊L⌋₊, (fouvryTau (2 * j ^ 2) q : ℝ) / q :=
          sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)
        _ ≤ _ := sum_fouvryTau_div_le_real _ hL
    _ = _ := (pow_succ _ _).symm

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds
