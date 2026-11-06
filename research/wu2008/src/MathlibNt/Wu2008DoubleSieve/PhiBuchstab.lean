import MathlibNt.Wu2008DoubleSieve.PhiMonotone

/-!
# The actual Phi Buchstab step toward the double-sieve comparison

Wu04 Proposition 2 and Wu08 (3.8) start with Buchstab on the source Phi.
The identity here retains the moving prime windows, convolution weights,
and full selected modulus. It is not the limiting h/H comparison: reboxing
the new prime family and the subsequent analytic integration remain open.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

/-- At the strict new-prime cutoff, enlarging the selected modulus removes
no sifting prime. This gives the actual next `P(d*q*N)` source carrier. -/
theorem buchstab_next_source_carrier (N d : ℕ) {q : ℕ} (hq : q.Prime) :
    sieveCarrier N (d * q) (d * N) q =
      sourceSieveCarrier N (d * q) ((d * q) * N) q := by
  have hprod : ordinarySievePrimeProduct ((d * q) * N) q =
      ordinarySievePrimeProduct (d * N) q := by
    unfold ordinarySievePrimeProduct
    rw [show (d * q) * N = q * (d * N) by ring,
      primeWindow_mul_of_prime_above (d * N) hq le_rfl]
  have hsel : Sifted (d * N) (d * q) q := by
    rw [sifted_mul_iff]
    refine ⟨fun r hr hc hz => siftedLE_of_dvd_modulus (dvd_mul_right d N) q
      r hr hc hz.le, ?_⟩
    intro r hr _ hrq hrd
    have heq : r = q := (Nat.dvd_prime hq).mp hrd |>.resolve_left hr.ne_one
    subst r
    exact (lt_irrefl (q : ℝ)) hrq
  have heq := sourceSieveCarrier_eq_ite N (d * q) (d * N) (q : ℝ)
  rw [if_pos hsel] at heq
  rw [← heq]
  ext p
  simp only [sourceSieveCarrier, mem_filter, sifted_iff_product_coprime, hprod]

theorem source_buchstab_selected_modulus (N d : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    (sourceSieveCount N d (d * N) z : ℝ) =
      (sourceSieveCount N d (d * N) w : ℝ) +
        ∑ q ∈ primeWindow (d * N) z w,
          (sourceSieveCount N (d * q) ((d * q) * N) (q : ℝ) : ℝ) := by
  have h := goldbach_buchstab N d (d * N) hzw
  have hd (x : ℝ) : sieveCount N d (d * N) x = sourceSieveCount N d (d * N) x := by
    unfold sieveCount sourceSieveCount
    rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right d N)]
  rw [hd z, hd w] at h
  have hsum :
      (∑ q ∈ primeWindow (d * N) z w, sieveCount N (d * q) (d * N) q) =
        ∑ q ∈ primeWindow (d * N) z w,
          sourceSieveCount N (d * q) ((d * q) * N) q := by
    apply sum_congr rfl
    intro q hq
    unfold sieveCount sourceSieveCount
    rw [buchstab_next_source_carrier N d (mem_primeWindow.mp hq).1]
  rw [hsum] at h
  have he : sourceSieveCount N d (d * N) z =
      sourceSieveCount N d (d * N) w +
        ∑ q ∈ primeWindow (d * N) z w,
          sourceSieveCount N (d * q) ((d * q) * N) q := by omega
  exact_mod_cast he

/-- Exact finite source Phi recurrence, before any limiting h/H or
admissible-family transport. All prime-window and tuple multiplicities
remain visible. -/
theorem wuBoxPhi_buchstab {i N : ℕ} {δ s t : ℝ} (W : Fin i → Finset ℕ)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 ≤ (N : ℝ) ^ (1 / 2 - δ) / d)
    (hs : 0 < s) (hst : s ≤ t) :
    wuBoxPhi N δ W t = wuBoxPhi N δ W s +
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ q ∈ primeWindow (d * N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          (sourceSieveCount N (d * q) ((d * q) * N) q : ℝ) := by
  unfold wuBoxPhi convolutionSieveCount boxConvolutionSupport
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hcut : wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d s :=
    rpow_le_rpow_of_exponent_le (hQ d hd) (one_div_le_one_div_of_le hs hst)
  rw [source_buchstab_selected_modulus N d hcut, mul_add]

/-- The next sieve has the shifted parameter, with the strict and closed
ends inherited from the actual prime window. -/
theorem buchstab_shifted_parameter {Q q s t : ℝ}
    (hQ : 1 < Q) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hlo : Q ^ (1 / t) ≤ q) (hhi : q < Q ^ (1 / s)) :
    s - 1 < log (Q / q) / log q ∧ log (Q / q) / log q ≤ t - 1 := by
  have hQ0 : 0 < Q := by linarith
  have hq0 : 0 < q := by linarith
  have hlogq : 0 < log q := log_pos hq
  have hl := log_le_log (rpow_pos_of_pos hQ0 _) hlo
  have hu := log_lt_log hq0 hhi
  rw [log_rpow hQ0] at hl hu
  have hlow : log Q / t ≤ log q := by simpa [div_eq_mul_inv, mul_comm] using hl
  have hhigh : log q < log Q / s := by simpa [div_eq_mul_inv, mul_comm] using hu
  have hlt : s < log Q / log q :=
    (lt_div_iff₀ hlogq).mpr (by nlinarith [(lt_div_iff₀ hs).mp hhigh])
  have hle : log Q / log q ≤ t :=
    (div_le_iff₀ hlogq).mpr (by nlinarith [(div_le_iff₀ ht).mp hlow])
  rw [log_div hQ0.ne' hq0.ne', sub_div, div_self hlogq.ne']
  constructor <;> linarith


end Wu2008DoubleSieve
