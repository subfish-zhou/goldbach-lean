import MathlibNt.Wu2008DoubleSieve.ReboxingSorted

/-!
# Exact local normalization in the inserted prime

Wu04 between (3.15) and (3.16). The windows exclude primes dividing N,
but not primes dividing d. The latter have local multiplier 1/p rather
than 1/(p-2); all statements below retain this distinction.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical
open MathlibNt.SieveTheory.SingularSeries

theorem wuSingularSeries_mul_prime_of_dvd {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpd : p ∣ n) :
    wuSingularSeries (p * n) = wuSingularSeries n := by
  rw [wuSingularSeries_eq_liu _ (Nat.mul_pos hp.pos hn), wuSingularSeries_eq_liu _ hn]
  rw [liuSingularSeries_source_formula, liuSingularSeries_source_formula]
  have hf : (p * n).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hn.ne', hp.primeFactors,
      singleton_union, insert_eq_of_mem (Nat.mem_primeFactors.mpr ⟨hp, hpd, hn.ne'⟩)]
  rw [hf]

theorem wuSingularSeries_mul_prime_of_not_dvd {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hp2 : 2 < p) (hpd : ¬p ∣ n) :
    wuSingularSeries (p * n) =
      wuSingularSeries n * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  rw [wuSingularSeries_eq_liu _ (Nat.mul_pos hp.pos hn), wuSingularSeries_eq_liu _ hn]
  rw [liuSingularSeries_source_formula, liuSingularSeries_source_formula]
  rw [Nat.primeFactors_mul hp.ne_zero hn.ne', hp.primeFactors, singleton_union,
    filter_insert, if_pos hp2, prod_insert]
  · ring
  · simp [Nat.mem_primeFactors, hpd]

/-- Exact C(dpN)/phi(dp), including repeated primes of the convolution. -/
theorem wu_inserted_arithmetic_weight {N d p : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hp : p.Prime) (hp2 : 2 < p) (hpN : p.Coprime N) :
    wuSingularSeries ((d * p) * N) / (Nat.totient (d * p) : ℝ) =
      (wuSingularSeries (d * N) / (Nat.totient d : ℝ)) *
        (if p ∣ d then 1 / (p : ℝ) else 1 / ((p : ℝ) - 2)) := by
  have ht : (Nat.totient d : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpr : (2 : ℝ) < p := by exact_mod_cast hp2
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2' : (p : ℝ) - 2 ≠ 0 := by linarith
  rw [show (d * p) * N = p * (d * N) by ring, show d * p = p * d by ring]
  by_cases hpd : p ∣ d
  · rw [if_pos hpd, wuSingularSeries_mul_prime_of_dvd (Nat.mul_pos hd hN) hp
      (hpd.trans (dvd_mul_right d N)), Nat.totient_mul_of_prime_of_dvd hp hpd,
      Nat.cast_mul]
    ring
  · have hpNd : ¬p ∣ d * N := by
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact hpd h
      · exact (hp.coprime_iff_not_dvd.mp hpN) h
    rw [if_neg hpd, wuSingularSeries_mul_prime_of_not_dvd (Nat.mul_pos hd hN) hp hp2 hpNd,
      Nat.totient_mul_of_prime_of_not_dvd hp hpd, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    field_simp

theorem wu_inserted_arithmetic_weight_le {N d p : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hp : p.Prime) (hp2 : 2 < p) (hpN : p.Coprime N) :
    wuSingularSeries ((d * p) * N) / (Nat.totient (d * p) : ℝ) ≤
      (wuSingularSeries (d * N) / (Nat.totient d : ℝ)) / ((p : ℝ) - 2) := by
  rw [wu_inserted_arithmetic_weight hN hd hp hp2 hpN, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left
  · split_ifs
    · have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
      simpa only [one_div] using one_div_le_one_div_of_le
        (by linarith : 0 < (p : ℝ) - 2) (by linarith : (p : ℝ) - 2 ≤ p)
    · simp
  · exact div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos hd hN)).le (Nat.cast_nonneg _)

/-- The complete discrepancy is supported only on the repeated-prime lane. -/
theorem wu_inserted_arithmetic_weight_defect {N d p : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hp : p.Prime) (hp2 : 2 < p) (hpN : p.Coprime N) :
    (wuSingularSeries (d * N) / (Nat.totient d : ℝ)) / ((p : ℝ) - 2) -
        wuSingularSeries ((d * p) * N) / (Nat.totient (d * p) : ℝ) =
      if p ∣ d then
        (wuSingularSeries (d * N) / (Nat.totient d : ℝ)) *
          (2 / ((p : ℝ) * ((p : ℝ) - 2)))
      else 0 := by
  rw [wu_inserted_arithmetic_weight hN hd hp hp2 hpN]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpr : (2 : ℝ) < p := by exact_mod_cast hp2
  have hp2' : (p : ℝ) - 2 ≠ 0 := by linarith
  split_ifs <;> field_simp <;> ring

theorem reboxing_log_denominator {q p : ℝ} (hq : 1 < q) (hp : 0 < p) :
    log (q / p) = log q * (1 - log p / log q) := by
  rw [log_div (by linarith : q ≠ 0) hp.ne']
  have hl : log q ≠ 0 := (log_pos hq).ne'
  field_simp

/-- The exact prime atom of Theta, with the repeated-prime multiplier. -/
theorem wu_inserted_theta_weight {N d p : ℕ} {Q : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hp : p.Prime) (hp2 : 2 < p) (hpN : p.Coprime N)
    (hQ : 1 < Q / d) :
    wuSingularSeries ((d * p) * N) /
        ((Nat.totient (d * p) : ℝ) * log (Q / (d * p))) =
      (wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))) *
        ((if p ∣ d then 1 / (p : ℝ) else 1 / ((p : ℝ) - 2)) /
          (1 - log (p : ℝ) / log (Q / d))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [show Q / ((d : ℝ) * p) = (Q / d) / p by ring,
    reboxing_log_denominator hQ hp0]
  rw [← div_div, wu_inserted_arithmetic_weight hN hd hp hp2 hpN]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact double-sum regrouping of an inserted window, with the original
ordered-tuple multiplicities and no squarefreeness assumption. -/
theorem boxConvolution_sum_cons {i : ℕ} (P : Finset ℕ) (W : Fin i → Finset ℕ)
    (f : ℕ → ℝ) :
    (∑ m ∈ boxConvolutionSupport (Fin.cons P W),
        (convolutionCoeff (Fin.cons P W) m : ℝ) * f m) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ P, f (d * p) := by
  rw [boxConvolution_sum_fibres, boxConvolution_sum_fibres]
  have hset :
      Fintype.piFinset (Fin.cons P W) =
        (P ×ˢ Fintype.piFinset W).map
          (Fin.consEquiv (fun _ : Fin (i + 1) => ℕ)).toEmbedding := by
    simpa using filter_piFinset_eq_map_consEquiv
      (α := fun _ : Fin (i + 1) => ℕ) (Fin.cons P W) (fun _ => True)
  rw [hset, sum_map, sum_product, sum_comm]
  simp only [Equiv.toEmbedding_apply, Fin.consEquiv_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Nat.mul_comm]

theorem boxTheta_cons {i : ℕ} (N : ℕ) (Q : ℝ) (P : Finset ℕ) (W : Fin i → Finset ℕ) :
    boxTheta N Q (Fin.cons P W) =
      4 * AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N *
        ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ P, wuSingularSeries ((d * p) * N) /
            ((Nat.totient (d * p) : ℝ) * log (Q / (d * p))) := by
  unfold boxTheta
  simp only [mul_div_assoc]
  rw [boxConvolution_sum_cons]
  simp only [Nat.cast_mul]

theorem wuBoxPhi_cons {i : ℕ} (N : ℕ) (δ s : ℝ) (P : Finset ℕ) (W : Fin i → Finset ℕ) :
    wuBoxPhi N δ (Fin.cons P W) s =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ P, (sourceSieveCount N (d * p) ((d * p) * N)
          (wuLocalCutoff N δ (d * p) s) : ℝ) := by
  exact boxConvolution_sum_cons P W _

end Wu2008DoubleSieve
