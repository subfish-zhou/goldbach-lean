import MathlibNt.Wu2008DoubleSieve.SingleUpperHDarboux

namespace Wu2008DoubleSieve.SingleUpperHPrimeQuadrature
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperQuadrature SingleUpperHDarboux
open scoped Classical Topology

/-- Rescaling of the accepted genuine closed-prime quadrature. The weight
may vary after T provided its analytic bounds are fixed before T. -/
theorem rescaled_weighted_uniform {M K ε : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc (1/15 : ℝ) (1/3)) →
      (∀ t ∈ Icc (1/15 : ℝ) (1/3), |f t| ≤ M) →
      (∀ x ∈ Icc (1/15 : ℝ) (1/3), ∀ y ∈ Icc (1/15 : ℝ) (1/3),
        |f x-f y| ≤ K*|x-y|) →
      ∀ a b : ℝ, 1/15 ≤ a → a ≤ b → b ≤ 1/3 →
      |(∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b),
        f (log p/log N)/(p : ℝ)) - ∫ t in a..b, f t/t| < ε := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(2/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (ht.eventually (primeOrdered_weighted_uniform M K ε hM hK hε))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN f hc hbound hlip a b ha hab hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmap (t : ℝ) (ht : t ∈ Icc (1/10 : ℝ) (1/2)) :
      (2/3)*t ∈ Icc (1/15 : ℝ) (1/3) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hcomp := hc.comp (by fun_prop :
    ContinuousOn (fun t : ℝ => (2/3)*t) (Icc (1/10 : ℝ) (1/2))) hmap
  have hlip' : ∀ x ∈ Icc (1/10 : ℝ) (1/2), ∀ y ∈ Icc (1/10 : ℝ) (1/2),
      |f ((2/3)*x)-f ((2/3)*y)| ≤ K*|x-y| := by
    intro x hx y hy
    have h := hlip _ (hmap x hx) _ (hmap y hy)
    rw [← mul_sub,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2/3)] at h
    nlinarith [mul_nonneg hK (abs_nonneg (x-y))]
  have h := hT N ((le_max_right _ _).trans hN) (fun t => f ((2/3)*t))
    (3/2*a) (3/2*b) hcomp (fun t ht => hbound _ (hmap t ht)) hlip'
    (by linarith) (by linarith) (by linarith)
  rw [rescaled_integral] at h
  have he (t : ℝ) : ((N : ℝ)^(2/3 : ℝ))^(3/2*t) = (N : ℝ)^t := by
    rw [← rpow_mul hN0.le,show (2/3 : ℝ)*(3/2*t) = t by ring]
  have htlog (p : ℕ) : (2/3)*(log (p : ℝ)/log ((N : ℝ)^(2/3 : ℝ))) = log p/log N := by
    rw [log_rpow hN0]
    field_simp
  simpa only [primeOrderedClosedSum,he,htlog] using h

/-- Only the reciprocal denominator is Lipschitz. No hypothesis about
regularity of the H coefficient enters the prime quadrature. -/
theorem reciprocal_regular {δ : ℝ} (hδhi : δ ≤ 1/100) :
    ContinuousOn (fun t => 1/((1/2-δ)-t)) (Icc (1/15 : ℝ) (1/3)) ∧
    (∀ t ∈ Icc (1/15 : ℝ) (1/3), |1/((1/2-δ)-t)| ≤ 10) ∧
    (∀ x ∈ Icc (1/15 : ℝ) (1/3), ∀ y ∈ Icc (1/15 : ℝ) (1/3),
      |1/((1/2-δ)-x)-1/((1/2-δ)-y)| ≤ 100*|x-y|) := by
  have hd (t : ℝ) (ht : t ∈ Icc (1/15 : ℝ) (1/3)) : (1/10 : ℝ) ≤ (1/2-δ)-t := by
    linarith [ht.2]
  refine ⟨ContinuousOn.div continuousOn_const (by fun_prop)
    (fun t ht => ne_of_gt (by linarith [hd t ht])),?_,?_⟩
  · intro t ht
    rw [abs_of_pos (div_pos (by norm_num) (by linarith [hd t ht]))]
    exact (div_le_iff₀ (by linarith [hd t ht])).mpr (by linarith [hd t ht])
  · intro x hx y hy
    have hx0 : 0 < (1/2-δ)-x := by linarith [hd x hx]
    have hy0 : 0 < (1/2-δ)-y := by linarith [hd y hy]
    have hp : (1/100 : ℝ) ≤ ((1/2-δ)-x)*((1/2-δ)-y) := by
      have h := mul_le_mul (hd x hx) (hd y hy) (by norm_num) hx0.le
      norm_num at h
      exact h
    have he : 1/((1/2-δ)-x)-1/((1/2-δ)-y) =
        (x-y)/(((1/2-δ)-x)*((1/2-δ)-y)) := by
      rw [div_sub_div _ _ hx0.ne' hy0.ne']
      congr 1
      ring
    rw [he,abs_div,abs_of_pos (mul_pos hx0 hy0)]
    apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 100*|x-y| by positivity)
    nlinarith only [h]

/-- Genuine primes, closed endpoints (also a=b), and the original rational
kernel. The common threshold precedes delta and both endpoints. -/
theorem reciprocal_prime_quadrature {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ δ a b : ℝ,
      δ ≤ 1/100 → 1/15 ≤ a → a ≤ b → b ≤ 1/3 →
      |(∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b),
        1/((p : ℝ)*((1/2-δ)-log p/log N))) -
        ∫ t in a..b, (t*((1/2-δ)-t))⁻¹| < ε := by
  obtain ⟨T,hT4,hT⟩ := rescaled_weighted_uniform
    (by norm_num : (0 : ℝ) ≤ 10) (by norm_num : (0 : ℝ) ≤ 100) hε
  refine ⟨T,hT4,?_⟩
  intro N hN δ a b hδhi ha hab hb
  have hreg := reciprocal_regular hδhi
  have h := hT N hN _ hreg.1 hreg.2.1 hreg.2.2 a b ha hab hb
  simpa only [one_div,div_eq_mul_inv,mul_inv_rev,mul_comm,one_mul] using h

/-- A fixed finite collection of coarse cells is paid together. The error
uses its fixed total coefficient mass, never the N-dependent fine-cell count. -/
theorem finite_coarse_prime_quadrature {ι : Type*} (S : Finset ι) (C : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ δ : ℝ, δ ≤ 1/100 →
      ∀ a b : ι → ℝ, (∀ i ∈ S, 1/15 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1/3) →
      |(∑ i ∈ S, C i * ∑ p ∈ primesIcc ((N : ℝ)^(a i)) ((N : ℝ)^(b i)),
          1/((p : ℝ)*((1/2-δ)-log p/log N))) -
        (∑ i ∈ S, C i * ∫ t in a i..b i, (t*((1/2-δ)-t))⁻¹)| < ε := by
  let M := ∑ i ∈ S, |C i|
  have hM : 0 ≤ M := sum_nonneg (fun _ _ => abs_nonneg _)
  let e := ε/(M+1)
  have he : 0 < e := div_pos hε (by linarith)
  obtain ⟨T,hT4,hT⟩ := reciprocal_prime_quadrature he
  refine ⟨T,hT4,?_⟩
  intro N hN δ hδhi a b hab
  have hbound : |(∑ i ∈ S, C i * ∑ p ∈ primesIcc ((N : ℝ)^(a i)) ((N : ℝ)^(b i)),
          1/((p : ℝ)*((1/2-δ)-log p/log N))) -
        (∑ i ∈ S, C i * ∫ t in a i..b i, (t*((1/2-δ)-t))⁻¹)| ≤ M*e := by
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ S, |C i| * e := by
        apply sum_le_sum
        intro i hi
        rw [← mul_sub,abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hT N hN δ _ _ hδhi (hab i hi).1 (hab i hi).2.1 (hab i hi).2.2).le
          (abs_nonneg _)
      _ = M*e := (sum_mul _ _ _).symm
  refine hbound.trans_lt ?_
  have heq : (M+1)*e = ε := by dsimp [e]; field_simp
  nlinarith only [he,heq]

end Wu2008DoubleSieve.SingleUpperHPrimeQuadrature
