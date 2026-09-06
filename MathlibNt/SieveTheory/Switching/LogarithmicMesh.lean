import MathlibNt.SieveTheory.Switching.SuzukiPrimeSums

/-!
# Logarithmic meshes and local prime-mass bounds

Atomic prime bounds and logarithmic partitions lead to fixed-depth Rosser
meshes, Darboux estimates, and compact logarithmic coordinate boxes.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- The local-product hypothesis controls each normalized prime density by
applying it to the unit interval containing that prime.  This is the atomic
estimate needed when the Rosser path expansion is summed prime by prime. -/
theorem nu_div_one_sub_le_of_dimensionOneLocalProductBound
    {S : BoundingSieve} {K : ℝ} {q : ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hq : q ∈ S.prodPrimes.primeFactors) :
    S.nu q / (1 - S.nu q) ≤
      Real.log ((q : ℝ) + 1) / Real.log q *
          (1 + K / Real.log q) - 1 := by
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hinterval :
      S.prodPrimes.primeFactors.filter
          (fun p : ℕ => (q : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (q : ℝ) + 1) =
        {q} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hpLower, hpUpper⟩
      have hpq : q ≤ p := by exact_mod_cast hpLower
      have hpq' : p < q + 1 := by exact_mod_cast hpUpper
      omega
    · rintro rfl
      exact ⟨hq, le_rfl, by norm_num⟩
  have hbound := hlocal (q : ℝ) ((q : ℝ) + 1)
    (by exact_mod_cast hqPrime.two_le) (by norm_num)
  rw [hinterval] at hbound
  simp only [Finset.prod_singleton] at hbound
  have hden : 1 - S.nu q ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime q hqPrime
      ((Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hq).2))
  calc
    S.nu q / (1 - S.nu q) = (1 - S.nu q)⁻¹ - 1 := by
      field_simp
      ring
    _ ≤ Real.log ((q : ℝ) + 1) / Real.log q *
          (1 + K / Real.log q) - 1 := sub_le_sub_right hbound 1

/-- Quantitative atomic form of the local-product estimate.  The normalized
density at one prime is bounded by the logarithmic unit-cell width plus its
interaction with the dimension-one error.  In particular, atoms vanish
uniformly when the prime and its logarithm tend to infinity. -/
theorem nu_div_one_sub_le_atomic_log_error
    {S : BoundingSieve} {K : ℝ} {q : ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hK : 0 ≤ K)
    (hq : q ∈ S.prodPrimes.primeFactors) :
    S.nu q / (1 - S.nu q) ≤
      1 / ((q : ℝ) * Real.log q) +
        (1 + 1 / ((q : ℝ) * Real.log q)) * (K / Real.log q) := by
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hqone : (1 : ℝ) < q := by exact_mod_cast hqPrime.one_lt
  have hlogq : 0 < Real.log q := Real.log_pos hqone
  have hlogstep :
      Real.log ((q : ℝ) + 1) - Real.log q ≤ 1 / (q : ℝ) := by
    rw [← Real.log_div (by positivity) hqpos.ne']
    calc
      Real.log (((q : ℝ) + 1) / q) =
          Real.log (1 + 1 / (q : ℝ)) := by
        congr 1
        field_simp [hqpos.ne']
      _ ≤ (1 + 1 / (q : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (q : ℝ) := by ring
  have hratio :
      Real.log ((q : ℝ) + 1) / Real.log q ≤
        1 + 1 / ((q : ℝ) * Real.log q) := by
    apply (div_le_iff₀ hlogq).2
    calc
      Real.log ((q : ℝ) + 1) ≤ Real.log q + 1 / (q : ℝ) := by
        linarith
      _ = (1 + 1 / ((q : ℝ) * Real.log q)) * Real.log q := by
        field_simp [hqpos.ne', hlogq.ne']
  calc
    S.nu q / (1 - S.nu q) ≤
        Real.log ((q : ℝ) + 1) / Real.log q *
            (1 + K / Real.log q) - 1 :=
      nu_div_one_sub_le_of_dimensionOneLocalProductBound hlocal hq
    _ ≤ (1 + 1 / ((q : ℝ) * Real.log q)) *
          (1 + K / Real.log q) - 1 := by
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_right hratio
          (add_nonneg zero_le_one (div_nonneg hK hlogq.le))) 1
    _ = 1 / ((q : ℝ) * Real.log q) +
          (1 + 1 / ((q : ℝ) * Real.log q)) *
            (K / Real.log q) := by ring

/-- The dimension-one bound also controls any subproduct lying in the same
real prime interval.  Positivity of the sieve density makes every omitted
inverse Euler factor at least one. -/
theorem prod_inv_one_sub_nu_le_of_subset_interval
    {S : BoundingSieve} {K z₁ z₂ : ℝ} {T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    ∏ p ∈ T, (1 - S.nu p)⁻¹ ≤
      Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := by
  let I := S.prodPrimes.primeFactors.filter
    (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hTI : T ⊆ I := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hT hp, hinterval p hp⟩
  calc
    ∏ p ∈ T, (1 - S.nu p)⁻¹ ≤ ∏ p ∈ I, (1 - S.nu p)⁻¹ := by
      apply Finset.prod_le_prod_of_subset_of_one_le hTI
      · intro p hp
        have hp' : p ∈ S.prodPrimes.primeFactors := hT hp
        have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'
        have hpdvd : p ∣ S.prodPrimes :=
          (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp' |>.2
        exact inv_nonneg.mpr
          (sub_nonneg.mpr (S.nu_lt_one_of_prime p hpPrime hpdvd).le)
      intro p hpI hpT
      have hp : p ∈ S.prodPrimes.primeFactors :=
        (Finset.mem_filter.mp hpI).1
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ S.prodPrimes :=
        (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
      have hnuPos : 0 < S.nu p := S.nu_pos_of_prime p hpPrime hpdvd
      have hdenPos : 0 < 1 - S.nu p :=
        sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpdvd)
      exact (one_le_inv₀ hdenPos).2 (by linarith)
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) :=
      hlocal z₁ z₂ hz₁ hz₁₂

/-- Every normalized local density appearing in a Rosser chain is nonnegative. -/
theorem nu_div_one_sub_nonneg_of_mem
    {S : BoundingSieve} {p : ℕ} (hp : p ∈ S.prodPrimes.primeFactors) :
    0 ≤ S.nu p / (1 - S.nu p) := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ S.prodPrimes :=
    (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
  exact div_nonneg (S.nu_pos_of_prime p hpPrime hpdvd).le
    (sub_nonneg.mpr (S.nu_lt_one_of_prime p hpPrime hpdvd).le)

/-- The linear part of a finite product of nonnegative Euler increments is
bounded by the full product. -/
theorem one_add_sum_le_prod_one_add
    {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ T, 0 ≤ f i) :
    1 + ∑ i ∈ T, f i ≤ ∏ i ∈ T, (1 + f i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a T)
      have hsum : 0 ≤ ∑ i ∈ T, f i :=
        Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
      calc
        1 + (f a + ∑ i ∈ T, f i) ≤
            (1 + f a) * (1 + ∑ i ∈ T, f i) := by nlinarith
        _ ≤ (1 + f a) * ∏ i ∈ T, (1 + f i) := by
          apply mul_le_mul_of_nonneg_left
          · exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
          · linarith

/-- Stieltjes mass bound extracted from the dimension-one Euler-product
hypothesis.  This is the interval atom used by logarithmic partitions: no
individual estimate for the primes in `T` is required. -/
theorem sum_nu_div_one_sub_le_of_subset_interval
    {S : BoundingSieve} {K z₁ z₂ : ℝ} {T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    ∑ p ∈ T, S.nu p / (1 - S.nu p) ≤
      Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) - 1 := by
  have hnonneg : ∀ p ∈ T, 0 ≤ S.nu p / (1 - S.nu p) :=
    fun p hp => nu_div_one_sub_nonneg_of_mem (hT hp)
  have hsum := one_add_sum_le_prod_one_add T
    (fun p => S.nu p / (1 - S.nu p)) hnonneg
  have hprod :
      (∏ p ∈ T, (1 + S.nu p / (1 - S.nu p))) =
        ∏ p ∈ T, (1 - S.nu p)⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp' : p ∈ S.prodPrimes.primeFactors := hT hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'
    have hpdvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp' |>.2
    have hden : 1 - S.nu p ≠ 0 :=
      ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpdvd))
    field_simp [hden]
    ring
  rw [hprod] at hsum
  have hbound := prod_inv_one_sub_nu_le_of_subset_interval
    hlocal hz₁ hz₁₂ hT hinterval
  linarith

/-- Quantitative mesh form of the Stieltjes mass bound.  If both the logarithmic
width and the local-product error are at most `η`, the normalized density mass
of the cell is at most `2η + η²`. -/
theorem sum_nu_div_one_sub_le_of_log_mesh
    {S : BoundingSieve} {K z₁ z₂ η : ℝ} {T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
    (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hmesh : Real.log z₂ / Real.log z₁ ≤ 1 + η)
    (herror : K / Real.log z₁ ≤ η) :
    ∑ p ∈ T, S.nu p / (1 - S.nu p) ≤ 2 * η + η ^ 2 := by
  have hlog₁ : 0 < Real.log z₁ := Real.log_pos (by linarith)
  have hlog₂ : 0 ≤ Real.log z₂ :=
    Real.log_nonneg (by linarith)
  have hcorrection : 0 ≤ 1 + K / Real.log z₁ :=
    add_nonneg zero_le_one (div_nonneg hK hlog₁.le)
  have hproduct :
      Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) ≤
        (1 + η) * (1 + η) := by
    calc
      Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) ≤
          (1 + η) * (1 + K / Real.log z₁) :=
        mul_le_mul_of_nonneg_right hmesh hcorrection
      _ ≤ (1 + η) * (1 + η) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · linarith
  calc
    ∑ p ∈ T, S.nu p / (1 - S.nu p) ≤
        Real.log z₂ / Real.log z₁ *
          (1 + K / Real.log z₁) - 1 :=
      sum_nu_div_one_sub_le_of_subset_interval
        hlocal hz₁ hz₁₂ hT hinterval
    _ ≤ (1 + η) * (1 + η) - 1 := sub_le_sub_right hproduct 1
    _ = 2 * η + η ^ 2 := by ring

/-- Logarithmic-coordinate form of the interval mass estimate.  On the cell
`[z^a, z^b)`, the main local-product increment is exactly `b / a`; this is the
form used in the Rosser-chain Riemann sums. -/
theorem sum_nu_div_one_sub_le_of_rpow_interval
    {S : BoundingSieve} {K z a b : ℝ} {T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (ha : 0 < a) (hab : a ≤ b)
    (hza : 2 ≤ z ^ a)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z ^ a ≤ (p : ℝ) ∧ (p : ℝ) < z ^ b) :
    ∑ p ∈ T, S.nu p / (1 - S.nu p) ≤
      b / a * (1 + K / (a * Real.log z)) - 1 := by
  have hzpos : 0 < z := by linarith
  have hlogz : Real.log z ≠ 0 := (Real.log_pos hz).ne'
  have habratio : b * Real.log z / (a * Real.log z) = b / a := by
    field_simp [ha.ne', hlogz]
  have hbound := sum_nu_div_one_sub_le_of_subset_interval
    hlocal hza (Real.rpow_le_rpow_of_exponent_le hz.le hab) hT hinterval
  rw [Real.log_rpow hzpos, Real.log_rpow hzpos, habratio] at hbound
  exact hbound

/-- Upper Darboux-sum form of the local-product estimate.  A nonnegative weight
bounded by `M` on one prime interval costs at most `M` times that interval's
Stieltjes mass. -/
theorem weighted_sum_nu_div_one_sub_le_of_subset_interval
    {S : BoundingSieve} {K z₁ z₂ M : ℝ} {T : Finset ℕ} {w : ℕ → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
    (hM : 0 ≤ M) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M) :
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
      M * (Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) - 1) := by
  calc
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
        ∑ p ∈ T, M * (S.nu p / (1 - S.nu p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (hw p hp).2
        (nu_div_one_sub_nonneg_of_mem (hT hp))
    _ = M * ∑ p ∈ T, S.nu p / (1 - S.nu p) := by
      rw [Finset.mul_sum]
    _ ≤ M * (Real.log z₂ / Real.log z₁ *
        (1 + K / Real.log z₁) - 1) := by
      exact mul_le_mul_of_nonneg_left
        (sum_nu_div_one_sub_le_of_subset_interval
          hlocal hz₁ hz₁₂ hT hinterval) hM

/-- Weighted logarithmic-coordinate cell estimate.  This is the direct
Darboux-sum input for a continuous Rosser-chain integrand on `[z^a, z^b)`. -/
theorem weighted_sum_nu_div_one_sub_le_of_rpow_interval
    {S : BoundingSieve} {K z a b M : ℝ} {T : Finset ℕ} {w : ℕ → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (ha : 0 < a) (hab : a ≤ b)
    (hza : 2 ≤ z ^ a)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z ^ a ≤ (p : ℝ) ∧ (p : ℝ) < z ^ b)
    (hM : 0 ≤ M) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M) :
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
      M * (b / a * (1 + K / (a * Real.log z)) - 1) := by
  have hzpos : 0 < z := by linarith
  have hlogz : Real.log z ≠ 0 := (Real.log_pos hz).ne'
  have habratio : b * Real.log z / (a * Real.log z) = b / a := by
    field_simp [ha.ne', hlogz]
  have hbound := weighted_sum_nu_div_one_sub_le_of_subset_interval
    hlocal hza (Real.rpow_le_rpow_of_exponent_le hz.le hab)
    hT hinterval hM hw
  rw [Real.log_rpow hzpos, Real.log_rpow hzpos, habratio] at hbound
  exact hbound

/-- Weighted logarithmic-coordinate cell estimate with a closed right endpoint.
The strict part is controlled by the local-product interval estimate, while the
unique possible prime on the right face is charged to the atomic error `η`. -/
theorem weighted_sum_nu_div_one_sub_le_of_rpow_Icc_add_atom
    {S : BoundingSieve} {K z a b M η : ℝ} {T : Finset ℕ} {w : ℕ → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (ha : 0 < a) (hab : a ≤ b)
    (hza : 2 ≤ z ^ a)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T, z ^ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ z ^ b)
    (hM : 0 ≤ M) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M)
    (hη : 0 ≤ η)
    (hatom : ∀ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤ η) :
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
      M * (b / a * (1 + K / (a * Real.log z)) - 1) + η := by
  let U := T.filter (fun p : ℕ => (p : ℝ) < z ^ b)
  let E := T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ b)
  have hU :
      ∑ p ∈ U, w p * (S.nu p / (1 - S.nu p)) ≤
        M * (b / a * (1 + K / (a * Real.log z)) - 1) := by
    apply weighted_sum_nu_div_one_sub_le_of_rpow_interval
      hlocal hz ha hab hza
    · intro p hp
      exact hT (Finset.mem_filter.mp hp).1
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact ⟨(hinterval p hp'.1).1, hp'.2⟩
    · exact hM
    · intro p hp
      exact hw p (Finset.mem_filter.mp hp).1
  have hEcard : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hpe : (p : ℝ) = z ^ b :=
      le_antisymm (hinterval p hp'.1).2 (le_of_not_gt hp'.2)
    have hqe : (q : ℝ) = z ^ b :=
      le_antisymm (hinterval q hq'.1).2 (le_of_not_gt hq'.2)
    exact_mod_cast hpe.trans hqe.symm
  have hE :
      ∑ p ∈ E, w p * (S.nu p / (1 - S.nu p)) ≤ η := by
    calc
      ∑ p ∈ E, w p * (S.nu p / (1 - S.nu p)) ≤ E.card • η :=
        Finset.sum_le_card_nsmul E _ η (fun p hp =>
          hatom p (Finset.mem_filter.mp hp).1)
      _ ≤ 1 • η := nsmul_le_nsmul_left hη hEcard
      _ = η := by simp
  rw [← Finset.sum_filter_add_sum_filter_not T
    (fun p : ℕ => (p : ℝ) < z ^ b)
    (fun p => w p * (S.nu p / (1 - S.nu p)))]
  exact add_le_add hU hE

/-- Finite upper-sum principle for the normalized density measure.  Assigning
each prime to a real interval reduces a weighted prime sum to the corresponding
sum of local-product increments.  Geometric logarithmic meshes are obtained by
taking `lo i` and `hi i` to be consecutive powers of the global cutoff. -/
theorem weighted_sum_nu_div_one_sub_le_partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : BoundingSieve} {K : ℝ} {T : Finset ℕ}
    {cell : ℕ → ι} {lo hi M : ι → ℝ} {w : ℕ → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hlo : ∀ i, 2 ≤ lo i) (hlohi : ∀ i, lo i ≤ hi i)
    (hinterval : ∀ p ∈ T, lo (cell p) ≤ (p : ℝ) ∧ (p : ℝ) < hi (cell p))
    (hM : ∀ i, 0 ≤ M i)
    (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M (cell p)) :
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
      ∑ i, M i *
        (Real.log (hi i) / Real.log (lo i) *
          (1 + K / Real.log (lo i)) - 1) := by
  rw [← Finset.sum_fiberwise T cell
    (fun p => w p * (S.nu p / (1 - S.nu p)))]
  apply Finset.sum_le_sum
  intro i hi_mem
  apply weighted_sum_nu_div_one_sub_le_of_subset_interval
    hlocal (hlo i) (hlohi i)
  · intro p hp
    exact hT (Finset.mem_filter.mp hp).1
  · intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hcell := (Finset.mem_filter.mp hp).2
    simpa [hcell] using hinterval p hpT
  · exact hM i
  · intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hcell := (Finset.mem_filter.mp hp).2
    simpa [hcell] using hw p hpT

/-- Finite logarithmic-coordinate upper sum.  Each cell is an interval
`[z^(a i), z^(b i))`, so its local-product increment has the explicit
Riemann-sum form `b i / a i - 1`, together with the vanishing `K / log z`
correction. -/
theorem weighted_sum_nu_div_one_sub_le_rpow_partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : BoundingSieve} {K z : ℝ} {T : Finset ℕ}
    {cell : ℕ → ι} {a b M : ι → ℝ} {w : ℕ → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i)
    (hza : ∀ i, 2 ≤ z ^ (a i))
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T,
      z ^ (a (cell p)) ≤ (p : ℝ) ∧ (p : ℝ) < z ^ (b (cell p)))
    (hM : ∀ i, 0 ≤ M i)
    (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M (cell p)) :
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
      ∑ i, M i *
        (b i / a i * (1 + K / (a i * Real.log z)) - 1) := by
  rw [← Finset.sum_fiberwise T cell
    (fun p => w p * (S.nu p / (1 - S.nu p)))]
  apply Finset.sum_le_sum
  intro i hi_mem
  apply weighted_sum_nu_div_one_sub_le_of_rpow_interval
    hlocal hz (ha i) (hab i) (hza i)
  · intro p hp
    exact hT (Finset.mem_filter.mp hp).1
  · intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hcell := (Finset.mem_filter.mp hp).2
    simpa [hcell] using hinterval p hpT
  · exact hM i
  · intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hcell := (Finset.mem_filter.mp hp).2
    simpa [hcell] using hw p hpT

/-- Finite logarithmic-coordinate upper sum with closed right faces.  Every cell
has at most one prime on its right face, and `η i` pays for that atom instead of
discarding the equality case. -/
theorem weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add_atoms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : BoundingSieve} {K z : ℝ} {T : Finset ℕ}
    {cell : ℕ → ι} {a b M η : ι → ℝ} {w : ℕ → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i)
    (hza : ∀ i, 2 ≤ z ^ (a i))
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T,
      z ^ (a (cell p)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z ^ (b (cell p)))
    (hM : ∀ i, 0 ≤ M i)
    (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M (cell p))
    (hη : ∀ i, 0 ≤ η i)
    (hatom : ∀ p ∈ T,
      w p * (S.nu p / (1 - S.nu p)) ≤ η (cell p)) :
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
      ∑ i, (M i *
        (b i / a i * (1 + K / (a i * Real.log z)) - 1) + η i) := by
  rw [← Finset.sum_fiberwise T cell
    (fun p => w p * (S.nu p / (1 - S.nu p)))]
  apply Finset.sum_le_sum
  intro i hi_mem
  apply weighted_sum_nu_div_one_sub_le_of_rpow_Icc_add_atom
    hlocal hz (ha i) (hab i) (hza i)
  · intro p hp
    exact hT (Finset.mem_filter.mp hp).1
  · intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hcell := (Finset.mem_filter.mp hp).2
    simpa [hcell] using hinterval p hpT
  · exact hM i
  · intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hcell := (Finset.mem_filter.mp hp).2
    simpa [hcell] using hw p hpT
  · exact hη i
  · intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hcell := (Finset.mem_filter.mp hp).2
    simpa [hcell] using hatom p hpT

/-- Closed logarithmic cells with a single global budget for all right-face
atoms.  Splitting off the union of the closed faces before applying the
half-open partition estimate prevents an error proportional to the number of
mesh cells. -/
theorem weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add_global_atoms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : BoundingSieve} {K z η : ℝ} {T : Finset ℕ}
    {cell : ℕ → ι} {a b M : ι → ℝ} {w : ℕ → ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i)
    (hza : ∀ i, 2 ≤ z ^ (a i))
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hinterval : ∀ p ∈ T,
      z ^ (a (cell p)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z ^ (b (cell p)))
    (hM : ∀ i, 0 ≤ M i)
    (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M (cell p))
    (hatom :
      ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (b (cell p))),
          w p * (S.nu p / (1 - S.nu p)) ≤ η) :
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
      (∑ i, M i *
        (b i / a i * (1 + K / (a i * Real.log z)) - 1)) + η := by
  have hopen :
      ∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) < z ^ (b (cell p))),
          w p * (S.nu p / (1 - S.nu p)) ≤
        ∑ i, M i *
          (b i / a i * (1 + K / (a i * Real.log z)) - 1) := by
    apply weighted_sum_nu_div_one_sub_le_rpow_partition
      hlocal hz ha hab hza
    · intro p hp
      exact hT (Finset.mem_filter.mp hp).1
    · intro p hp
      have hpT := (Finset.mem_filter.mp hp).1
      exact ⟨(hinterval p hpT).1, (Finset.mem_filter.mp hp).2⟩
    · exact hM
    · intro p hp
      exact hw p (Finset.mem_filter.mp hp).1
  rw [← Finset.sum_filter_add_sum_filter_not T
    (fun p : ℕ => (p : ℝ) < z ^ (b (cell p)))
    (fun p => w p * (S.nu p / (1 - S.nu p)))]
  exact add_le_add hopen hatom

/-! ### A fixed logarithmic mesh on the screened depth-two interval -/

/-- The mesh width of the uniform `m + 1`-cell partition of `[1 / 6, 1]`. -/
noncomputable def upperRosserDepthTwoMeshWidth (m : ℕ) : ℝ :=
  (5 / 6 : ℝ) / (m + 1)

/-- The left endpoint of a cell in the uniform partition of `[1 / 6, 1]`. -/
noncomputable def upperRosserDepthTwoMeshLeft (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  1 / 6 + (i : ℝ) * upperRosserDepthTwoMeshWidth m

/-- The right endpoint of a cell in the uniform partition of `[1 / 6, 1]`. -/
noncomputable def upperRosserDepthTwoMeshRight (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  upperRosserDepthTwoMeshLeft m i + upperRosserDepthTwoMeshWidth m

/-- The (clamped) cell containing a screened logarithmic coordinate. -/
noncomputable def upperRosserDepthTwoMeshCell (m : ℕ) (x : ℝ) : Fin (m + 1) :=
  ⟨min (Nat.floor ((x - 1 / 6) / upperRosserDepthTwoMeshWidth m)) m,
    Nat.lt_succ_iff.mpr (min_le_right _ _)⟩

theorem upperRosserDepthTwoMeshWidth_pos (m : ℕ) :
    0 < upperRosserDepthTwoMeshWidth m := by
  unfold upperRosserDepthTwoMeshWidth
  exact div_pos (by norm_num) (by positivity)

theorem upperRosserDepthTwoMeshLeft_pos (m : ℕ) (i : Fin (m + 1)) :
    0 < upperRosserDepthTwoMeshLeft m i := by
  unfold upperRosserDepthTwoMeshLeft
  have hi : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hh := upperRosserDepthTwoMeshWidth_pos m
  nlinarith

theorem upperRosserDepthTwoMeshLeft_le_right (m : ℕ) (i : Fin (m + 1)) :
    upperRosserDepthTwoMeshLeft m i ≤ upperRosserDepthTwoMeshRight m i := by
  unfold upperRosserDepthTwoMeshRight
  exact le_add_of_nonneg_right (upperRosserDepthTwoMeshWidth_pos m).le

theorem upperRosserDepthTwoMeshRight_le_one (m : ℕ) (i : Fin (m + 1)) :
    upperRosserDepthTwoMeshRight m i ≤ 1 := by
  unfold upperRosserDepthTwoMeshRight upperRosserDepthTwoMeshLeft
    upperRosserDepthTwoMeshWidth
  have hi : (i : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_iff.mpr i.isLt
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  calc
    1 / 6 + (i : ℝ) * ((5 / 6 : ℝ) / (m + 1)) +
          (5 / 6 : ℝ) / (m + 1) =
        1 / 6 + ((i : ℝ) + 1) * ((5 / 6 : ℝ) / (m + 1)) := by ring
    _ ≤ 1 / 6 + ((m : ℝ) + 1) * ((5 / 6 : ℝ) / (m + 1)) := by
      gcongr
    _ = 1 := by
      field_simp
      norm_num

theorem upperRosserDepthTwoMeshRight_last (m : ℕ) :
    upperRosserDepthTwoMeshRight m (Fin.last m) = 1 := by
  unfold upperRosserDepthTwoMeshRight upperRosserDepthTwoMeshLeft
    upperRosserDepthTwoMeshWidth
  simp only [Fin.val_last]
  field_simp
  ring

theorem upperRosserDepthTwoMeshCell_bounds
    (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (1 / 6 : ℝ) 1) :
    upperRosserDepthTwoMeshLeft m (upperRosserDepthTwoMeshCell m x) ≤ x ∧
      x ≤ upperRosserDepthTwoMeshRight m (upperRosserDepthTwoMeshCell m x) := by
  let h := upperRosserDepthTwoMeshWidth m
  let y := (x - 1 / 6) / h
  let n := Nat.floor y
  have hh : 0 < h := upperRosserDepthTwoMeshWidth_pos m
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx.1) hh.le
  have hyn : y ≤ (m : ℝ) + 1 := by
    apply (div_le_iff₀ hh).2
    dsimp [h, upperRosserDepthTwoMeshWidth]
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have heq :
        ((m : ℝ) + 1) * ((5 / 6 : ℝ) / ((m : ℝ) + 1)) = 5 / 6 := by
      field_simp
    rw [heq]
    linarith [hx.2]
  have hfloor : (n : ℝ) ≤ y := Nat.floor_le hy0
  have hyfloor : y < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one y
  by_cases hnm : n ≤ m
  · have hcell : upperRosserDepthTwoMeshCell m x = ⟨n, Nat.lt_succ_iff.mpr hnm⟩ := by
      apply Fin.ext
      change min n m = n
      exact min_eq_left hnm
    rw [hcell]
    constructor
    · unfold upperRosserDepthTwoMeshLeft
      rw [show upperRosserDepthTwoMeshWidth m = h by rfl]
      have hmul := (le_div_iff₀ hh).1 hfloor
      simpa using (show 1 / 6 + (n : ℝ) * h ≤ x by linarith)
    · unfold upperRosserDepthTwoMeshRight upperRosserDepthTwoMeshLeft
      rw [show upperRosserDepthTwoMeshWidth m = h by rfl]
      have hmul := (div_le_iff₀ hh).1 hyfloor.le
      push_cast
      nlinarith
  · have hmn : m < n := lt_of_not_ge hnm
    have hcell : upperRosserDepthTwoMeshCell m x = Fin.last m := by
      apply Fin.ext
      change min n m = m
      exact min_eq_right hmn.le
    rw [hcell]
    constructor
    · unfold upperRosserDepthTwoMeshLeft
      rw [show upperRosserDepthTwoMeshWidth m = h by rfl]
      have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn.le
      have hmle : (m : ℝ) ≤ y := hmnR.trans hfloor
      have hmul := (le_div_iff₀ hh).1 hmle
      simpa using (show 1 / 6 + (m : ℝ) * h ≤ x by linarith)
    · rw [upperRosserDepthTwoMeshRight_last]
      exact hx.2

/-- The uniform logarithmic mesh on an arbitrary fixed positive screen
`[c,1]`.  The depth-two mesh above is its specialization at `c = 1 / 6`; this
version is used by the arbitrary fixed-depth Rosser recursion. -/
noncomputable def upperRosserFixedDepthMeshWidth (c : ℝ) (m : ℕ) : ℝ :=
  (1 - c) / (m + 1)

/-- The left endpoint of a fixed-depth logarithmic mesh cell. -/
noncomputable def upperRosserFixedDepthMeshLeft
    (c : ℝ) (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  c + (i : ℝ) * upperRosserFixedDepthMeshWidth c m

/-- The right endpoint of a fixed-depth logarithmic mesh cell. -/
noncomputable def upperRosserFixedDepthMeshRight
    (c : ℝ) (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  upperRosserFixedDepthMeshLeft c m i + upperRosserFixedDepthMeshWidth c m

/-- The clamped fixed-depth mesh cell containing a screened logarithmic
coordinate. -/
noncomputable def upperRosserFixedDepthMeshCell
    (c : ℝ) (m : ℕ) (x : ℝ) : Fin (m + 1) :=
  ⟨min (Nat.floor ((x - c) / upperRosserFixedDepthMeshWidth c m)) m,
    Nat.lt_succ_iff.mpr (min_le_right _ _)⟩

theorem upperRosserFixedDepthMeshWidth_pos
    {c : ℝ} (hc : c < 1) (m : ℕ) :
    0 < upperRosserFixedDepthMeshWidth c m := by
  unfold upperRosserFixedDepthMeshWidth
  exact div_pos (sub_pos.mpr hc) (by positivity)

theorem upperRosserFixedDepthMeshLeft_mem
    {c : ℝ} (hc : c < 1) (m : ℕ) (i : Fin (m + 1)) :
    upperRosserFixedDepthMeshLeft c m i ∈ Set.Icc c 1 := by
  have hh := upperRosserFixedDepthMeshWidth_pos hc m
  constructor
  · unfold upperRosserFixedDepthMeshLeft
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hh.le)
  · unfold upperRosserFixedDepthMeshLeft upperRosserFixedDepthMeshWidth
    have hi : (i : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    calc
      c + (i : ℝ) * ((1 - c) / (m + 1)) ≤
          c + (m : ℝ) * ((1 - c) / (m + 1)) := by gcongr
      _ ≤ c + ((m : ℝ) + 1) * ((1 - c) / (m + 1)) := by
        gcongr
        norm_num
      _ = 1 := by
        field_simp
        ring

theorem upperRosserFixedDepthMeshLeft_le_right
    {c : ℝ} (hc : c < 1) (m : ℕ) (i : Fin (m + 1)) :
    upperRosserFixedDepthMeshLeft c m i ≤
      upperRosserFixedDepthMeshRight c m i := by
  unfold upperRosserFixedDepthMeshRight
  exact le_add_of_nonneg_right (upperRosserFixedDepthMeshWidth_pos hc m).le

theorem upperRosserFixedDepthMeshRight_le_one
    {c : ℝ} (hc : c < 1) (m : ℕ) (i : Fin (m + 1)) :
    upperRosserFixedDepthMeshRight c m i ≤ 1 := by
  unfold upperRosserFixedDepthMeshRight upperRosserFixedDepthMeshLeft
    upperRosserFixedDepthMeshWidth
  have hi : (i : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_iff.mpr i.isLt
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  calc
    c + (i : ℝ) * ((1 - c) / (m + 1)) +
          (1 - c) / (m + 1) =
        c + ((i : ℝ) + 1) * ((1 - c) / (m + 1)) := by ring
    _ ≤ c + ((m : ℝ) + 1) * ((1 - c) / (m + 1)) := by
      gcongr
    _ = 1 := by
      field_simp
      ring

theorem upperRosserFixedDepthMeshRight_mem
    {c : ℝ} (hc : c < 1) (m : ℕ) (i : Fin (m + 1)) :
    upperRosserFixedDepthMeshRight c m i ∈ Set.Icc c 1 :=
  ⟨(upperRosserFixedDepthMeshLeft_mem hc m i).1.trans
      (upperRosserFixedDepthMeshLeft_le_right hc m i),
    upperRosserFixedDepthMeshRight_le_one hc m i⟩

theorem upperRosserFixedDepthMeshRight_last
    {c : ℝ} (_hc : c < 1) (m : ℕ) :
    upperRosserFixedDepthMeshRight c m (Fin.last m) = 1 := by
  unfold upperRosserFixedDepthMeshRight upperRosserFixedDepthMeshLeft
    upperRosserFixedDepthMeshWidth
  simp only [Fin.val_last]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  field_simp
  ring

theorem upperRosserFixedDepthMeshCell_bounds
    {c : ℝ} (hc : c < 1) (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc c 1) :
    upperRosserFixedDepthMeshLeft c m
        (upperRosserFixedDepthMeshCell c m x) ≤ x ∧
      x ≤ upperRosserFixedDepthMeshRight c m
        (upperRosserFixedDepthMeshCell c m x) := by
  let h := upperRosserFixedDepthMeshWidth c m
  let y := (x - c) / h
  let n := Nat.floor y
  have hh : 0 < h := upperRosserFixedDepthMeshWidth_pos hc m
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx.1) hh.le
  have hyn : y ≤ (m : ℝ) + 1 := by
    apply (div_le_iff₀ hh).2
    dsimp [h, upperRosserFixedDepthMeshWidth]
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have heq :
        ((m : ℝ) + 1) * ((1 - c) / ((m : ℝ) + 1)) = 1 - c := by
      field_simp
    rw [heq]
    linarith [hx.2]
  have hfloor : (n : ℝ) ≤ y := Nat.floor_le hy0
  have hyfloor : y < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one y
  by_cases hnm : n ≤ m
  · have hcell :
        upperRosserFixedDepthMeshCell c m x =
          ⟨n, Nat.lt_succ_iff.mpr hnm⟩ := by
      apply Fin.ext
      change min n m = n
      exact min_eq_left hnm
    rw [hcell]
    constructor
    · unfold upperRosserFixedDepthMeshLeft
      rw [show upperRosserFixedDepthMeshWidth c m = h by rfl]
      have hmul := (le_div_iff₀ hh).1 hfloor
      simpa using (show c + (n : ℝ) * h ≤ x by linarith)
    · unfold upperRosserFixedDepthMeshRight upperRosserFixedDepthMeshLeft
      rw [show upperRosserFixedDepthMeshWidth c m = h by rfl]
      have hmul := (div_le_iff₀ hh).1 hyfloor.le
      push_cast
      nlinarith
  · have hmn : m < n := lt_of_not_ge hnm
    have hcell : upperRosserFixedDepthMeshCell c m x = Fin.last m := by
      apply Fin.ext
      change min n m = m
      exact min_eq_right hmn.le
    rw [hcell]
    constructor
    · unfold upperRosserFixedDepthMeshLeft
      rw [show upperRosserFixedDepthMeshWidth c m = h by rfl]
      have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn.le
      have hmle : (m : ℝ) ≤ y := hmnR.trans hfloor
      have hmul := (le_div_iff₀ hh).1 hmle
      simpa using (show c + (m : ℝ) * h ≤ x by linarith)
    · rw [upperRosserFixedDepthMeshRight_last hc]
      exact hx.2

/-- A finite logarithmic Darboux sum on the fixed-depth mesh is bounded by the
corresponding integral, with an explicit cell-majorant and reciprocal-coordinate
error.  This is the analytic bridge used twice in one Rosser-pair recursion:
first for the inner coordinate and then for the peeled outer coordinate. -/
theorem upperRosserFixedDepthMesh_darbouxSum_le_integral_add
    (m : ℕ) {c ε B : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {f : ℝ → ℝ} {M : Fin (m + 1) → ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hfB : ∀ x ∈ Set.Icc c 1, f x ≤ B)
    (hmajorant : ∀ i : Fin (m + 1), ∀ x ∈
      Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
        (upperRosserFixedDepthMeshRight c m i),
      M i ≤ f x + ε)
    (hint : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * f x) (Set.Ioo c 1)) :
    (∑ i : Fin (m + 1), M i *
        (upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i - 1)) ≤
      (∫ x in Set.Ioo c 1, x⁻¹ * f x) +
        ε / c + B * upperRosserFixedDepthMeshWidth c m / c ^ 2 := by
  let h := upperRosserFixedDepthMeshWidth c m
  let E := ε / c + B * h / c ^ 2
  let g : ℝ → ℝ := fun x => x⁻¹ * f x
  have hh : 0 < h := upperRosserFixedDepthMeshWidth_pos hc1 m
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hcell : ∀ i : Fin (m + 1),
      M i * (upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i - 1) ≤
        (∫ x in Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
          (upperRosserFixedDepthMeshRight c m i), g x) + E * h := by
    intro i
    let u := upperRosserFixedDepthMeshLeft c m i
    let v := upperRosserFixedDepthMeshRight c m i
    have hu : 0 < u := hc.trans_le (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
    have huv : u ≤ v := upperRosserFixedDepthMeshLeft_le_right hc1 m i
    have huLower : c ≤ u := (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
    have hvUpper : v ≤ 1 := upperRosserFixedDepthMeshRight_le_one hc1 m i
    have hvsub : v - u = h := by
      dsimp [u, v, h, upperRosserFixedDepthMeshRight]
      ring
    have hgCell : MeasureTheory.IntegrableOn g (Set.Ioo u v) :=
      hint.mono_set (by
        intro x hx
        exact ⟨huLower.trans_lt hx.1, hx.2.trans_le hvUpper⟩)
    have hpoint : ∀ x ∈ Set.Ioo u v, M i / u ≤ g x + E := by
      intro x hx
      have hxPos : 0 < x := hu.trans hx.1
      have hxMem : x ∈ Set.Icc c 1 :=
        ⟨huLower.trans hx.1.le, hx.2.le.trans hvUpper⟩
      have hxu : x - u ≤ h := by
        calc
          x - u ≤ v - u := sub_le_sub_right hx.2.le u
          _ = h := hvsub
      have hden : c ^ 2 ≤ u * x := by
        nlinarith [huLower, hxMem.1]
      have hInvDiff : u⁻¹ - x⁻¹ ≤ h / c ^ 2 := by
        rw [inv_sub_inv hu.ne' hxPos.ne']
        rw [div_le_iff₀ (mul_pos hu hxPos)]
        have hden' : (1 : ℝ) * c ^ 2 ≤ u * x := by
          simpa using hden
        have hfactor : 1 ≤ (u * x) / c ^ 2 :=
          (le_div_iff₀ (sq_pos_of_pos hc)).2 hden'
        calc
          x - u ≤ h := hxu
          _ ≤ h * ((u * x) / c ^ 2) :=
            (le_mul_of_one_le_right hh.le hfactor)
          _ = h / c ^ 2 * (u * x) := by
            field_simp [ne_of_gt hc]
      have hεDiv : ε / u ≤ ε / c := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ hu hc).2 huLower) hε
      have hmassInv :
          f x * (u⁻¹ - x⁻¹) ≤ B * h / c ^ 2 := by
        have hdiffNonneg : 0 ≤ u⁻¹ - x⁻¹ :=
          sub_nonneg.mpr ((inv_le_inv₀ hxPos hu).2 hx.1.le)
        calc
          f x * (u⁻¹ - x⁻¹) ≤ B * (u⁻¹ - x⁻¹) :=
            mul_le_mul_of_nonneg_right (hfB x hxMem) hdiffNonneg
          _ ≤ B * (h / c ^ 2) :=
            mul_le_mul_of_nonneg_left hInvDiff hB
          _ = B * h / c ^ 2 := by ring
      calc
        M i / u ≤ (f x + ε) / u :=
          (div_le_div_iff_of_pos_right hu).2 (hmajorant i x (by simpa [u, v] using hx))
        _ = x⁻¹ * f x + ε / u + f x * (u⁻¹ - x⁻¹) := by
          field_simp [hu.ne', hxPos.ne']
          ring
        _ ≤ x⁻¹ * f x + ε / c + B * h / c ^ 2 := by
          gcongr
        _ = g x + E := by
          dsimp [g, E]
          ring
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => E) (Set.Ioo u v) :=
      MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    have hmono :
        (∫ _x in Set.Ioo u v, M i / u) ≤
          ∫ x in Set.Ioo u v, g x + E := by
      apply MeasureTheory.setIntegral_mono_on
        (MeasureTheory.integrableOn_const (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top))
        (hgCell.add hconst) measurableSet_Ioo
      exact hpoint
    calc
      M i * (upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i - 1) =
          (∫ _x in Set.Ioo u v, M i / u) := by
        change M i * (v / u - 1) = ∫ _x in Set.Ioo u v, M i / u
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr huv)]
        rw [hvsub]
        rw [show v = u + h by linarith [hvsub]]
        simp only [smul_eq_mul]
        field_simp [hu.ne']
        ring
      _ ≤ ∫ x in Set.Ioo u v, g x + E := hmono
      _ = (∫ x in Set.Ioo u v, g x) + E * h := by
        rw [MeasureTheory.integral_add hgCell hconst,
          MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr huv)]
        rw [hvsub]
        ring
  have hdecomp :
      (∑ i : Fin (m + 1),
          ∫ x in Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
            (upperRosserFixedDepthMeshRight c m i), g x) =
        ∫ x in Set.Ioo c 1, g x := by
    let a : ℕ → ℝ := fun k => c + (k : ℝ) * h
    have ha : ∀ (k : ℕ) (hk : k < m + 1),
        upperRosserFixedDepthMeshLeft c m ⟨k, hk⟩ = a k ∧
          upperRosserFixedDepthMeshRight c m ⟨k, hk⟩ = a (k + 1) := by
      intro k hk
      constructor
      · simp [a, upperRosserFixedDepthMeshLeft, h]
      · simp [a, upperRosserFixedDepthMeshRight,
          upperRosserFixedDepthMeshLeft, h, Nat.cast_add, Nat.cast_one]
        ring
    have hintCells : ∀ k < m + 1,
        IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1)) := by
      intro k hk
      have hk' := ha k hk
      rw [← hk'.1, ← hk'.2]
      apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (upperRosserFixedDepthMeshLeft_le_right hc1 m ⟨k, hk⟩)).2
      exact hint.mono_set (by
        intro x hx
        exact ⟨(upperRosserFixedDepthMeshLeft_mem hc1 m ⟨k, hk⟩).1.trans_lt hx.1,
          hx.2.trans_le (upperRosserFixedDepthMeshRight_le_one hc1 m ⟨k, hk⟩)⟩)
    calc
      (∑ i : Fin (m + 1),
          ∫ x in Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
            (upperRosserFixedDepthMeshRight c m i), g x) =
          ∑ i : Fin (m + 1), ∫ x in a i..a (i + 1), g x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(ha i i.isLt).1, (ha i i.isLt).2,
          intervalIntegral.integral_of_le (by
            dsimp [a]
            have := hh
            push_cast
            nlinarith),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = ∑ k ∈ Finset.range (m + 1), ∫ x in a k..a (k + 1), g x := by
        rw [Fin.sum_univ_eq_sum_range
          (fun k => ∫ x in a k..a (k + 1), g x) (m + 1)]
      _ = ∫ x in a 0..a (m + 1), g x :=
        intervalIntegral.sum_integral_adjacent_intervals hintCells
      _ = ∫ x in Set.Ioo c 1, g x := by
        have ha0 : a 0 = c := by simp [a]
        have han : a (m + 1) = 1 := by
          dsimp [a, h, upperRosserFixedDepthMeshWidth]
          have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
          push_cast
          field_simp
          ring_nf
        rw [ha0, han, intervalIntegral.integral_of_le (by linarith),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    (∑ i : Fin (m + 1), M i *
        (upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i - 1)) ≤
        ∑ i : Fin (m + 1),
          ((∫ x in Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
            (upperRosserFixedDepthMeshRight c m i), g x) + E * h) :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = (∫ x in Set.Ioo c 1, g x) + ((m : ℝ) + 1) * (E * h) := by
      rw [Finset.sum_add_distrib, hdecomp]
      simp
    _ ≤ (∫ x in Set.Ioo c 1, g x) + E := by
      have htotal : ((m : ℝ) + 1) * h = 1 - c := by
        dsimp [h, upperRosserFixedDepthMeshWidth]
        field_simp
      have herr : ((m : ℝ) + 1) * (E * h) ≤ E := by
        calc
          ((m : ℝ) + 1) * (E * h) = E * (((m : ℝ) + 1) * h) := by ring
          _ ≤ E * 1 := by
            apply mul_le_mul_of_nonneg_left
            · rw [htotal]
              linarith [hc.le]
            · exact hE
          _ = E := by ring
      linarith
    _ = (∫ x in Set.Ioo c 1, x⁻¹ * f x) +
        ε / c + B * upperRosserFixedDepthMeshWidth c m / c ^ 2 := by
      dsimp [g, E, h]
      ring

/-- A sufficiently fine explicit logarithmic mesh simultaneously majorizes the
positive-depth residual mass in both peeled prime coordinates.  The corner uses
the right endpoints for the residual level and the left endpoint for the
inherited upper cutoff, exactly as required by the two-partition comparison. -/
theorem exists_upperRosserFixedDepthMesh_mass_majorant_succ
    (k : ℕ) {s a ε : ℝ} (ha : 0 < a) (ha1 : a < 1) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ i j : Fin (m + 1), ∀ x₀ x₁ : ℝ,
      x₀ ∈ Set.Icc (upperRosserFixedDepthMeshLeft a m j)
        (upperRosserFixedDepthMeshRight a m j) →
      x₁ ∈ Set.Icc (upperRosserFixedDepthMeshLeft a m i)
        (upperRosserFixedDepthMeshRight a m i) →
      LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - x₀ - x₁) a x₁ ≤
        LinearSieve.upperRosserBoundaryMassAux (k + 1)
          (s - upperRosserFixedDepthMeshRight a m j -
            upperRosserFixedDepthMeshRight a m i)
          a (upperRosserFixedDepthMeshLeft a m i) + ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    LinearSieve.exists_upperRosserBoundaryMassAux_level_upper_modulus_succ
      k (a := a) (r₀ := s - 2) (r₁ := s - 2 * a) ha hε
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * (1 - a) / δ < m := exists_nat_gt _
  have hwidth :
      2 * upperRosserFixedDepthMeshWidth a m < δ := by
    have hcross : 2 * (1 - a) < δ * (m : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hδ).1 hm
    dsimp [upperRosserFixedDepthMeshWidth]
    rw [show 2 * ((1 - a) / ((m : ℝ) + 1)) =
      (2 * (1 - a)) / ((m : ℝ) + 1) by ring]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  refine ⟨m, ?_⟩
  intro i j x₀ x₁ hx₀ hx₁
  let li := upperRosserFixedDepthMeshLeft a m i
  let ri := upperRosserFixedDepthMeshRight a m i
  let lj := upperRosserFixedDepthMeshLeft a m j
  let rj := upperRosserFixedDepthMeshRight a m j
  let h := upperRosserFixedDepthMeshWidth a m
  have hli := upperRosserFixedDepthMeshLeft_mem ha1 m i
  have hri := upperRosserFixedDepthMeshRight_mem ha1 m i
  have hlj := upperRosserFixedDepthMeshLeft_mem ha1 m j
  have hrj := upperRosserFixedDepthMeshRight_mem ha1 m j
  have hx₀mem : x₀ ∈ Set.Icc a 1 :=
    ⟨hlj.1.trans hx₀.1, hx₀.2.trans hrj.2⟩
  have hx₁mem : x₁ ∈ Set.Icc a 1 :=
    ⟨hli.1.trans hx₁.1, hx₁.2.trans hri.2⟩
  have hactual :
      (s - x₀ - x₁, x₁) ∈ Set.Icc (s - 2) (s - 2 * a) ×ˢ Set.Icc a 1 := by
    refine ⟨⟨?_, ?_⟩, hx₁mem⟩
    · linarith [hx₀mem.2, hx₁mem.2]
    · linarith [hx₀mem.1, hx₁mem.1]
  have hcorner :
      (s - rj - ri, li) ∈ Set.Icc (s - 2) (s - 2 * a) ×ˢ Set.Icc a 1 := by
    refine ⟨⟨?_, ?_⟩, hli⟩
    · linarith [hrj.2, hri.2]
    · linarith [hrj.1, hri.1]
  have hwidthPos : 0 < h := upperRosserFixedDepthMeshWidth_pos ha1 m
  have hriWidth : ri - li = h := by
    dsimp [ri, li, h, upperRosserFixedDepthMeshRight]
    ring
  have hrjWidth : rj - lj = h := by
    dsimp [rj, lj, h, upperRosserFixedDepthMeshRight]
    ring
  have hx₀gap : 0 ≤ rj - x₀ ∧ rj - x₀ ≤ h := by
    constructor
    · linarith [hx₀.2]
    · linarith [hx₀.1, hrjWidth]
  have hx₁gap : 0 ≤ ri - x₁ ∧ ri - x₁ ≤ h := by
    constructor
    · linarith [hx₁.2]
    · linarith [hx₁.1, hriWidth]
  have hdist :
      dist (s - x₀ - x₁, x₁) (s - rj - ri, li) < δ := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor
    · change |(s - x₀ - x₁) - (s - rj - ri)| < δ
      rw [show (s - x₀ - x₁) - (s - rj - ri) =
          (rj - x₀) + (ri - x₁) by ring,
          abs_of_nonneg (add_nonneg hx₀gap.1 hx₁gap.1)]
      have htwo : h + h < δ := by
        dsimp [h] at *
        linarith
      exact (add_le_add hx₀gap.2 hx₁gap.2).trans_lt htwo
    · change |x₁ - li| < δ
      rw [abs_of_nonneg (sub_nonneg.mpr hx₁.1)]
      have hgap : x₁ - li ≤ h := by linarith [hx₁.2, hriWidth]
      exact hgap.trans_lt (by nlinarith [hwidth, hwidthPos])
  have hclose := hmod _ hactual _ hcorner hdist
  have hone := le_abs_self
    (LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - x₀ - x₁) a x₁ -
      LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - ri) a li)
  dsimp [li, ri, lj, rj] at hone ⊢
  linarith

/-- One sufficiently fine logarithmic mesh majorizes the positive-depth residual
mass simultaneously for every level in a fixed compact interval.  This removes
the dependence of the mesh on the individual sieve ratio in the fixed-depth
successor induction. -/
theorem exists_upperRosserFixedDepthMesh_mass_majorant_succ_uniform
    (k : ℕ) {s₀ s₁ a ε : ℝ} (ha : 0 < a) (ha1 : a < 1) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ s ∈ Set.Icc s₀ s₁,
      ∀ i j : Fin (m + 1), ∀ x₀ x₁ : ℝ,
        x₀ ∈ Set.Icc (upperRosserFixedDepthMeshLeft a m j)
          (upperRosserFixedDepthMeshRight a m j) →
        x₁ ∈ Set.Icc (upperRosserFixedDepthMeshLeft a m i)
          (upperRosserFixedDepthMeshRight a m i) →
        LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - x₀ - x₁) a x₁ ≤
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - upperRosserFixedDepthMeshRight a m j -
              upperRosserFixedDepthMeshRight a m i)
            a (upperRosserFixedDepthMeshLeft a m i) + ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    LinearSieve.exists_upperRosserBoundaryMassAux_level_upper_modulus_succ
      k (a := a) (r₀ := s₀ - 2) (r₁ := s₁ - 2 * a) ha hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (1 - a) / δ < N := exists_nat_gt _
  refine ⟨N, ?_⟩
  intro m hNm
  have hm : 2 * (1 - a) / δ < (m : ℝ) :=
    hN.trans_le (by exact_mod_cast hNm)
  have hwidth :
      2 * upperRosserFixedDepthMeshWidth a m < δ := by
    have hcross : 2 * (1 - a) < δ * (m : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hδ).1 hm
    dsimp [upperRosserFixedDepthMeshWidth]
    rw [show 2 * ((1 - a) / ((m : ℝ) + 1)) =
      (2 * (1 - a)) / ((m : ℝ) + 1) by ring]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  intro s hs i j x₀ x₁ hx₀ hx₁
  let li := upperRosserFixedDepthMeshLeft a m i
  let ri := upperRosserFixedDepthMeshRight a m i
  let lj := upperRosserFixedDepthMeshLeft a m j
  let rj := upperRosserFixedDepthMeshRight a m j
  let h := upperRosserFixedDepthMeshWidth a m
  have hli := upperRosserFixedDepthMeshLeft_mem ha1 m i
  have hri := upperRosserFixedDepthMeshRight_mem ha1 m i
  have hlj := upperRosserFixedDepthMeshLeft_mem ha1 m j
  have hrj := upperRosserFixedDepthMeshRight_mem ha1 m j
  have hx₀mem : x₀ ∈ Set.Icc a 1 :=
    ⟨hlj.1.trans hx₀.1, hx₀.2.trans hrj.2⟩
  have hx₁mem : x₁ ∈ Set.Icc a 1 :=
    ⟨hli.1.trans hx₁.1, hx₁.2.trans hri.2⟩
  have hactual :
      (s - x₀ - x₁, x₁) ∈
        Set.Icc (s₀ - 2) (s₁ - 2 * a) ×ˢ Set.Icc a 1 := by
    refine ⟨⟨?_, ?_⟩, hx₁mem⟩
    · linarith [hs.1, hx₀mem.2, hx₁mem.2]
    · linarith [hs.2, hx₀mem.1, hx₁mem.1]
  have hcorner :
      (s - rj - ri, li) ∈
        Set.Icc (s₀ - 2) (s₁ - 2 * a) ×ˢ Set.Icc a 1 := by
    refine ⟨⟨?_, ?_⟩, hli⟩
    · linarith [hs.1, hrj.2, hri.2]
    · linarith [hs.2, hrj.1, hri.1]
  have hwidthPos : 0 < h := upperRosserFixedDepthMeshWidth_pos ha1 m
  have hriWidth : ri - li = h := by
    dsimp [ri, li, h, upperRosserFixedDepthMeshRight]
    ring
  have hrjWidth : rj - lj = h := by
    dsimp [rj, lj, h, upperRosserFixedDepthMeshRight]
    ring
  have hx₀gap : 0 ≤ rj - x₀ ∧ rj - x₀ ≤ h := by
    constructor
    · linarith [hx₀.2]
    · linarith [hx₀.1, hrjWidth]
  have hx₁gap : 0 ≤ ri - x₁ ∧ ri - x₁ ≤ h := by
    constructor
    · linarith [hx₁.2]
    · linarith [hx₁.1, hriWidth]
  have hdist :
      dist (s - x₀ - x₁, x₁) (s - rj - ri, li) < δ := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor
    · change |(s - x₀ - x₁) - (s - rj - ri)| < δ
      rw [show (s - x₀ - x₁) - (s - rj - ri) =
          (rj - x₀) + (ri - x₁) by ring,
          abs_of_nonneg (add_nonneg hx₀gap.1 hx₁gap.1)]
      have htwo : h + h < δ := by
        dsimp [h] at *
        linarith
      exact (add_le_add hx₀gap.2 hx₁gap.2).trans_lt htwo
    · change |x₁ - li| < δ
      rw [abs_of_nonneg (sub_nonneg.mpr hx₁.1)]
      have hgap : x₁ - li ≤ h := by linarith [hx₁.2, hriWidth]
      exact hgap.trans_lt (by nlinarith [hwidth, hwidthPos])
  have hclose := hmod _ hactual _ hcorner hdist
  have hone := le_abs_self
    (LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - x₀ - x₁) a x₁ -
      LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - ri) a li)
  dsimp [li, ri, lj, rj] at hone ⊢
  linarith

/-- A finite family of positive lower cutoffs admits one common refinement
threshold.  Hence any finer mesh simultaneously supplies all residual
majorants, uniformly over the prescribed level interval. -/
theorem exists_upperRosserFixedDepthMesh_mass_majorant_succ_uniform_finite
    {ι : Type*} [Fintype ι] (k : ℕ) (a : ι → ℝ) {s₀ s₁ ε : ℝ}
    (ha : ∀ t, 0 < a t) (ha1 : ∀ t, a t < 1) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ t, ∀ s ∈ Set.Icc s₀ s₁,
      ∀ i j : Fin (m + 1), ∀ x₀ x₁ : ℝ,
        x₀ ∈ Set.Icc (upperRosserFixedDepthMeshLeft (a t) m j)
          (upperRosserFixedDepthMeshRight (a t) m j) →
        x₁ ∈ Set.Icc (upperRosserFixedDepthMeshLeft (a t) m i)
          (upperRosserFixedDepthMeshRight (a t) m i) →
        LinearSieve.upperRosserBoundaryMassAux
            (k + 1) (s - x₀ - x₁) (a t) x₁ ≤
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - upperRosserFixedDepthMeshRight (a t) m j -
                upperRosserFixedDepthMeshRight (a t) m i)
              (a t) (upperRosserFixedDepthMeshLeft (a t) m i) + ε := by
  classical
  choose N hN using fun t =>
    exists_upperRosserFixedDepthMesh_mass_majorant_succ_uniform
      k (s₀ := s₀) (s₁ := s₁) (ha t) (ha1 t) hε
  refine ⟨∑ t, N t, ?_⟩
  intro m hm t
  apply hN t m
  exact (Finset.single_le_sum
    (fun u _ => Nat.zero_le (N u)) (Finset.mem_univ t)).trans hm

/-- One sufficiently fine logarithmic mesh simultaneously controls the residual
level, the distinguished-prime cutoff, and the inherited upper face.  Thus the
majorizing corner is indexed only by the three mesh cells and is uniform in the
sieve ratio on a compact interval. -/
theorem exists_upperRosserFixedDepthMesh_mass_majorant_succ_uniform_cutoffs
    (k : ℕ) {s₀ s₁ c ε : ℝ} (hc : 0 < c) (hc1 : c < 1) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ s ∈ Set.Icc s₀ s₁,
      ∀ h i j : Fin (m + 1), ∀ a x₀ x₁ : ℝ,
        a ∈ Set.Icc (upperRosserFixedDepthMeshLeft c m h)
          (upperRosserFixedDepthMeshRight c m h) →
        x₀ ∈ Set.Icc (upperRosserFixedDepthMeshLeft c m j)
          (upperRosserFixedDepthMeshRight c m j) →
        x₁ ∈ Set.Icc (upperRosserFixedDepthMeshLeft c m i)
          (upperRosserFixedDepthMeshRight c m i) →
        LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - x₀ - x₁) a x₁ ≤
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - upperRosserFixedDepthMeshRight c m j -
                upperRosserFixedDepthMeshRight c m i)
              (upperRosserFixedDepthMeshLeft c m h)
              (upperRosserFixedDepthMeshRight c m i) + ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    LinearSieve.exists_upperRosserBoundaryMassAux_level_lower_upper_modulus_succ
      k (r₀ := s₀ - 2) (r₁ := s₁ - 2 * c) hc hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (1 - c) / δ < N := exists_nat_gt _
  refine ⟨N, ?_⟩
  intro m hNm
  have hm : 2 * (1 - c) / δ < (m : ℝ) :=
    hN.trans_le (by exact_mod_cast hNm)
  have hwidth :
      2 * upperRosserFixedDepthMeshWidth c m < δ := by
    have hcross : 2 * (1 - c) < δ * (m : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hδ).1 hm
    dsimp [upperRosserFixedDepthMeshWidth]
    rw [show 2 * ((1 - c) / ((m : ℝ) + 1)) =
      (2 * (1 - c)) / ((m : ℝ) + 1) by ring]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  intro s hs h i j a x₀ x₁ ha hx₀ hx₁
  let lh := upperRosserFixedDepthMeshLeft c m h
  let rh := upperRosserFixedDepthMeshRight c m h
  let li := upperRosserFixedDepthMeshLeft c m i
  let ri := upperRosserFixedDepthMeshRight c m i
  let lj := upperRosserFixedDepthMeshLeft c m j
  let rj := upperRosserFixedDepthMeshRight c m j
  let w := upperRosserFixedDepthMeshWidth c m
  have hlh := upperRosserFixedDepthMeshLeft_mem hc1 m h
  have hrh := upperRosserFixedDepthMeshRight_mem hc1 m h
  have hli := upperRosserFixedDepthMeshLeft_mem hc1 m i
  have hri := upperRosserFixedDepthMeshRight_mem hc1 m i
  have hlj := upperRosserFixedDepthMeshLeft_mem hc1 m j
  have hrj := upperRosserFixedDepthMeshRight_mem hc1 m j
  have haMem : a ∈ Set.Icc c 1 :=
    ⟨hlh.1.trans ha.1, ha.2.trans hrh.2⟩
  have hx₀Mem : x₀ ∈ Set.Icc c 1 :=
    ⟨hlj.1.trans hx₀.1, hx₀.2.trans hrj.2⟩
  have hx₁Mem : x₁ ∈ Set.Icc c 1 :=
    ⟨hli.1.trans hx₁.1, hx₁.2.trans hri.2⟩
  have hactual :
      ((s - x₀ - x₁, a), x₁) ∈
        (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1 := by
    refine ⟨⟨⟨?_, ?_⟩, haMem⟩, hx₁Mem⟩
    · linarith [hs.1, hx₀Mem.2, hx₁Mem.2]
    · linarith [hs.2, hx₀Mem.1, hx₁Mem.1]
  have hcorner :
      ((s - rj - ri, lh), ri) ∈
        (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ Set.Icc c 1 := by
    refine ⟨⟨⟨?_, ?_⟩, hlh⟩, hri⟩
    · linarith [hs.1, hrj.2, hri.2]
    · linarith [hs.2, hrj.1, hri.1]
  have hwPos : 0 < w := upperRosserFixedDepthMeshWidth_pos hc1 m
  have hrhWidth : rh - lh = w := by
    dsimp [rh, lh, w, upperRosserFixedDepthMeshRight]
    ring
  have hriWidth : ri - li = w := by
    dsimp [ri, li, w, upperRosserFixedDepthMeshRight]
    ring
  have hrjWidth : rj - lj = w := by
    dsimp [rj, lj, w, upperRosserFixedDepthMeshRight]
    ring
  have haGap : 0 ≤ a - lh ∧ a - lh ≤ w := by
    constructor
    · linarith [ha.1]
    · linarith [ha.2, hrhWidth]
  have hx₀Gap : 0 ≤ rj - x₀ ∧ rj - x₀ ≤ w := by
    constructor
    · linarith [hx₀.2]
    · linarith [hx₀.1, hrjWidth]
  have hx₁Gap : 0 ≤ ri - x₁ ∧ ri - x₁ ≤ w := by
    constructor
    · linarith [hx₁.2]
    · linarith [hx₁.1, hriWidth]
  have hwlt : w < δ := by
    dsimp [w]
    nlinarith [hwidth, hwPos]
  have hdist :
      dist ((s - x₀ - x₁, a), x₁) ((s - rj - ri, lh), ri) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff,
      Real.dist_eq, Real.dist_eq, Real.dist_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change |(s - x₀ - x₁) - (s - rj - ri)| < δ
      rw [show (s - x₀ - x₁) - (s - rj - ri) =
          (rj - x₀) + (ri - x₁) by ring,
        abs_of_nonneg (add_nonneg hx₀Gap.1 hx₁Gap.1)]
      exact (add_le_add hx₀Gap.2 hx₁Gap.2).trans_lt (by
        dsimp [w] at *
        linarith)
    · rw [abs_of_nonneg haGap.1]
      exact haGap.2.trans_lt hwlt
    · rw [abs_of_nonpos (sub_nonpos.mpr hx₁.2)]
      rw [neg_sub]
      simpa [ri] using hx₁Gap.2.trans_lt hwlt
  have hclose := hmod _ hactual _ hcorner hdist
  have hone := le_abs_self
    (LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - x₀ - x₁) a x₁ -
      LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - ri) lh ri)
  dsimp [lh, ri, rj] at hone ⊢
  linarith

/-- The canonical upper sum of a nonnegative Lipschitz weight on the screened
mesh is within `O(meshWidth)` of its logarithmic integral. -/
theorem upperRosserDepthTwoMesh_darbouxSum_le_integral_add
    (m : ℕ) {f : ℝ → ℝ} {B L : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hf : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, 0 ≤ f x)
    (hfB : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, f x ≤ B)
    (hfLip : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 6 : ℝ) 1, |f x - f y| ≤ L * |x - y|)
    (hint : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * f x) (Set.Ioo (1 / 6) 1)) :
    (∑ i : Fin (m + 1),
        (f (upperRosserDepthTwoMeshLeft m i) +
            L * upperRosserDepthTwoMeshWidth m) *
          (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i - 1)) ≤
      (∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * f x) +
        (12 * L + 36 * B) * upperRosserDepthTwoMeshWidth m := by
  have hwidth : upperRosserFixedDepthMeshWidth (1 / 6) m =
      upperRosserDepthTwoMeshWidth m := by
    norm_num [upperRosserFixedDepthMeshWidth, upperRosserDepthTwoMeshWidth]
  have hleft : ∀ i : Fin (m + 1),
      upperRosserFixedDepthMeshLeft (1 / 6) m i =
        upperRosserDepthTwoMeshLeft m i := by
    intro i
    simp only [upperRosserFixedDepthMeshLeft, upperRosserDepthTwoMeshLeft, hwidth]
  have hright : ∀ i : Fin (m + 1),
      upperRosserFixedDepthMeshRight (1 / 6) m i =
        upperRosserDepthTwoMeshRight m i := by
    intro i
    simp only [upperRosserFixedDepthMeshRight, upperRosserDepthTwoMeshRight,
      hleft, hwidth]
  let h := upperRosserDepthTwoMeshWidth m
  have hh : 0 < h := upperRosserDepthTwoMeshWidth_pos m
  have hmajorant : ∀ i : Fin (m + 1), ∀ x ∈
      Set.Ioo (upperRosserFixedDepthMeshLeft (1 / 6) m i)
        (upperRosserFixedDepthMeshRight (1 / 6) m i),
      f (upperRosserDepthTwoMeshLeft m i) + L * h ≤ f x + 2 * L * h := by
    intro i x hx
    have huMem := upperRosserFixedDepthMeshLeft_mem (by norm_num : (1 / 6 : ℝ) < 1) m i
    have hvUpper := upperRosserFixedDepthMeshRight_le_one
      (by norm_num : (1 / 6 : ℝ) < 1) m i
    rw [hleft] at huMem
    rw [hleft, hright] at hx
    rw [hright] at hvUpper
    have hxMem : x ∈ Set.Icc (1 / 6 : ℝ) 1 :=
      ⟨huMem.1.trans hx.1.le, hx.2.le.trans hvUpper⟩
    have hdist : |upperRosserDepthTwoMeshLeft m i - x| ≤ h := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
      have hxRight := hx.2.le
      change x ≤ upperRosserDepthTwoMeshLeft m i + h at hxRight
      linarith only [hxRight]
    have hdiff := (hfLip _ huMem x hxMem).trans
      (mul_le_mul_of_nonneg_left hdist hL)
    linarith only [hdiff, le_abs_self (f (upperRosserDepthTwoMeshLeft m i) - f x)]
  have hbound := upperRosserFixedDepthMesh_darbouxSum_le_integral_add
    m (c := (1 / 6 : ℝ)) (ε := 2 * L * h) (B := B) (f := f)
    (M := fun i => f (upperRosserDepthTwoMeshLeft m i) + L * h)
    (by norm_num) (by norm_num) (by positivity) hB hfB hmajorant hint
  simp only [hleft, hright, hwidth] at hbound
  convert hbound using 1
  dsimp [h]
  ring

/-- Every canonical boundary chain in the normalized density expansion lands in
the real Rosser region, with all coordinates in the compact interval between
the distinguished-prime coordinate and `1`. -/
theorem upperRosserBoundaryChains_logarithmicCoordinates_mem
    {S : BoundingSieve} {z Δ s : ℝ} {q : ℕ} {l : List ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hl : l ∈ LinearSieve.upperRosserBoundaryChains
    (Nat.floor Δ + 1) q
    (S.prodPrimes.primeFactors.filter (fun p => q < p))) :
    LinearSieve.UpperRosserLogRegion s (Real.log q / Real.log z)
      (LinearSieve.logarithmicCoordinates z l) ∧
    ∀ x ∈ LinearSieve.logarithmicCoordinates z l,
      Real.log q / Real.log z < x ∧ x ≤ 1 := by
  let P := S.prodPrimes.primeFactors.filter (fun p => q < p)
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqP : q ∉ P := by simp [P]
  have hqmin : ∀ p ∈ P, q ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.le
  have hl' := (LinearSieve.mem_upperRosserBoundaryChains_iff
    hqP hqPrime hqmin).mp (by simpa [P] using hl)
  have hlP : l.toFinset ⊆ P := hl'.2.2.1
  have hlmem : ∀ p ∈ l, p ∈ P := by
    intro p hp
    exact hlP (by simpa using hp)
  have hlpos : ∀ p ∈ l, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp (hlmem p hp)).1).pos
  have hql : ∀ p ∈ l, q < p := by
    intro p hp
    exact (Finset.mem_filter.mp (hlmem p hp)).2
  have hlz : ∀ p ∈ l, (p : ℝ) ≤ z := by
    intro p hp
    exact hcut p (Finset.mem_filter.mp (hlmem p hp)).1
  refine ⟨LinearSieve.UpperRosserBoundaryChain.logarithmicCoordinates_mem
    (by linarith) hΔ hs hqPrime.pos hlpos hl'.2.2.2, ?_⟩
  exact LinearSieve.logarithmicCoordinates_mem_Ioc
    (by linarith) hqPrime.pos hql hlz

/-- Every even prefix of an explicit boundary chain satisfies the reverse
suffix inequality used by the geometric tail operator.  This keeps the
alternating Rosser restrictions in the exact `mainSum` expansion rather than
discarding them in an unrestricted factorial bound. -/
theorem upperRosserBoundaryChains_logarithmicCoordinates_even_lt_suffix
    {S : BoundingSieve} {z Δ s : ℝ} {q : ℕ} {l : List ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hl : l ∈ LinearSieve.upperRosserBoundaryChains
      (Nat.floor Δ + 1) q
      (S.prodPrimes.primeFactors.filter (fun p => q < p)))
    {i : ℕ}
    (hi : i < (LinearSieve.logarithmicCoordinates z l).length)
    (heven : Even i) :
    2 * (LinearSieve.logarithmicCoordinates z l)[i] <
      ((LinearSieve.logarithmicCoordinates z l).drop (i + 1)).sum +
        3 * (Real.log q / Real.log z) := by
  exact
    (upperRosserBoundaryChains_logarithmicCoordinates_mem
      hz hΔ hs hcut hq hl).1.even_coordinate_lt_suffix_add_terminal hi heven

/-- The innermost pair of every nonempty explicit boundary chain, normalized by
the distinguished-prime coordinate, lies in the initial `r = 3` cell of
`upperRosserAlternatingPairTransform`. -/
theorem upperRosserBoundaryChains_last_pair_log_ratios_mem
    {S : BoundingSieve} {z Δ s : ℝ} {q k : ℕ} {l : List ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hl : l ∈ LinearSieve.upperRosserBoundaryChains
      (Nat.floor Δ + 1) q
      (S.prodPrimes.primeFactors.filter (fun p => q < p)))
    (hlen : (LinearSieve.logarithmicCoordinates z l).length =
      2 * (k + 1)) :
    (LinearSieve.logarithmicCoordinates z l)[2 * k + 1] /
        (Real.log q / Real.log z) ∈ Set.Ioo (1 : ℝ) 3 ∧
      (LinearSieve.logarithmicCoordinates z l)[2 * k] /
          (Real.log q / Real.log z) ∈
        Set.Ioo
          ((LinearSieve.logarithmicCoordinates z l)[2 * k + 1] /
            (Real.log q / Real.log z))
          (((LinearSieve.logarithmicCoordinates z l)[2 * k + 1] /
              (Real.log q / Real.log z) + 3) / 2) := by
  have hmem := upperRosserBoundaryChains_logarithmicCoordinates_mem
    hz hΔ hs hcut hq hl
  have hbelow : LinearSieve.UpperRosserLogRegionBelow s
      (Real.log q / Real.log z) 2
      (LinearSieve.logarithmicCoordinates z l) := by
    refine ⟨hmem.1, ?_⟩
    intro x hx
    exact
      ⟨(hmem.2 x hx).1, (hmem.2 x hx).2.trans_lt (by norm_num)⟩
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have ha : 0 < Real.log q / Real.log z :=
    div_pos (Real.log_pos (by exact_mod_cast hqPrime.one_lt))
      (Real.log_pos (by linarith))
  exact hbelow.last_pair_ratios_mem hlen ha

/-- Enlarging the global upper face by any positive amount places every
discrete boundary chain in the strict bounded region used by the recursive
continuous mass. -/
theorem upperRosserBoundaryChains_logarithmicCoordinates_mem_below
    {S : BoundingSieve} {z Δ s ε : ℝ} {q : ℕ} {l : List ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hl : l ∈ LinearSieve.upperRosserBoundaryChains
      (Nat.floor Δ + 1) q
      (S.prodPrimes.primeFactors.filter (fun p => q < p)))
    (hε : 0 < ε) :
    LinearSieve.UpperRosserLogRegionBelow s
      (Real.log q / Real.log z) (1 + ε)
      (LinearSieve.logarithmicCoordinates z l) := by
  have hmem := upperRosserBoundaryChains_logarithmicCoordinates_mem
    hz hΔ hs hcut hq hl
  refine ⟨hmem.1, ?_⟩
  intro x hx
  exact ⟨(hmem.2 x hx).1, (hmem.2 x hx).2.trans_lt (by linarith)⟩

/-- At each fixed even depth, both the distinguished prime and every selected
prime coordinate stay in a compact interval bounded away from zero.  This is
the uniform support needed for the fixed-depth Darboux approximation. -/
theorem upperRosserBoundaryChains_fixed_length_logarithmic_support
    {S : BoundingSieve} {z Δ s : ℝ} {q k : ℕ} {l : List ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hl : l ∈ LinearSieve.upperRosserBoundaryChains
      (Nat.floor Δ + 1) q
      (S.prodPrimes.primeFactors.filter (fun p => q < p)))
    (hlen : l.length = 2 * k) :
    1 / (2 * 3 ^ k) < Real.log q / Real.log z ∧
      ∀ x ∈ LinearSieve.logarithmicCoordinates z l,
        1 / (2 * 3 ^ k) < x ∧ x ≤ 1 := by
  have hmem := upperRosserBoundaryChains_logarithmicCoordinates_mem
    hz hΔ hs hcut hq hl
  have hcoordlen :
      (LinearSieve.logarithmicCoordinates z l).length = 2 * k := by
    simpa [LinearSieve.logarithmicCoordinates] using hlen
  have houter :=
    hmem.1.outer_lower_of_three_halves_le hslo hcoordlen
  refine ⟨houter, ?_⟩
  intro x hx
  exact ⟨houter.trans (hmem.2 x hx).1, (hmem.2 x hx).2⟩

/-- At a fixed pair depth, the complete outer boundary sum is exactly supported
above the depth-dependent logarithmic cutoff.  This equality is uniform in the
outer weight and is the screening step used before recursive Stieltjes
comparisons. -/
theorem sum_mul_upperRosserBoundaryChainsFixedDepthDensity_eq_screened
    (nu w : ℕ → ℝ) {S : BoundingSieve} {z Δ s : ℝ} (k : ℕ)
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) :
    ∑ q ∈ S.prodPrimes.primeFactors, w q *
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity nu
          (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k =
      ∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => 1 / (2 * 3 ^ k) < Real.log q / Real.log z),
        w q * LinearSieve.upperRosserBoundaryChainsFixedDepthDensity nu
          (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  classical
  symm
  apply Finset.sum_subset
  · intro q hq
    exact (Finset.mem_filter.mp hq).1
  · intro q hq hqnot
    apply mul_eq_zero_of_right
    unfold LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
    apply Finset.sum_eq_zero
    intro l hl
    have hl' := Finset.mem_filter.mp hl
    have hsupport :=
      upperRosserBoundaryChains_fixed_length_logarithmic_support
        hz hΔ hs hslo hcut hq hl'.1 hl'.2
    exact (hqnot (Finset.mem_filter.mpr ⟨hq, hsupport.1⟩)).elim

/-- The logarithmic coordinates of a chain of prescribed even length, packaged
as a fixed finite-dimensional vector. -/
noncomputable def upperRosserLogCoordinateVector
    (z : ℝ) (l : List ℕ) (k : ℕ) (hlen : l.length = 2 * k) :
    List.Vector ℝ (2 * k) :=
  ⟨LinearSieve.logarithmicCoordinates z l, by
    simpa [LinearSieve.logarithmicCoordinates] using hlen⟩

/-- A compact box containing every logarithmic coordinate vector at fixed
Rosser depth on the fundamental-lemma range. -/
def upperRosserFixedDepthAmbientBox (k : ℕ) :
    Set (Fin (2 * k) → ℝ) :=
  Set.Icc (fun _ => 1 / (2 * 3 ^ k)) (fun _ => 1)

theorem upperRosserFixedDepthAmbientBox_isCompact (k : ℕ) :
    IsCompact (upperRosserFixedDepthAmbientBox k) :=
  isCompact_Icc

theorem upperRosserFixedDepthAmbientBox_measurableSet (k : ℕ) :
    MeasurableSet (upperRosserFixedDepthAmbientBox k) :=
  measurableSet_Icc

/-- The vector form of fixed-depth support, suitable for integration against
the product Lebesgue measure on `Fin (2k) → ℝ`. -/
theorem upperRosserLogCoordinateVector_mem_fixedDepthAmbientBox
    {S : BoundingSieve} {z Δ s : ℝ} {q k : ℕ} {l : List ℕ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hl : l ∈ LinearSieve.upperRosserBoundaryChains
      (Nat.floor Δ + 1) q
      (S.prodPrimes.primeFactors.filter (fun p => q < p)))
    (hlen : l.length = 2 * k) :
    (fun i => (upperRosserLogCoordinateVector z l k hlen).get i) ∈
      upperRosserFixedDepthAmbientBox k := by
  have hsupport := upperRosserBoundaryChains_fixed_length_logarithmic_support
    hz hΔ hs hslo hcut hq hl hlen
  constructor <;> intro i
  · apply (hsupport.2 _ ?_).1.le
    change (upperRosserLogCoordinateVector z l k hlen).get i ∈
      LinearSieve.logarithmicCoordinates z l
    exact List.get_mem _ _
  · apply (hsupport.2 _ ?_).2
    change (upperRosserLogCoordinateVector z l k hlen).get i ∈
      LinearSieve.logarithmicCoordinates z l
    exact List.get_mem _ _

/-- A lower bound for a logarithmic coordinate gives a uniform bound for the
local-product correction occurring in every logarithmic cell. -/
theorem localProduct_error_le_of_log_coordinate_lower
    {K z a c : ℝ} (hK : 0 ≤ K) (hz : 1 < z)
    (hc : 0 < c) (hca : c ≤ a) :
    K / (a * Real.log z) ≤ K / (c * Real.log z) := by
  apply div_le_div_of_nonneg_left hK
  · exact mul_pos hc (Real.log_pos hz)
  · exact mul_le_mul_of_nonneg_right hca (Real.log_pos hz).le

/-- An explicit cutoff makes the local-product correction uniformly smaller
than a prescribed error on every logarithmic coordinate bounded below by `c`. -/
theorem exists_localProduct_error_cutoff
    {K η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z →
      K / (c * Real.log z) ≤ η := by
  refine ⟨max 2 (Real.exp (K / (c * η))), le_max_left _ _, ?_⟩
  intro z hz
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hzexp : Real.exp (K / (c * η)) ≤ z :=
    (le_max_right _ _).trans hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : K / (c * η) ≤ Real.log z := by
    calc
      K / (c * η) = Real.log (Real.exp (K / (c * η))) :=
        (Real.log_exp _).symm
      _ ≤ Real.log z := Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos _) ((Real.exp_pos _).trans_le hzexp) hzexp
  apply (div_le_iff₀ (mul_pos hc hlogz)).2
  calc
    K = (c * η) * (K / (c * η)) := by field_simp
    _ ≤ (c * η) * Real.log z :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hc.le hη.le)
    _ = η * (c * Real.log z) := by ring

end MathlibNt.SieveTheory.SwitchingPrinciple
