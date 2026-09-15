import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergUniformEuler
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# Growth of Liu's prime-divisor Euler factors

We split the prime divisors of `N` at the transparent cutoff
`⌈log N⌉₊`.  Mertens' product theorem controls the small primes, while
the elementary estimate `log (1 + 1 / p) ≤ 1 / p` and the radical of `N`
control the large primes.
-/

open scoped BigOperators Topology

namespace MathlibNt.SieveTheory.LiuWeight

open Finset Filter

/-- The natural cutoff used to split the prime divisors of `N`. -/
noncomputable def liuPrimeDivisorCutoff (N : ℕ) : ℕ :=
  ⌈Real.log (N : ℝ)⌉₊

/-- Passing from `log N` to its natural ceiling costs at most one after taking logs. -/
private theorem log_liuPrimeDivisorCutoff_le {N : ℕ}
    (hlogN2 : 2 ≤ Real.log (N : ℝ)) :
    Real.log (liuPrimeDivisorCutoff N : ℝ) ≤ 1 + Real.log (Real.log N) := by
  let y := liuPrimeDivisorCutoff N
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := le_trans (by norm_num) hlogN2
  have hlogNpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num) hlogN2
  have hlogN_le_y : Real.log (N : ℝ) ≤ (y : ℝ) := Nat.le_ceil _
  have hyPos : (0 : ℝ) < y := hlogNpos.trans_le hlogN_le_y
  have hy_lt : (y : ℝ) < Real.log N + 1 := Nat.ceil_lt_add_one hlogN0
  have hy_le_two_log : (y : ℝ) ≤ 2 * Real.log N := by linarith
  calc
    Real.log (y : ℝ) ≤ Real.log (2 * Real.log N) :=
      Real.strictMonoOn_log.monotoneOn hyPos (mul_pos (by norm_num) hlogNpos)
        hy_le_two_log
    _ = Real.log 2 + Real.log (Real.log N) := by
      rw [Real.log_mul (by norm_num) hlogNpos.ne']
    _ ≤ 1 + Real.log (Real.log N) := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]

private theorem sum_log_primeFactors_le_log {N : ℕ} (hN : 0 < N) :
    ∑ p ∈ N.primeFactors, Real.log p ≤ Real.log N := by
  have hradPos : 0 < ∏ p ∈ N.primeFactors, p := by
    exact Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).pos
  have hradLe : ∏ p ∈ N.primeFactors, p ≤ N :=
    Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  calc
    ∑ p ∈ N.primeFactors, Real.log p =
        Real.log (∏ p ∈ N.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ = Real.log (↑(∏ p ∈ N.primeFactors, p) : ℝ) := by
          rw [Nat.cast_prod]
    _ ≤ Real.log (N : ℝ) := by
          apply Real.strictMonoOn_log.monotoneOn
          · show 0 < (↑(∏ p ∈ N.primeFactors, p) : ℝ)
            exact_mod_cast hradPos
          · show 0 < (N : ℝ)
            exact_mod_cast hN
          · exact_mod_cast hradLe

private theorem one_add_prime_inv_le_one_sub_prime_inv_inv
    {p : ℕ} (hp : p.Prime) :
    1 + ((p : ℝ)⁻¹) ≤ (1 - ((p : ℝ)⁻¹))⁻¹ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : 0 < 1 - ((p : ℝ)⁻¹) := by
    have : (1 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
    exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).2 this)
  have hmul :
      (1 + ((p : ℝ)⁻¹)) * (1 - ((p : ℝ)⁻¹)) ≤ 1 := by
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
    field_simp
    nlinarith
  simpa only [one_div] using (le_div_iff₀ hden).2 hmul

private theorem one_le_one_sub_prime_inv_inv {p : ℕ} (hp : p.Prime) :
    1 ≤ (1 - ((p : ℝ)⁻¹))⁻¹ := by
  calc
    1 ≤ 1 + ((p : ℝ)⁻¹) := le_add_of_nonneg_right (by positivity)
    _ ≤ (1 - ((p : ℝ)⁻¹))⁻¹ := one_add_prime_inv_le_one_sub_prime_inv_inv hp

private theorem small_prime_divisor_product_le
    {N y : ℕ} :
    (N.primeFactors.filter (· ≤ y)).prod (fun p => 1 + ((p : ℝ)⁻¹)) ≤
      (MertensTheorem.primeProduct y)⁻¹ := by
  let P := (range (y + 1)).filter Nat.Prime
  have hsub : N.primeFactors.filter (· ≤ y) ⊆ P := by
    intro p hp
    simp only [mem_filter, mem_range, P] at hp ⊢
    exact ⟨Nat.lt_succ_of_le hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  calc
    (N.primeFactors.filter (· ≤ y)).prod (fun p => 1 + ((p : ℝ)⁻¹)) ≤
        (N.primeFactors.filter (· ≤ y)).prod
          (fun p => (1 - ((p : ℝ)⁻¹))⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        exact one_add_prime_inv_le_one_sub_prime_inv_inv
          (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
    _ ≤ P.prod (fun p => (1 - ((p : ℝ)⁻¹))⁻¹) := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsub
      · intro p hp
        exact (one_le_one_sub_prime_inv_inv
          (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).trans' zero_le_one
      · intro p hpP hp
        exact one_le_one_sub_prime_inv_inv (mem_filter.mp hpP).2
    _ = (MertensTheorem.primeProduct y)⁻¹ := by
      rw [Finset.prod_inv_distrib]
      simp [P, MertensTheorem.primeProduct]

private theorem large_prime_divisor_reciprocal_sum_le
    {N y : ℕ} (hN : 0 < N) (hy : 2 ≤ y)
    (hlogN : Real.log N ≤ y) :
    ∑ p ∈ N.primeFactors.filter (y < ·), ((p : ℝ)⁻¹) ≤
      (Real.log 2)⁻¹ := by
  have hyR : (0 : ℝ) < y := by positivity
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hpoint : ∀ p ∈ N.primeFactors.filter (y < ·),
      ((p : ℝ)⁻¹) ≤ Real.log p / ((y : ℝ) * Real.log y) := by
    intro p hp
    have hyp : y < p := (mem_filter.mp hp).2
    have hpR : (y : ℝ) ≤ p := by exact_mod_cast hyp.le
    have hlogle : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hyR
        (lt_of_lt_of_le hyR hpR) hpR
    have hratio : (1 : ℝ) ≤ Real.log p / Real.log y :=
      (le_div_iff₀ hlogy).2 (by simpa using hlogle)
    calc
      ((p : ℝ)⁻¹) = 1 / (p : ℝ) := (one_div _).symm
      _ ≤ 1 / (y : ℝ) := one_div_le_one_div_of_le hyR hpR
      _ = (1 / (y : ℝ)) * 1 := by ring
      _ ≤ (1 / (y : ℝ)) * (Real.log p / Real.log y) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = Real.log p / ((y : ℝ) * Real.log y) := by field_simp
  calc
    ∑ p ∈ N.primeFactors.filter (y < ·), ((p : ℝ)⁻¹) ≤
        ∑ p ∈ N.primeFactors.filter (y < ·),
          Real.log p / ((y : ℝ) * Real.log y) :=
      Finset.sum_le_sum hpoint
    _ = (∑ p ∈ N.primeFactors.filter (y < ·), Real.log p) /
          ((y : ℝ) * Real.log y) := by rw [Finset.sum_div]
    _ ≤ Real.log N / ((y : ℝ) * Real.log y) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hyR.le hlogy.le)
      exact le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p hp₁ hp₂ => Real.log_natCast_nonneg p))
        (sum_log_primeFactors_le_log hN)
    _ ≤ (y : ℝ) / ((y : ℝ) * Real.log y) := by
      exact div_le_div_of_nonneg_right hlogN (mul_nonneg hyR.le hlogy.le)
    _ = (Real.log y)⁻¹ := by field_simp
    _ ≤ (Real.log 2)⁻¹ := by
      apply (inv_le_inv₀ hlogy (Real.log_pos (by norm_num))).2
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hyR
        (by exact_mod_cast hy)

private theorem large_prime_divisor_product_le
    {N y : ℕ} (hN : 0 < N) (hy : 2 ≤ y)
    (hlogN : Real.log N ≤ y) :
    (N.primeFactors.filter (y < ·)).prod
        (fun p => 1 + ((p : ℝ)⁻¹)) ≤
      Real.exp ((Real.log 2)⁻¹) := by
  calc
    (N.primeFactors.filter (y < ·)).prod
        (fun p => 1 + ((p : ℝ)⁻¹)) ≤
        (N.primeFactors.filter (y < ·)).prod
          (fun p => Real.exp ((p : ℝ)⁻¹)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp ((p : ℝ)⁻¹)
    _ = Real.exp (∑ p ∈ N.primeFactors.filter (y < ·), ((p : ℝ)⁻¹)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp ((Real.log 2)⁻¹) :=
      Real.exp_le_exp.mpr (large_prime_divisor_reciprocal_sum_le hN hy hlogN)

/-- Liu's finite prime-divisor Euler product has at most log-log growth.
The constants and threshold are independent of `N`. -/
theorem exists_liuPrimeDivisorProduct_le_log_log :
    ∃ C_L : ℝ, 0 < C_L ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuPrimeDivisorProduct N ≤
        C_L * (1 + Real.log (Real.log N)) := by
  obtain ⟨c₁, c₂, hc₁, hMertens⟩ :=
    MertensTheorem.primeProduct_asymptotic_order
  let E := Real.exp ((Real.log 2)⁻¹)
  refine ⟨E / c₁, div_pos (Real.exp_pos _) hc₁, ?_⟩
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      liuPrimeDivisorProduct N ≤
        (E / c₁) * (1 + Real.log (Real.log N)) := by
    filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ))]
      with N hlogN2
    let y := liuPrimeDivisorCutoff N
    have hN : 0 < N := by
      by_contra h
      have : N = 0 := Nat.eq_zero_of_not_pos h
      subst N
      norm_num at hlogN2
    have hlogN_le_y : Real.log (N : ℝ) ≤ (y : ℝ) := by
      exact Nat.le_ceil _
    have hy : 2 ≤ y := by
      exact_mod_cast (hlogN2.trans hlogN_le_y)
    have hlogy_le : Real.log (y : ℝ) ≤ 1 + Real.log (Real.log N) :=
      log_liuPrimeDivisorCutoff_le hlogN2
    have hsmall :=
      small_prime_divisor_product_le (N := N) (y := y)
    have hPP := (hMertens y hy).1
    have hPPpos : 0 < MertensTheorem.primeProduct y :=
      lt_of_lt_of_le (div_pos hc₁ (Real.log_pos (by exact_mod_cast
        (show 1 < y by omega)))) hPP
    have hsmall' :
        (N.primeFactors.filter (· ≤ y)).prod
            (fun p => 1 + ((p : ℝ)⁻¹)) ≤ Real.log y / c₁ := by
      refine hsmall.trans ?_
      have hinv := (inv_le_inv₀ hPPpos
        (div_pos hc₁ (Real.log_pos (by exact_mod_cast
          (show 1 < y by omega))))).2 hPP
      calc
        (MertensTheorem.primeProduct y)⁻¹ ≤
            (c₁ / Real.log y)⁻¹ := hinv
        _ = Real.log y / c₁ := by field_simp
    have hlarge := large_prime_divisor_product_le hN hy hlogN_le_y
    have hsplit :
        liuPrimeDivisorProduct N =
          (N.primeFactors.filter (· ≤ y)).prod
              (fun p => 1 + ((p : ℝ)⁻¹)) *
            (N.primeFactors.filter (y < ·)).prod
              (fun p => 1 + ((p : ℝ)⁻¹)) := by
      rw [liuPrimeDivisorProduct,
        ← Finset.prod_filter_mul_prod_filter_not N.primeFactors
          (· ≤ y) (fun p => 1 + ((p : ℝ)⁻¹))]
      simp only [not_le]
    rw [hsplit]
    calc
      _ ≤ (Real.log y / c₁) * E :=
        mul_le_mul hsmall' hlarge (by positivity) (by positivity)
      _ ≤ (E / c₁) * (1 + Real.log (Real.log N)) := by
        dsimp [E]
        have hnonneg : 0 ≤ Real.log (y : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
        calc
          Real.log y / c₁ * Real.exp (Real.log 2)⁻¹ =
              (Real.exp (Real.log 2)⁻¹ / c₁) * Real.log y := by ring
          _ ≤ (Real.exp (Real.log 2)⁻¹ / c₁) *
              (1 + Real.log (Real.log N)) :=
            mul_le_mul_of_nonneg_left hlogy_le
              (div_nonneg (Real.exp_pos _).le hc₁.le)
  simpa only [eventually_atTop] using hevent

/-- The logarithmic prime-divisor moment has at most squared log-log growth. -/
theorem exists_liuPrimeDivisorLogSum_le_log_log_sq :
    ∃ C_D : ℝ, 0 < C_D ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuPrimeDivisorLogSum N ≤
        C_D * (1 + (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨B, C, hM⟩ := MertensTheorem.mertens_second_theorem
  have hC : 0 ≤ C := by
    have h := hM 2 (by norm_num)
    have hn : 0 ≤ C / Real.log 2 := le_trans (abs_nonneg _) h
    simpa using (le_div_iff₀ (Real.log_pos (by norm_num))).mp hn
  let K := |B| + C / Real.log 2
  have hK : 0 ≤ K := add_nonneg (abs_nonneg _)
    (div_nonneg hC (Real.log_pos (by norm_num)).le)
  refine ⟨8 * (1 + K), by positivity, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hevent : ∀ᶠ N : ℕ in atTop, liuPrimeDivisorLogSum N ≤
      (8 * (1 + K)) * (1 + (Real.log (Real.log N)) ^ 2) := by
    filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ)),
      hll.eventually (eventually_ge_atTop (1 : ℝ))] with N hlogN2 ht
    let y := liuPrimeDivisorCutoff N
    have hN : 0 < N := by
      by_contra hn
      have : N = 0 := Nat.eq_zero_of_not_pos hn
      subst N
      norm_num at hlogN2
    have hlogN_le_y : Real.log (N : ℝ) ≤ (y : ℝ) := Nat.le_ceil _
    have hy : 2 ≤ y := by exact_mod_cast hlogN2.trans hlogN_le_y
    have hlogypos : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hlogy_le : Real.log (y : ℝ) ≤ 1 + Real.log (Real.log N) :=
      log_liuPrimeDivisorCutoff_le hlogN2
    have hrecip :
        MertensTheorem.primeReciprocalSum y ≤ Real.log (Real.log y) + K := by
      have hm := hM y hy
      have hu := (le_abs_self
        (MertensTheorem.primeReciprocalSum y -
          (Real.log (Real.log y) + B))).trans hm
      have hlog2le : Real.log 2 ≤ Real.log y :=
        Real.strictMonoOn_log.monotoneOn (by norm_num)
          (show (0 : ℝ) < y by positivity)
          (by exact_mod_cast hy)
      have hdiv : C / Real.log y ≤ C / Real.log 2 :=
        div_le_div_of_nonneg_left hC (Real.log_pos (by norm_num)) hlog2le
      dsimp [K]
      linarith [le_abs_self B]
    have hsmall :
        ∑ p ∈ N.primeFactors.filter (· ≤ y), Real.log p / p ≤
          Real.log y * MertensTheorem.primeReciprocalSum y := by
      calc
        _ ≤ ∑ p ∈ N.primeFactors.filter (· ≤ y),
            Real.log y * ((p : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpP := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
          have hl := Real.strictMonoOn_log.monotoneOn
            (show (0 : ℝ) < p by exact_mod_cast hpP.pos)
            (show (0 : ℝ) < y by positivity)
            (by exact_mod_cast (mem_filter.mp hp).2)
          have hinv : 0 ≤ ((p : ℝ)⁻¹) := by positivity
          change Real.log p * (p : ℝ)⁻¹ ≤ Real.log y * (p : ℝ)⁻¹
          exact mul_le_mul_of_nonneg_right hl hinv
        _ ≤ Real.log y * MertensTheorem.primeReciprocalSum y := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ hlogypos.le
          unfold MertensTheorem.primeReciprocalSum
          have hs : N.primeFactors.filter (· ≤ y) ⊆
              (range (y + 1)).filter Nat.Prime := by
            intro p hp
            simp only [mem_filter, mem_range] at hp ⊢
            exact ⟨Nat.lt_succ_of_le hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
          simpa only [one_div] using
            (Finset.sum_le_sum_of_subset_of_nonneg hs
              (fun p hp₁ hp₂ => (inv_nonneg.mpr (by positivity) :
                0 ≤ ((p : ℝ)⁻¹))))
    have hlarge :
        ∑ p ∈ N.primeFactors.filter (y < ·), Real.log p / p ≤ 1 := by
      calc
        _ ≤ ∑ p ∈ N.primeFactors.filter (y < ·), Real.log p / y := by
          apply Finset.sum_le_sum
          intro p hp
          exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
            (by positivity) (by exact_mod_cast (mem_filter.mp hp).2.le)
        _ = (∑ p ∈ N.primeFactors.filter (y < ·), Real.log p) / y := by
          rw [Finset.sum_div]
        _ ≤ Real.log N / y := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun p hp₁ hp₂ => Real.log_natCast_nonneg p))
            (sum_log_primeFactors_le_log hN)
        _ ≤ 1 := (div_le_one (by positivity)).2 hlogN_le_y
    rw [liuPrimeDivisorLogSum,
      ← Finset.sum_filter_add_sum_filter_not N.primeFactors (· ≤ y)]
    simp only [not_le]
    have hloglogy : Real.log (Real.log y) ≤ Real.log y :=
      (Real.log_le_sub_one_of_pos hlogypos).trans (by linarith)
    calc
      _ ≤ Real.log y * MertensTheorem.primeReciprocalSum y + 1 :=
        add_le_add hsmall hlarge
      _ ≤ Real.log y * (Real.log y + K) + 1 := by
        gcongr
        have hh : Real.log (Real.log y) + K ≤ Real.log y + K := by
          linarith
        exact hrecip.trans hh
      _ ≤ (8 * (1 + K)) * (1 + (Real.log (Real.log N)) ^ 2) := by
        have ha : Real.log y ≤ 2 * Real.log (Real.log N) := by linarith
        have ht0 : 0 ≤ Real.log (Real.log N) := le_trans (by norm_num) ht
        nlinarith [sq_nonneg (Real.log (Real.log N) - 1),
          mul_nonneg hK ht0]
  simpa only [eventually_atTop] using hevent

/-- Along even integers, the numerator in the uniform Selberg Euler error is
bounded by a fixed sixth power of `1 + log log N`. -/
theorem exists_liuSelbergEulerErrorNumerator_le_log_log_pow :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N) *
          SingularSeries.liuSingularSeries N ≤
        C * (1 + Real.log (Real.log N)) ^ 6 := by
  obtain ⟨C_L, hC_L, N_L, hL⟩ :=
    exists_liuPrimeDivisorProduct_le_log_log
  obtain ⟨C_D, hC_D, N_D, hD⟩ :=
    exists_liuPrimeDivisorLogSum_le_log_log_sq
  let C := liuUniversalAbsEuler * C_L ^ 4 *
    (2 * (liuUniversalAbsLogRatio + C_D) + 1)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos
      (mul_pos liuUniversalAbsEuler_pos (pow_pos hC_L 4))
      (by nlinarith [liuUniversalAbsLogRatio_nonneg])
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll :
      Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hevent : ∀ᶠ N : ℕ in atTop,
      Even N →
        (2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N) *
            SingularSeries.liuSingularSeries N ≤
          C * (1 + Real.log (Real.log N)) ^ 6 := by
    filter_upwards [eventually_ge_atTop N_L, eventually_ge_atTop N_D,
      hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      hll.eventually (eventually_ge_atTop (1 : ℝ))]
      with N hNL hND hlogN hllN
    intro hNeven
    let t := Real.log (Real.log (N : ℝ))
    let u := 1 + t
    have ht : 1 ≤ t := hllN
    have hu : 1 ≤ u := by dsimp [u]; linarith
    have hu0 : 0 ≤ u := le_trans zero_le_one hu
    have hu2 : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
    have hN : 0 < N := by
      by_contra hn
      have : N = 0 := Nat.eq_zero_of_not_pos hn
      subst N
      norm_num at hlogN
    have hL0 : 0 ≤ liuPrimeDivisorProduct N :=
      (liuPrimeDivisorProduct_pos N).le
    have hD0 : 0 ≤ liuPrimeDivisorLogSum N := by
      unfold liuPrimeDivisorLogSum
      apply Finset.sum_nonneg
      intro p hp
      exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
    have hA0 : 0 ≤ liuSelbergAbsoluteMass N := by
      unfold liuSelbergAbsoluteMass
      exact tsum_nonneg fun d => abs_nonneg _
    have hB0 : 0 ≤ liuSelbergAbsoluteLogMoment N := by
      unfold liuSelbergAbsoluteLogMoment
      exact tsum_nonneg fun d =>
        mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg d)
    have hS0 : 0 ≤ SingularSeries.liuSingularSeries N :=
      (SingularSeries.liuSingularSeries_pos N).le
    have hE0 : 0 ≤ liuUniversalAbsEuler :=
      liuUniversalAbsEuler_nonneg
    have hR0 : 0 ≤ liuUniversalAbsLogRatio :=
      liuUniversalAbsLogRatio_nonneg
    have hLu :
        liuPrimeDivisorProduct N ≤ C_L * u := by
      simpa [u, t] using hL N hNL
    have hDu :
        liuPrimeDivisorLogSum N ≤ C_D * u ^ 2 := by
      calc
        liuPrimeDivisorLogSum N ≤ C_D * (1 + t ^ 2) := by
          simpa [t] using hD N hND
        _ ≤ C_D * u ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC_D.le
          dsimp [u]
          nlinarith
    have hRu :
        liuUniversalAbsLogRatio + liuPrimeDivisorLogSum N ≤
          (liuUniversalAbsLogRatio + C_D) * u ^ 2 := by
      calc
        liuUniversalAbsLogRatio + liuPrimeDivisorLogSum N ≤
            liuUniversalAbsLogRatio + C_D * u ^ 2 :=
          by linarith
        _ ≤ (liuUniversalAbsLogRatio + C_D) * u ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hu2 hR0
          nlinarith
    have hA :
        liuSelbergAbsoluteMass N ≤
          liuUniversalAbsEuler * C_L * u := by
      calc
        liuSelbergAbsoluteMass N ≤
            liuUniversalAbsEuler * liuPrimeDivisorProduct N := by
          simpa [liuSelbergAbsoluteMass] using
            tsum_abs_liuSelbergCorrection_le_uniform hNeven hN
        _ ≤ liuUniversalAbsEuler * (C_L * u) :=
          mul_le_mul_of_nonneg_left hLu hE0
        _ = liuUniversalAbsEuler * C_L * u := by ring
    have hB :
        liuSelbergAbsoluteLogMoment N ≤
          liuUniversalAbsEuler * C_L *
            (liuUniversalAbsLogRatio + C_D) * u ^ 3 := by
      calc
        liuSelbergAbsoluteLogMoment N ≤
            liuUniversalAbsEuler * liuPrimeDivisorProduct N *
              (liuUniversalAbsLogRatio + liuPrimeDivisorLogSum N) :=
          liuSelbergAbsoluteLogMoment_le_uniform_normalized hNeven hN
        _ ≤ liuUniversalAbsEuler * (C_L * u) *
              (liuUniversalAbsLogRatio + liuPrimeDivisorLogSum N) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLu hE0)
            (add_nonneg hR0 hD0)
        _ ≤ liuUniversalAbsEuler * (C_L * u) *
              ((liuUniversalAbsLogRatio + C_D) * u ^ 2) := by
          exact mul_le_mul_of_nonneg_left hRu
            (mul_nonneg hE0 (mul_nonneg hC_L.le hu0))
        _ = liuUniversalAbsEuler * C_L *
              (liuUniversalAbsLogRatio + C_D) * u ^ 3 := by ring
    have hS :
        SingularSeries.liuSingularSeries N ≤ C_L ^ 3 * u ^ 3 := by
      calc
        SingularSeries.liuSingularSeries N ≤ liuPrimeDivisorProduct N ^ 3 :=
          liuSingularSeries_le_liuPrimeDivisorProduct_cube N
        _ ≤ (C_L * u) ^ 3 := pow_le_pow_left₀ hL0 hLu 3
        _ = C_L ^ 3 * u ^ 3 := by ring
    have hu_le_u3 : u ≤ u ^ 3 := by
      calc
        u = u * 1 := by ring
        _ ≤ u * u ^ 2 := mul_le_mul_of_nonneg_left hu2 hu0
        _ = u ^ 3 := by ring
    have hA3 :
        liuSelbergAbsoluteMass N ≤
          liuUniversalAbsEuler * C_L * u ^ 3 :=
      hA.trans (mul_le_mul_of_nonneg_left hu_le_u3
        (mul_nonneg hE0 hC_L.le))
    have hBA :
        2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N ≤
          liuUniversalAbsEuler * C_L *
            (2 * (liuUniversalAbsLogRatio + C_D) + 1) * u ^ 3 := by
      calc
        2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N ≤
            2 * (liuUniversalAbsEuler * C_L *
              (liuUniversalAbsLogRatio + C_D) * u ^ 3) +
              liuUniversalAbsEuler * C_L * u ^ 3 := by linarith
        _ = liuUniversalAbsEuler * C_L *
              (2 * (liuUniversalAbsLogRatio + C_D) + 1) * u ^ 3 := by ring
    calc
      (2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N) *
          SingularSeries.liuSingularSeries N ≤
        (liuUniversalAbsEuler * C_L *
            (2 * (liuUniversalAbsLogRatio + C_D) + 1) * u ^ 3) *
          (C_L ^ 3 * u ^ 3) := by
            exact mul_le_mul hBA hS hS0
              (by positivity)
      _ = C * (1 + Real.log (Real.log N)) ^ 6 := by
        dsimp [C, u, t]
        ring
  simpa only [eventually_atTop] using hevent

private theorem tendsto_one_add_log_log_pow_six_div_log :
    Tendsto
      (fun N : ℕ =>
        (1 + Real.log (Real.log (N : ℝ))) ^ 6 / Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll :
      Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hcore :
      Tendsto
        (fun N : ℕ =>
          Real.log (Real.log (N : ℝ)) ^ 6 / Real.log (N : ℝ))
        atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 6 one_ne_zero).comp hlog
  apply squeeze_zero'
  · filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))] with N hN
    exact div_nonneg (by positivity) (le_trans zero_le_one hN)
  · filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      hll.eventually (eventually_ge_atTop (1 : ℝ))] with N hN ht
    have hp :
        (1 + Real.log (Real.log (N : ℝ))) ^ 6 ≤
          64 * Real.log (Real.log (N : ℝ)) ^ 6 := by
      calc
        (1 + Real.log (Real.log (N : ℝ))) ^ 6 ≤
            (2 * Real.log (Real.log (N : ℝ))) ^ 6 := by
          apply pow_le_pow_left₀
          · linarith
          · linarith
        _ = 64 * Real.log (Real.log (N : ℝ)) ^ 6 := by ring
    calc
      (1 + Real.log (Real.log (N : ℝ))) ^ 6 / Real.log (N : ℝ) ≤
          (64 * Real.log (Real.log (N : ℝ)) ^ 6) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hp (le_trans zero_le_one hN)
      _ = 64 * (Real.log (Real.log (N : ℝ)) ^ 6 / Real.log (N : ℝ)) := by ring
  · simpa using hcore.const_mul (64 : ℝ)

/-- The uniform Selberg Euler error tends to zero as `N` tends to infinity
through the even integers. -/
theorem tendsto_liuSelbergEulerError_even :
    Tendsto
      (fun N : ℕ =>
        (2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N) *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ))
      (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) := by
  obtain ⟨C, hC, N₀, hbound⟩ :=
    exists_liuSelbergEulerErrorNumerator_le_log_log_pow
  have hmajor :
      Tendsto
        (fun N : ℕ =>
          C * ((1 + Real.log (Real.log (N : ℝ))) ^ 6 /
            Real.log (N : ℝ)))
        atTop (𝓝 0) := by
    simpa using tendsto_one_add_log_log_pow_six_div_log.const_mul C
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · rw [eventually_inf_principal]
    filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))]
      with N hlogN
    intro hNeven
    have hA0 : 0 ≤ liuSelbergAbsoluteMass N := by
      unfold liuSelbergAbsoluteMass
      exact tsum_nonneg fun d => abs_nonneg _
    have hB0 : 0 ≤ liuSelbergAbsoluteLogMoment N := by
      unfold liuSelbergAbsoluteLogMoment
      exact tsum_nonneg fun d =>
        mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg d)
    exact div_nonneg
      (mul_nonneg (by positivity)
        (SingularSeries.liuSingularSeries_pos N).le)
      (le_trans zero_le_one hlogN)
  · rw [eventually_inf_principal]
    filter_upwards [eventually_ge_atTop N₀,
      hlog.eventually (eventually_ge_atTop (1 : ℝ))]
      with N hN₀ hlogN
    intro hNeven
    calc
      (2 * liuSelbergAbsoluteLogMoment N + liuSelbergAbsoluteMass N) *
            SingularSeries.liuSingularSeries N / Real.log (N : ℝ) ≤
          (C * (1 + Real.log (Real.log N)) ^ 6) /
            Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right (hbound N hN₀ hNeven)
          (le_trans zero_le_one hlogN)
      _ = C * ((1 + Real.log (Real.log (N : ℝ))) ^ 6 /
            Real.log (N : ℝ)) := by ring
  · exact hmajor.mono_left inf_le_left

end MathlibNt.SieveTheory.LiuWeight