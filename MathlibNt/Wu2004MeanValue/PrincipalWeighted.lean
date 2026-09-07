import MathlibNt.Wu2004MeanValue.PrincipalMaximal
import MathlibNt.SieveTheory.LiuPanPrincipalRemainder
import AnalyticNumberTheory.Sieve.PanMainTerm

/-!
# The complete induced-principal contribution in Wu's weighted norm

The prime count removes primes dividing the modulus. The frozen elementary
deletion bound and weighted reciprocal-totient estimate pay for this removal,
uniformly even over modulus-dependent coefficient and endpoint choices.
No nonprincipal-character estimate is asserted here.
-/

namespace Wu2004MeanValue

open Classical Finset Filter
open scoped BigOperators Topology ArithmeticFunction
open AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve

noncomputable section

def coprimePrincipalSum (S : Finset ℕ) (f r : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ S, f m * (PanPrincipal.coprimePrimeCount ⌊r m⌋₊ d - wuLi (r m))

theorem coprimePrincipalSum_sub_core_le (S : Finset ℕ) (f r : ℕ → ℝ)
    (d : ℕ) (F : ℝ) (hd : 0 < d) (hF : 0 ≤ F)
    (hf : ∀ m ∈ S, |f m| ≤ F) :
    |coprimePrincipalSum S f r d - ∑ m ∈ S, f m * principalError (r m)| ≤
      F * S.card * d.primeFactors.card := by
  have heq : coprimePrincipalSum S f r d -
      ∑ m ∈ S, f m * principalError (r m) =
      ∑ m ∈ S, f m *
        (PanPrincipal.coprimePrimeCount ⌊r m⌋₊ d - PanPrincipal.primeCount ⌊r m⌋₊) := by
    simp only [coprimePrincipalSum, principalError, realPrimeCount, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    ring
  rw [heq]
  calc
    _ ≤ ∑ m ∈ S, |f m *
        (PanPrincipal.coprimePrimeCount ⌊r m⌋₊ d - PanPrincipal.primeCount ⌊r m⌋₊)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ S, F * (d.primeFactors.card : ℝ) := by
      apply sum_le_sum
      intro m hm
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul (hf m hm)
        (PanPrincipal.abs_primeCount_sub_coprimePrimeCount_le _ d hd)
        (abs_nonneg _) hF
    _ = _ := by simp; ring

/-- The principal character with all primes dividing `d` removed, before
division by `phi(d)`. Constants precede every finite support, weight and
moving endpoint, and even all positive moduli `d <= x`. -/
theorem coprimePrincipalSum_log_saving (A F K : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ (d : ℕ) (S : Finset ℕ) (f r : ℕ → ℝ),
      0 < d → (d : ℝ) ≤ x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      |coprimePrincipalSum S f r d| ≤ C * x / Real.log x ^ A := by
  obtain ⟨J, hJ, x₁, hcore⟩ := principal_moving_sum_bound_ratio A F K hA hF
  have hlim := (isLittleO_log_rpow_rpow_atTop (A + 1)
    (show (0 : ℝ) < 1 / 2 by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  refine ⟨J + F / Real.log 2, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlim, eventually_ge_atTop x₁, eventually_ge_atTop (Real.exp 1)]
    with x hlim hx₁ hxexp
  intro d S f r hd hdx hS hf hr
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxexp
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log x := by linarith
  have hpay : Real.log x ^ (A + 1) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hlim
  have hcard : (S.card : ℝ) ≤ Real.sqrt x := by
    have hsub : S ⊆ Icc 1 ⌊Real.sqrt x⌋₊ := by
      intro m hm
      exact mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor (hS m hm).2⟩
    have h := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact (by exact_mod_cast h : (S.card : ℝ) ≤ ⌊Real.sqrt x⌋₊).trans
      (Nat.floor_le (Real.sqrt_nonneg x))
  have hdel : F * S.card * d.primeFactors.card ≤
      (F / Real.log 2) * x / Real.log x ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ ≤ F * Real.sqrt x * ((Real.log 2)⁻¹ * Real.log x) * Real.log x ^ A := by
        gcongr
        exact PanLow.primeFactors_card_le_log_of_le hd hdx
      _ = (F / Real.log 2) * Real.sqrt x * Real.log x ^ (A + 1) := by
        rw [Real.rpow_add hlog0, Real.rpow_one]
        ring
      _ ≤ (F / Real.log 2) * Real.sqrt x * Real.sqrt x := by gcongr
      _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hx0.le]
  calc
    _ ≤ |∑ m ∈ S, f m * principalError (r m)| +
        |coprimePrincipalSum S f r d - ∑ m ∈ S, f m * principalError (r m)| := by
      simpa only [add_sub_cancel] using
        abs_add_le (∑ m ∈ S, f m * principalError (r m))
          (coprimePrincipalSum S f r d - ∑ m ∈ S, f m * principalError (r m))
    _ ≤ J * x / Real.log x ^ A + (F / Real.log 2) * x / Real.log x ^ A :=
      add_le_add (hcore x hx₁ S f r hS hf hr)
        ((coprimePrincipalSum_sub_core_le S f r d F hd hF hf).trans hdel)
    _ = _ := by ring

def wuModulusWeight (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ d.primeFactors.card

theorem wuModulusWeight_nonneg (d : ℕ) : 0 ≤ wuModulusWeight d := by
  unfold wuModulusWeight
  positivity

/-- The exact source weight, not an unweighted replacement. -/
theorem wu_reciprocal_totient_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ∀ Q : ℕ, (Q : ℝ) ≤ x →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d) ≤
        C * Real.log x ^ (6 : ℝ) := by
  obtain ⟨J, hJ, hsum⟩ := panMainTotientWeightedSum_le_polylog
  refine ⟨J * (2 : ℝ) ^ (6 : ℝ), by positivity, ?_⟩
  intro x hx Q hQ
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogs : Real.log (Q + 2 : ℝ) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x * x) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul hx0.ne' hx0.ne']; ring
  calc
    _ ≤ panMainTotientWeightedSum Q := by
      change (∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d) ≤
        ∑ d ∈ range (Q + 1), wuModulusWeight d / Nat.totient d
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hd).2)
      · intro d _ _
        exact div_nonneg (wuModulusWeight_nonneg d) (by positivity)
    _ ≤ J * Real.log (Q + 2) ^ (6 : ℝ) := hsum Q
    _ ≤ J * (2 * Real.log x) ^ (6 : ℝ) := by
      gcongr
      exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) Q; linarith)
    _ = _ := by rw [Real.mul_rpow (by norm_num) hlog0.le]; ring

/-- A genuine supremum, including zero for an empty admissible domain.
Its domain is deliberately stronger than Wu needs: the support and weights
may also be selected separately for each modulus. -/
def principalModulusSup (x F K : ℝ) (d : ℕ) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ (S : Finset ℕ) (f r : ℕ → ℝ),
    (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) ∧
    (∀ m ∈ S, |f m| ≤ F) ∧
    (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) ∧
    v = |coprimePrincipalSum (S.filter (fun m => m.Coprime d)) f r d| /
      Nat.totient d})

/-- Full `mu^2(d) 3^omega(d)` modulus payment for the induced-principal
contribution, with the supremum inside the modulus sum. -/
theorem principal_weighted_sup_log_saving (A F K : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ x →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * principalModulusSup x F K d) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨J, hJ, x₁, hprincipal⟩ :=
    coprimePrincipalSum_log_saving (A + 6) F K (by linarith) hF
  obtain ⟨L, hL, hweight⟩ := wu_reciprocal_totient_sum_bound
  refine ⟨J * L, by positivity, max 2 x₁, ?_⟩
  intro x hx Q hQ
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx₁ : x₁ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hsup (d : ℕ) (hd : d ∈ Icc 1 Q) :
      principalModulusSup x F K d ≤
        (J * x / Real.log x ^ (A + 6)) / Nat.totient d := by
    apply csSup_le ⟨0, Set.mem_insert _ _⟩
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · positivity
    · obtain ⟨S, f, r, hS, hf, hr, rfl⟩ := hv
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact hprincipal x hx₁ d (S.filter (fun m => m.Coprime d)) f r
        (by have := (mem_Icc.mp hd).1; omega)
        ((by exact_mod_cast (mem_Icc.mp hd).2 : (d : ℝ) ≤ Q).trans hQ)
        (fun m hm => hS m (mem_filter.mp hm).1)
        (fun m hm => hf m (mem_filter.mp hm).1)
        (fun m hm => hr m (mem_filter.mp hm).1)
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        ((J * x / Real.log x ^ (A + 6)) / Nat.totient d) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hsup d hd) (wuModulusWeight_nonneg d)
    _ = (J * x / Real.log x ^ (A + 6)) *
        (∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (J * x / Real.log x ^ (A + 6)) * (L * Real.log x ^ (6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hweight x hx2 Q hQ) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlog0]
      field_simp

end
end Wu2004MeanValue