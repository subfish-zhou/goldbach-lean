import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalMoving
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPayment

/-! Pan (2.4)'s actual principal remainder for Liu's weight, before division by φ(q).
This does not assert any estimate for the nonprincipal-character contribution. -/
namespace AnalyticNumberTheory.LargeSieve.PanPrincipal
open Classical Finset Filter
open MathlibNt.SieveTheory.LiuWeight
open scoped BigOperators Topology
noncomputable section

def coprimePrimeCount (t q : ℕ) : ℝ :=
  ∑ p ∈ range (t + 1), if p.Prime ∧ p.Coprime q then (1 : ℝ) else 0

/-- The literal prime deletion is bounded by ω(q); q must be positive. -/
theorem abs_primeCount_sub_coprimePrimeCount_le (t q : ℕ) (hq : 0 < q) :
    |primeCount t - coprimePrimeCount t q| ≤ (q.primeFactors.card : ℝ) := by
  have h := PanLow.norm_primePrefix_sub_coprimePrimePrefix_le
    (1 : DirichletCharacter ℂ 1) t q hq
  have hev (p : ℕ) : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 := by
    have hx : (p : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hx]
    simp
  have hid : ((primeCount t - coprimePrimeCount t q : ℝ) : ℂ) =
      PanLow.primePrefix (1 : DirichletCharacter ℂ 1) t -
        PanLow.coprimePrimePrefix (1 : DirichletCharacter ℂ 1) t q := by
    unfold primeCount coprimePrimeCount PanLow.primePrefix PanLow.coprimePrimePrefix
    push_cast
    simp only [hev, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
  rw [← hid, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Exact principal error Pκ₀, not divided by φ(q), with real Li argument N/a. -/
def principalError (N A₁ A₂ q : ℕ) : ℝ :=
  ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
    liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
      ((∑ p ∈ range (N / a + 1), if p.Prime ∧ p.Coprime q then (1 : ℝ) else 0) -
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)) else 0

/-- Elementary finite triangle and harmonic summation. The prime-Li estimates
in this finite lemma are supplied unconditionally in the final theorem below. -/
theorem principalError_le_budget (N A₁ A₂ q : ℕ) (B : ℝ)
    (hq : 0 < q) (hA : A₂ ≤ N) (hB : 0 ≤ B)
    (hp : ∀ a ∈ Ioc A₁ A₂,
      |primeCount (N / a) - liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| ≤ B / a) :
    |principalError N A₁ A₂ q| ≤
      B * (1 + Real.log N) + (A₂ : ℝ) * (q.primeFactors.card : ℝ) := by
  have hpoint (a : ℕ) (ha : a ∈ Ioc A₁ A₂) :
      |coprimePrimeCount (N / a) q - liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| ≤
        B / a + (q.primeFactors.card : ℝ) := by
    have hdel := abs_primeCount_sub_coprimePrimeCount_le (N / a) q hq
    calc
      _ ≤ |coprimePrimeCount (N / a) q - primeCount (N / a)| +
          |primeCount (N / a) - liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| :=
        abs_sub_le _ _ _
      _ ≤ (q.primeFactors.card : ℝ) + B / a := by
        rw [abs_sub_comm (coprimePrimeCount _ _) (primeCount _)]
        exact add_le_add hdel (hp a ha)
      _ = _ := add_comm _ _
  unfold principalError
  calc
    _ ≤ ∑ a ∈ Ioc A₁ A₂, |if a.Coprime q then
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          (coprimePrimeCount (N / a) q -
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Ioc A₁ A₂, (B / a + (q.primeFactors.card : ℝ)) := by
      apply sum_le_sum
      intro a ha
      split_ifs with hc
      · rw [abs_mul]
        exact (mul_le_mul (abs_liuWeight_le_one _ _ _ _) (hpoint a ha)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      · simp only [abs_zero]
        positivity
    _ = B * (∑ a ∈ Ioc A₁ A₂, (a : ℝ)⁻¹) +
        ((Ioc A₁ A₂).card : ℝ) * (q.primeFactors.card : ℝ) := by
      simp [sum_add_distrib, div_eq_mul_inv, mul_sum]
    _ ≤ _ := by
      apply add_le_add (mul_le_mul_of_nonneg_left (PanLow.low_harmonic_le hA) hB)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (Ioc A₁ A₂).card ≤ A₂ by simp)

/-- Arbitrary logarithmic saving for Pan's actual principal Liu convolution error.
C and N₀ precede q and both window endpoints. The unnormalized error uses the
fixed true-Li normalization κ₀=2/log 2. No ordinary-BV convolution claim is used. -/
theorem principalError_log_saving (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ q A₁ A₂ : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.sqrt N →
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
        |principalError N A₁ A₂ q| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ s := by
  obtain ⟨K, hK, M, hprefix⟩ := primeCount_li_moving_prefix (s + 2) (by linarith)
  obtain ⟨C, hC, M', hpay⟩ := PanLow.exists_low_budget_payment s 0 K hs (by norm_num) hK
  refine ⟨C, hC, max 3 (max M M'), ?_⟩
  intro N hN q A₁ A₂ hq hqN hA
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNM : M ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hNM' : M' ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hAN : A₂ ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le hN1 (by norm_num : (2 / 3 : ℝ) ≤ 1))
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb := principalError_le_budget N A₁ A₂ q (K * N / Real.log (N : ℝ) ^ (s + 2))
    (by omega) hAN (by positivity) (by
      intro a ha
      rcases mem_Ioc.mp ha with ⟨ha, haA⟩
      apply hprefix N hNM a (by omega)
      exact (show (a : ℝ) ≤ A₂ by exact_mod_cast haA).trans hA)
  refine hb.trans ?_
  have hpaid := hpay N hNM' q A₂ 1 hq hqN hA (by simp)
  simpa only [Nat.cast_one, one_mul, add_zero] using hpaid

end
end AnalyticNumberTheory.LargeSieve.PanPrincipal