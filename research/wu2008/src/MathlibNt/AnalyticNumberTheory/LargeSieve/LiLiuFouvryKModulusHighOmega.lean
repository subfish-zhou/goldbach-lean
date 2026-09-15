import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDivisor
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKCleanPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryModulusHighOmegaPayment
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem betaClean_modulusHighOmega_signedError_bound_kscale (i k j : ℕ) {Cscale : ℝ} (hCscale : 1 ≤ Cscale)
    {U V x : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hUV : U * V ≤ x) (hUx : U ≤ x) (hVx : V ≤ x)
    (S N Q : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊U⌋₊)
    (hN : N ⊆ Ioc 0 ⌊V⌋₊) (hQ : Q ⊆ Ioc 0 ⌊x⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (a : ℤ) (ha : |(a : ℝ)| ≤ Cscale*x) (ξ : ℝ) (hω : ∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ)) :
    |signedError S N Q α (betaClean β a) c a| ≤
      (6*Cscale*(1+Real.log Cscale)^modulusHighOmegaLogExponent i k j) * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j := by
  have hxx : x ≤ Cscale*x := le_mul_of_one_le_left (by linarith) hCscale
  have hh := betaClean_modulusHighOmega_signedError_bound i k j hU hV (hx.trans hxx)
    (hUV.trans hxx) (hUx.trans hxx) (hVx.trans hxx) S N Q hS hN
    (hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hxx))) α β c hα hβ hc a ha ξ hω
  have hl := kscale_log_cost hCscale hx (modulusHighOmegaLogExponent i k j)
  calc
    _ ≤ 6*(2 : ℝ)^(-ξ)*(Cscale*x)*
        (1+Real.log (2*Cscale*x))^modulusHighOmegaLogExponent i k j := by
      simpa only [mul_assoc] using hh
    _ ≤ 6*(2 : ℝ)^(-ξ)*(Cscale*x)*
        ((1+Real.log Cscale)^modulusHighOmegaLogExponent i k j *
          (1+Real.log (2*x))^modulusHighOmegaLogExponent i k j) := by gcongr
    _ = _ := by ring

private theorem kModulusHighOmega_dyadic_support {M : ℝ} (hM : 1 ≤ M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) :
    S ⊆ Ioc 0 ⌊2 * M⌋₊ := by
  intro m hm
  refine mem_Ioc.mpr ⟨?_, Nat.le_floor (hS m hm).2⟩
  have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
  exact_mod_cast this

theorem betaClean_modulusHighOmega_signedError_dyadic_bound_kscale (i k j : ℕ)
    {Cscale : ℝ} (hCscale : 1 ≤ Cscale)
    {M T L x : ℝ} (hM : 1 ≤ M) (hT : 1 ≤ T) (hx : 1 ≤ x)
    (hscale : x = 4 * M * T) (hLx : L ≤ x)
    (S N Q : Finset ℕ)
    (hS : ∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M)
    (hN : ∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T)
    (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (α β c : ℕ → ℝ)
    (hα : ∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ))
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ))
    (a : ℤ) (ha : |(a : ℝ)| ≤ Cscale*x)
    (ξ : ℝ) (hω : ∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ)) :
    |signedError S N Q α (betaClean β a) c a| ≤
      (6*Cscale*(1+Real.log Cscale)^modulusHighOmegaLogExponent i k j) * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j := by
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by linarith
  exact betaClean_modulusHighOmega_signedError_bound_kscale i k j hCscale
    (by linarith : 1 ≤ 2 * M) (by linarith : 1 ≤ 2 * T) hx
    (by nlinarith : (2 * M) * (2 * T) ≤ x)
    (by nlinarith : 2 * M ≤ x) (by nlinarith : 2 * T ≤ x)
    S N Q (kModulusHighOmega_dyadic_support hM S hS)
    (kModulusHighOmega_dyadic_support hT N hN)
    (hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hLx)))
    α β c hα hβ hc a ha ξ hω

/-- The threshold depends only on the fixed three orders and logarithmic
saving. Modulus signs and the residue remain arbitrary after that threshold. -/
theorem betaClean_modulusHighOmega_signedError_dyadic_log_payment_kscale (i k j A : ℕ)
    {Cscale : ℝ} (hCscale : 1 ≤ Cscale) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → x = 4 * M * T → L ≤ x →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      (∀ q ∈ Q, c q ≠ 0 → highOmegaCutoff x < (q.primeFactors.card : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale*x →
      |signedError S N Q α (betaClean β a) c a| ≤ x / Real.log x ^ A := by
  have hlogC := Real.log_nonneg hCscale
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    highOmega_eventually_log_payment (6*Cscale*(1+Real.log Cscale)^modulusHighOmegaLogExponent i k j) (by positivity) (modulusHighOmegaLogExponent i k j) A]
    with x hx hpay
  intro M T L hM hT hscale hLx S N Q hS hN hQ α β c hα hβ hc hω a ha
  calc
    _ ≤ (6*Cscale*(1+Real.log Cscale)^modulusHighOmegaLogExponent i k j) * (2 : ℝ) ^ (-highOmegaCutoff x) * x *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j :=
      betaClean_modulusHighOmega_signedError_dyadic_bound_kscale i k j hCscale hM hT hx hscale hLx
        S N Q hS hN hQ α β c hα hβ hc a ha (highOmegaCutoff x) hω
    _ = x * ((6*Cscale*(1+Real.log Cscale)^modulusHighOmegaLogExponent i k j) * (2 : ℝ) ^ (-highOmegaCutoff x) *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j) := by ring
    _ ≤ x * (1 / Real.log x ^ A) :=
      mul_le_mul_of_nonneg_left hpay (by linarith)
    _ = _ := by ring

theorem modulusHighOmega_signedError_dyadic_log_payment_kscale (i k j A : ℕ)
    {Cscale ε : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → x = 4 * M * T →
      x ^ ε ≤ T → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      (∀ q ∈ Q, c q ≠ 0 → highOmegaCutoff x < (q.primeFactors.card : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
      |signedError S N Q α β c a| ≤ x / Real.log x ^ A := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ),
    betaClean_modulusHighOmega_signedError_dyadic_log_payment_kscale i k j (A + 1) hCscale,
    kClean_signedError_log_payment i k j (A + 1) hCscale hε] with x hx hlog hclean hdiv
  intro M T L hM hT hL hscale hlow hlevel S N Q hS hN hQ α β c hα hβ hc hω a ha hax
  have hLx : L ≤ x := hlevel.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx
      (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have hcpaid := hclean M T L hM hT hscale hLx S N Q hS hN hQ α β c hα hβ hc hω a hax
  have hdpaid := (hdiv M T L hM hT hL hscale hlow hlevel
    S N Q hS hN hQ α β c hα hβ hc a ha hax).1
  have hpay : 2 * (x / Real.log x ^ (A + 1)) ≤ x / Real.log x ^ A := by
    rw [pow_succ, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < Real.log x by linarith)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x / Real.log x ^ A)
      (show 0 ≤ Real.log x - 2 by linarith)]
  calc
    _ = |signedError S N Q α (betaClean β a) c a +
        signedError S N Q α (betaDivisorPart β a) c a| := by
      rw [← signedError_eq_clean_add_divisorPart]
    _ ≤ |signedError S N Q α (betaClean β a) c a| +
        |signedError S N Q α (betaDivisorPart β a) c a| := abs_add_le _ _
    _ ≤ x / Real.log x ^ (A + 1) + x / Real.log x ^ (A + 1) :=
      add_le_add hcpaid hdpaid
    _ = 2 * (x / Real.log x ^ (A + 1)) := by ring
    _ ≤ _ := hpay


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
