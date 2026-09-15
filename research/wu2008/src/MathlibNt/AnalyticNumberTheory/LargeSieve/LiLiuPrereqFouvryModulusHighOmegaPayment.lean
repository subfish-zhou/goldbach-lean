import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryModulusHighOmegaError
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanPayment

/-!
# Uniform payment for high-omega signed modulus weights

At the growing cutoff `(log x)^(1/5)`, the clean error is `O(x/log^A x)`
uniformly in all changing dyadic scales, coefficients, and residues. For
original beta a separate divisor-deletion cost includes the equality
progression. Its eventual payment uses a positive lower exponent for the
beta scale and the C.2 level bound; it is not exponentially small in omega.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem modulusHighOmega_dyadic_support {M : ℝ} (hM : 1 ≤ M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) :
    S ⊆ Ioc 0 ⌊2 * M⌋₊ := by
  intro m hm
  refine mem_Ioc.mpr ⟨?_, Nat.le_floor (hS m hm).2⟩
  have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
  exact_mod_cast this

/-- The exact dyadic specialization uses the upper endpoints `2*M, 2*T`.
It does not need a positive beta-scale exponent or a nonzero residue. -/
theorem betaClean_modulusHighOmega_signedError_dyadic_bound (i k j : ℕ)
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
    (a : ℤ) (ha : |(a : ℝ)| ≤ x)
    (ξ : ℝ) (hω : ∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ)) :
    |signedError S N Q α (betaClean β a) c a| ≤
      6 * (2 : ℝ) ^ (-ξ) * x *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j := by
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by linarith
  exact betaClean_modulusHighOmega_signedError_bound i k j
    (by linarith : 1 ≤ 2 * M) (by linarith : 1 ≤ 2 * T) hx
    (by nlinarith : (2 * M) * (2 * T) ≤ x)
    (by nlinarith : 2 * M ≤ x) (by nlinarith : 2 * T ≤ x)
    S N Q (modulusHighOmega_dyadic_support hM S hS)
    (modulusHighOmega_dyadic_support hT N hN)
    (hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hLx)))
    α β c hα hβ hc a ha ξ hω

/-- The threshold depends only on the fixed three orders and logarithmic
saving. Modulus signs and the residue remain arbitrary after that threshold. -/
theorem betaClean_modulusHighOmega_signedError_dyadic_log_payment (i k j A : ℕ) :
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
      ∀ a : ℤ, |(a : ℝ)| ≤ x →
      |signedError S N Q α (betaClean β a) c a| ≤ x / Real.log x ^ A := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    highOmega_eventually_log_payment 6 (by norm_num) (modulusHighOmegaLogExponent i k j) A]
    with x hx hpay
  intro M T L hM hT hscale hLx S N Q hS hN hQ α β c hα hβ hc hω a ha
  calc
    _ ≤ 6 * (2 : ℝ) ^ (-highOmegaCutoff x) * x *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j :=
      betaClean_modulusHighOmega_signedError_dyadic_bound i k j hM hT hx hscale hLx
        S N Q hS hN hQ α β c hα hβ hc a ha (highOmegaCutoff x) hω
    _ = x * (6 * (2 : ℝ) ^ (-highOmegaCutoff x) *
        (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j) := by ring
    _ ≤ x * (1 / Real.log x ^ A) :=
      mul_le_mul_of_nonneg_left hpay (by linarith)
    _ = _ := by ring

/-- Original beta, with an explicit additional term covering divisor indices
and `m*n=a`. No exponential cutoff gain is asserted for that additional term. -/
theorem modulusHighOmega_eventually_signedError_bound (i k j : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → x = 4 * M * T → L ≤ x →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      ∀ ξ : ℝ, (∀ q ∈ Q, c q ≠ 0 → ξ < (q.primeFactors.card : ℝ)) →
      |signedError S N Q α β c a| ≤
        6 * (2 : ℝ) ^ (-ξ) * x *
          (1 + Real.log (2 * x)) ^ modulusHighOmegaLogExponent i k j +
        4 * (M + L) * x ^ (3 * δ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    betaPayment_eventually_signedError_bound i k j hδ] with x hx hdiv
  intro M T L hM hT hL hscale hLx S N Q hS hN hQ α β c hα hβ hc a ha hax ξ hω
  rw [signedError_eq_clean_add_divisorPart]
  exact (abs_add_le _ _).trans (add_le_add
    (betaClean_modulusHighOmega_signedError_dyadic_bound i k j hM hT hx hscale hLx
      S N Q hS hN hQ α β c hα hβ hc a hax ξ hω)
    (hdiv M T L hM hT hL hscale hLx S N Q hS hN hQ α β c hα hβ hc a ha hax))

/-- Genuine original-beta payment under the C.2 scale restrictions.
All orders may be zero, and one threshold works for every changing residue
in `0 < |a| ≤ x`, including those with equality progressions. -/
theorem modulusHighOmega_signedError_dyadic_log_payment (i k j A : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
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
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      |signedError S N Q α β c a| ≤ x / Real.log x ^ A := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ),
    betaClean_modulusHighOmega_signedError_dyadic_log_payment i k j (A + 1),
    betaClean_signedError_log_payment i k j (A + 1) hε] with x hx hlog hclean hdiv
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
