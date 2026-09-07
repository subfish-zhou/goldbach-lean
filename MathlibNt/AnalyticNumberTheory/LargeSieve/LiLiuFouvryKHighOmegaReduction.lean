import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKFirstGCD
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKHighOmega
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaReduction
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem highOmega_original_signedError_log_payment_kscale (i k j A : ℕ)
    {Cscale ε : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 4 * M * T = x →
      x ^ ε ≤ T → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
      |signedError S N Q α (betaHighOmega β (highOmegaCutoff x)) c a| ≤
          x / Real.log x ^ A ∧
      |signedError S N Q α β c a -
          signedError S N Q α (betaLowOmega β (highOmegaCutoff x)) c a| ≤
        x / Real.log x ^ A := by
  filter_upwards [
    kClean_signedError_log_payment i k j (A + 1) hCscale hε,
    betaClean_highOmega_signedError_log_payment_kscale i k j (A + 1) hCscale,
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)]
    with x hdiv hhigh hx hlog
  intro M T L hM hT hL hscale hlow hlevel S N Q hS hN hQ α β c hα hβ hc a ha hax
  have hS' : S ⊆ Ioc 0 ⌊2 * M⌋₊ := by
    intro m hm
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor (hS m hm).2⟩
    have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
    exact_mod_cast this
  have hN' : N ⊆ Ioc 0 ⌊2 * T⌋₊ := by
    intro n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor (hN n hn).2⟩
    have : (0 : ℝ) < n := by have := (hN n hn).1; linarith
    exact_mod_cast this
  have hLx : L ≤ x := hlevel.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have hQx : Q ⊆ Ioc 0 ⌊x⌋₊ :=
    hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hLx))
  have hhighβ : ∀ n ∈ N,
      |betaHighOmega β (highOmegaCutoff x) n| ≤ (fouvryTau k n : ℝ) :=
    fun n hn => (abs_betaHighOmega_le _ _ _).trans (hβ n hn)
  have hd := (hdiv M T L hM hT hL hscale.symm hlow hlevel S N Q hS hN hQ
    α (betaHighOmega β (highOmegaCutoff x)) c hα hhighβ hc a ha hax).1
  have hh := (hhigh (2 * M) (2 * T) (by linarith) (by linarith)
    (by nlinarith) (by nlinarith) (by nlinarith) S N Q hS' hN' hQx
    α β c hα hβ hc a hax).1
  have hpay : 2 * (x / Real.log x ^ (A + 1)) ≤ x / Real.log x ^ A := by
    rw [pow_succ, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < Real.log x)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlog
      (by positivity : 0 ≤ x / Real.log x ^ A)
  have hb : |signedError S N Q α (betaHighOmega β (highOmegaCutoff x)) c a| ≤
      x / Real.log x ^ A := by
    rw [signedError_eq_clean_add_divisorPart, betaClean_highOmega_comm]
    exact (abs_add_le _ _).trans ((add_le_add hh hd).trans (by linarith))
  refine ⟨hb, ?_⟩
  rw [signedError_eq_lowOmega_add_highOmega S N Q α β c a (highOmegaCutoff x),
    add_sub_cancel_left]
  exact hb

theorem signedError_sq_le_lowOmega_firstGCD_truncated_kscale
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {Cscale ε η : ℝ} (hCscale : 1 ≤ Cscale) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T z = x →
      x ^ ε ≤ T z → T z ≤ x ^ (1 / 9 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale*x →
      signedError S (N z) Q α (β z) c a ^ 2 ≤
        4 * (∑ m ∈ S, α m ^ 2) *
          wMaskedTruncated M (wUniformCutoff M (x ^ η)) (N z) Q
            (betaClean (β z) a) c a
            (fun t => (t.2.1.gcd t.2.2 : ℝ) ≤ x ^ η ∧
              (t.2.1.primeFactors.card : ℝ) ≤ highOmegaCutoff x ∧
              (t.2.2.primeFactors.card : ℝ) ≤ highOmegaCutoff x) +
          x ^ 2 / Real.log x ^ A := by
  have hN' : ∀ z, N z ⊆ Ioc 0 ⌊2 * T z⌋₊ := by
    intro z n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor (hN z n hn).2⟩
    have : (0 : ℝ) < n := by have := (hN z n hn).1; have := hT z; linarith
    exact_mod_cast this
  have hlowβ : ∀ z : BetaLowOmegaIndex T, ∀ n ∈ N z.index,
      |betaLowOmega (β z.index) (highOmegaCutoff z.scale) n| ≤ (fouvryTau k n : ℝ) :=
    fun z n hn => (abs_betaLowOmega_le _ _ _).trans (hβ z.index n hn)
  have hreduce := signedError_sq_le_clean_firstGCD_truncated_kscale
    (i := i) (j := j) (A + 2) (hSW.betaLowOmega hT hN' hβ)
    (fun z : BetaLowOmegaIndex T => hT z.index) (fun z => hN z.index) hlowβ hCscale hε hη
  filter_upwards [hreduce, highOmega_original_signedError_log_payment_kscale i k j (A + 2) hCscale hε,
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (3 : ℝ)]
    with x hreduce hdelete hx hlog
  intro z M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  let z' : BetaLowOmegaIndex T := ⟨z, x, by nlinarith [hT z]⟩
  have he := hreduce z' M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  dsimp only [z'] at he
  rw [betaClean_lowOmega_comm, wMaskedTruncated_betaLowOmega] at he
  have hd := (hdelete M (T z) L hM (hT z) hL hscale hlow hlevel S (N z) Q hS
    (hN z) hQ α (β z) c hα (hβ z) hc a ha hax).1
  have hlog0 : 0 < Real.log x := by linarith
  have hdSq :
      signedError S (N z) Q α (betaHighOmega (β z) (highOmegaCutoff x)) c a ^ 2 ≤
        (x / Real.log x ^ (A + 2)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hlogA : 1 ≤ Real.log x ^ (A + 2) :=
    one_le_pow₀ (by linarith : 1 ≤ Real.log x)
  have hdelpay : (x / Real.log x ^ (A + 2)) ^ 2 ≤
      x ^ 2 / Real.log x ^ (A + 2) := by
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg x) (pow_pos hlog0 _)
    nlinarith
  have hpay : 4 * (x ^ 2 / Real.log x ^ (A + 2)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_add, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hlog0)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (show 0 ≤ Real.log x ^ 2 - 4 by nlinarith)]
  have hsq : signedError S (N z) Q α (β z) c a ^ 2 ≤
      2 * signedError S (N z) Q α (betaLowOmega (β z) (highOmegaCutoff x)) c a ^ 2 +
        2 * signedError S (N z) Q α (betaHighOmega (β z) (highOmegaCutoff x)) c a ^ 2 := by
    rw [signedError_eq_lowOmega_add_highOmega S (N z) Q α (β z) c a (highOmegaCutoff x)]
    nlinarith [sq_nonneg (signedError S (N z) Q α
        (betaLowOmega (β z) (highOmegaCutoff x)) c a -
      signedError S (N z) Q α (betaHighOmega (β z) (highOmegaCutoff x)) c a)]
  linarith


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
