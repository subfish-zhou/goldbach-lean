import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModeReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWLargeGCDExclusion

/-!
# Clean beta at the original C.2 entry and in the first gcd exclusion

The original error is reduced to the genuine nonzero W mode of the constructed
clean sequence. Its SW input is proved for the enlarged changing-residue family.
The first large-gcd exclusion is then applied with upper beta endpoint `2*T`,
not `T`. No claim is made for the other four exclusions or the IV.3 remainder.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The original, uncleaned signed error after honest divisor deletion and
zero-mode payment. All orders, including the SW order, may be zero. -/
theorem signedError_sq_le_clean_nonzeroMode_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T z = x →
      x ^ ε ≤ T z → T z ≤ x ^ (1 / 10 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      signedError S (N z) Q α (β z) c a ^ 2 ≤
        2 * (∑ m ∈ S, α m ^ 2) *
          smoothWNonzeroMode M (N z) Q (betaClean (β z) a) c a +
          x ^ 2 / Real.log x ^ A := by
  have hcleanβ : ∀ z : BetaCleanIndex T ε, ∀ n ∈ N z.index,
      |betaClean (β z.index) z.residue n| ≤ (fouvryTau (k + 1) n : ℝ) := by
    intro z n hn
    exact ((abs_betaClean_le _ _ _).trans (hβ z.index n hn)).trans
      (by exact_mod_cast fouvryTau_le_succ k n)
  have hreduce := signedError_sq_le_nonzeroMode_c2
    (k := k + 1) (ℓ := i + 1) (j := j + 1) (by omega) (by omega) (by omega)
    (A + 2) (hSW.betaClean hβ hε)
    (fun z : BetaCleanIndex T ε => z.one_le_T)
    (fun z => hN z.index) hcleanβ hε
  filter_upwards [hreduce, betaClean_signedError_log_payment i k j (A + 2) hε,
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)]
    with x hreduce hdelete hx hlog
  intro z M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  let z' : BetaCleanIndex T ε :=
    ⟨z, a, x, hT z, hx, ha, by simpa using hax, hlow⟩
  have hα' : ∀ m ∈ S, |α m| ≤ (fouvryTau (i + 1) m : ℝ) := by
    intro m hm
    exact (hα m hm).trans (by exact_mod_cast fouvryTau_le_succ i m)
  have hc' : ∀ q ∈ Q, |c q| ≤ (fouvryTau (j + 1) q : ℝ) := by
    intro q hq
    exact (hc q hq).trans (by exact_mod_cast fouvryTau_le_succ j q)
  have hclean := hreduce z' M L hM hL hscale hlow hhigh hlevel
    S Q hS hQ α c hα' hc' a
  have hdeleted := (hdelete M (T z) L hM (hT z) hL hscale.symm hlow hlevel
    S (N z) Q hS (hN z) hQ α (β z) c hα (hβ z) hc a ha hax).1
  have hlog0 : 0 < Real.log x := by linarith
  have hB0 : 0 ≤ x / Real.log x ^ (A + 2) := by positivity
  have hdeletedSq :
      signedError S (N z) Q α (betaDivisorPart (β z) a) c a ^ 2 ≤
        (x / Real.log x ^ (A + 2)) ^ 2 := by
    nlinarith [sq_abs (signedError S (N z) Q α (betaDivisorPart (β z) a) c a),
      mul_nonneg (sub_nonneg.mpr hdeleted)
        (add_nonneg hB0 (abs_nonneg (signedError S (N z) Q α
          (betaDivisorPart (β z) a) c a)))]
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
  have hsplit := signedError_eq_clean_add_divisorPart S (N z) Q α (β z) c a
  have hsq : signedError S (N z) Q α (β z) c a ^ 2 ≤
      2 * signedError S (N z) Q α (betaClean (β z) a) c a ^ 2 +
        2 * signedError S (N z) Q α (betaDivisorPart (β z) a) c a ^ 2 := by
    rw [hsplit]
    nlinarith [sq_nonneg (signedError S (N z) Q α (betaClean (β z) a) c a -
      signedError S (N z) Q α (betaDivisorPart (β z) a) c a)]
  dsimp only [z'] at hclean
  linarith

/-- Physical application of the accepted first-gcd estimate to `betaClean`.
The factor 12 is `3 * (2*T)^2 / T^2`; the beta endpoint is not confused with
its lower dyadic scale. No beta nondivisibility assumption remains. -/
theorem betaClean_wMaskedTruncated_largeGCD_dyadic
    (i k j : ℕ) (A : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → 4 * M * T = x → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ x → ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P| ≤
        12 * M * T ^ 2 * x ^ (-η / 8) ∧
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P| ≤
          x ^ 2 / (Real.log x) ^ A := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_wMaskedTruncated_largeGCD_power_saving
      (k := k + 1) (j := j + 1) (by omega) (by omega) hη,
    wMaskedTruncated_largeGCD_alpha_real_log_payment
      (i := i + 1) (k := k + 1) (j := j + 1) (by omega) (by omega) (by omega) A hη]
    with x hx hpower hpay
  intro M T L hM hT _ hscale hlevel S N Q hS hN hQ α β c hα hβ hc a ha P hP
  have hN' : N ⊆ Ioc 0 ⌊2 * T⌋₊ := by
    intro n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor (hN n hn).2⟩
    have : (0 : ℝ) < n := by have := (hN n hn).1; linarith
    exact_mod_cast this
  have hLx : L ≤ x := hlevel.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have hQ' : Q ⊆ Ioc 0 ⌊x⌋₊ :=
    hQ.trans (Ioc_subset_Ioc_right (Nat.floor_mono hLx))
  have hMT : M * (2 * T) ≤ x := by nlinarith
  have hT' : 1 ≤ 2 * T := by linarith
  have hα' : ∀ m ∈ S, |α m| ≤ (fouvryTau (i + 1) m : ℝ) := by
    intro m hm
    exact (hα m hm).trans (by exact_mod_cast fouvryTau_le_succ i m)
  have hβ' : ∀ n ∈ N, |betaClean β a n| ≤ (fouvryTau (k + 1) n : ℝ) := by
    intro n hn
    exact ((abs_betaClean_le _ _ _).trans (hβ n hn)).trans
      (by exact_mod_cast fouvryTau_le_succ k n)
  have hc' : ∀ q ∈ Q, |c q| ≤ (fouvryTau (j + 1) q : ℝ) := by
    intro q hq
    exact (hc q hq).trans (by exact_mod_cast fouvryTau_le_succ j q)
  have hs : ∀ n ∈ N, betaClean β a n ≠ 0 → ¬(n : ℤ) ∣ a :=
    fun _ _ hn => betaClean_nonzero_not_dvd hn
  refine ⟨?_, hpay M (2 * T) hM hT' hMT S N Q hS hN' hQ'
    α (betaClean β a) c hα' hβ' hc' a ha hs P hP⟩
  exact (hpower M (2 * T) hM hT' hMT N Q hN' hQ'
    (betaClean β a) c hβ' hc' a ha hs P hP).trans_eq (by ring)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
