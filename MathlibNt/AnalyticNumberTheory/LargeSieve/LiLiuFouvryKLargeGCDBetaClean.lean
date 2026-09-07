import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKLargeGCDExclusion
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanReduction

noncomputable section
open Classical Finset Filter
open scoped Topology
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Physical application of the accepted first-gcd estimate to `betaClean`.
The factor 12 is `3 * (2*T)^2 / T^2`; the beta endpoint is not confused with
its lower dyadic scale. No beta nondivisibility assumption remains. -/
theorem betaClean_wMaskedTruncated_largeGCD_dyadic_kscale
    (i k j : ℕ) (A : ℝ) {η Cscale : ℝ} (hη : 0 < η) (hCscale : 1 ≤ Cscale) :
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
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x → ∀ P : WOriginalTuple → Prop,
      (∀ t ∈ wOriginalTuples N Q a, P t → x ^ η < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P| ≤
        12 * M * T ^ 2 * x ^ (-η / 8) ∧
      (∑ m ∈ S, α m ^ 2) *
        |wMaskedTruncated M (wUniformCutoff M (x ^ η)) N Q (betaClean β a) c a P| ≤
          x ^ 2 / (Real.log x) ^ A := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_wMaskedTruncated_largeGCD_power_saving_kscale
      (k := k + 1) (j := j + 1) (by omega) (by omega) hη hCscale,
    wMaskedTruncated_largeGCD_alpha_real_log_payment_kscale
      (i := i + 1) (k := k + 1) (j := j + 1) (by omega) (by omega) (by omega) A hη hCscale]
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

