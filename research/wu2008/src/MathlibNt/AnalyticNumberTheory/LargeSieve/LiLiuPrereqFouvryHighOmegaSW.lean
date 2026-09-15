import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmegaPayment

/-!
# Uniform coprime Siegel--Walfisz transport at the growing omega cutoff

The enlarged family contains every scale `x >= T >= 1`. The bounded-scale
range is paid explicitly, so no saving-dependent lower cutoff is hidden in
the index type. Coefficient order is unchanged; the SW sieve order rises by
one to include order zero.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem highOmega_uniform_bound (K : ℝ) (hK : 0 ≤ K) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      K * (2 : ℝ) ^ (-highOmegaCutoff x) * (1 + Real.log (2 * x)) ^ B ≤ C := by
  obtain ⟨X₀, hX₀⟩ := (highOmega_eventually_log_payment K hK B 0).exists_forall_of_atTop
  let X := max X₀ 2
  have hX : 2 ≤ X := le_max_right _ _
  have hH : 0 ≤ 1 + Real.log (2 * X) := by
    have := Real.log_nonneg (show 1 ≤ 2 * X by linarith)
    linarith
  refine ⟨1 + K * (1 + Real.log (2 * X)) ^ B, by positivity, fun x hx => ?_⟩
  by_cases hlarge : X₀ ≤ x
  · have hb := hX₀ x hlarge
    simp only [pow_zero, div_one] at hb
    exact hb.trans (le_add_of_nonneg_right (mul_nonneg hK (pow_nonneg hH _)))
  · have hxX : x ≤ X := (le_of_not_ge hlarge).trans (le_max_left _ _)
    have hcut : 0 ≤ highOmegaCutoff x :=
      Real.rpow_nonneg (Real.log_nonneg hx) _
    have hpow : (2 : ℝ) ^ (-highOmegaCutoff x) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show -highOmegaCutoff x ≤ 0 by linarith)
    have hlog : 1 + Real.log (2 * x) ≤ 1 + Real.log (2 * X) := by
      gcongr
    have hlog0 : 0 ≤ 1 + Real.log (2 * x) := by
      have := Real.log_nonneg (show 1 ≤ 2 * x by linarith)
      linarith
    calc
      _ ≤ K * 1 * (1 + Real.log (2 * X)) ^ B := by gcongr
      _ ≤ _ := by nlinarith

theorem sum_abs_betaHighOmega_uniform_log_payment (k B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ, 1 ≤ T → T ≤ x →
      ∀ N : Finset ℕ, N ⊆ Ioc 0 ⌊2 * T⌋₊ → ∀ β : ℕ → ℝ,
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∑ n ∈ N, |betaHighOmega β (highOmegaCutoff x) n|) ≤
        C * T / Real.log (2 * T) ^ B := by
  obtain ⟨C, hC, hb⟩ := highOmega_uniform_bound 2 (by norm_num) (2 * k + B)
  refine ⟨C, hC, fun x T hT hTx N hN β hβ => ?_⟩
  have hx : 1 ≤ x := hT.trans hTx
  have hlog0 : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hH0 : 0 ≤ 1 + Real.log (2 * T) := by linarith
  have hHle : 1 + Real.log (2 * T) ≤ 1 + Real.log (2 * x) := by
    gcongr
  have hm := sum_abs_betaHighOmega_le k (by linarith : 1 ≤ 2 * T) N hN β hβ
    (highOmegaCutoff x)
  apply (le_div_iff₀ (pow_pos hlog0 B)).mpr
  calc
    _ ≤ ((2 : ℝ) ^ (-highOmegaCutoff x) * (2 * T) *
        (1 + Real.log (2 * T)) ^ (2 * k)) * (1 + Real.log (2 * T)) ^ B := by
      gcongr
      linarith
    _ = T * (2 * (2 : ℝ) ^ (-highOmegaCutoff x) *
        (1 + Real.log (2 * T)) ^ (2 * k + B)) := by rw [pow_add]; ring
    _ ≤ T * (2 * (2 : ℝ) ^ (-highOmegaCutoff x) *
        (1 + Real.log (2 * x)) ^ (2 * k + B)) := by gcongr
    _ ≤ T * C := mul_le_mul_of_nonneg_left (hb x hx) (by linarith)
    _ = _ := mul_comm _ _

theorem betaLowOmega_AP_abs_le (N : Finset ℕ) (β : ℕ → ℝ) (ξ : ℝ)
    {d : ℕ} (hd : 0 < d) (h b : ℕ) :
    |betaCoprimeAPDiscrepancy N (betaLowOmega β ξ) d h b| ≤
      |betaCoprimeAPDiscrepancy N β d h b| +
        2 * ∑ n ∈ N, |betaHighOmega β ξ n| := by
  have he : betaCoprimeAPDiscrepancy N β d h b =
      betaCoprimeAPDiscrepancy N (betaLowOmega β ξ) d h b +
        betaCoprimeAPDiscrepancy N (betaHighOmega β ξ) d h b := by
    conv_lhs => arg 2; ext n; rw [beta_eq_lowOmega_add_highOmega β ξ n]
    exact betaCoprimeAPDiscrepancy_add N _ _ d h b
  have he' : betaCoprimeAPDiscrepancy N (betaLowOmega β ξ) d h b =
      betaCoprimeAPDiscrepancy N β d h b -
        betaCoprimeAPDiscrepancy N (betaHighOmega β ξ) d h b := by linarith
  rw [he']
  exact (abs_sub _ _).trans (add_le_add le_rfl
    (betaCoprimeAPDiscrepancy_abs_le_twice_mass N (betaHighOmega β ξ) hd h b))

theorem BetaCoprimeSWFamily.betaLowOmega_uniform
    {ι : Type*} {κ k : ℕ} {T : ι → ℝ}
    {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, N z ⊆ Ioc 0 ⌊2 * T z⌋₊)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ)) :
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ z : ι, ∀ x : ℝ, T z ≤ x →
      ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
        |betaCoprimeAPDiscrepancy (N z) (betaLowOmega (β z) (highOmegaCutoff x)) d h b| ≤
          C * T z * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T z) ^ B := by
  intro B
  obtain ⟨C, hC, hAP⟩ := hSW B
  obtain ⟨D, hD, hmass⟩ := sum_abs_betaHighOmega_uniform_log_payment k B
  refine ⟨C + 2 * D, by positivity, ?_⟩
  intro z x hTx d h hd hh b hb
  have hlog : 0 < Real.log (2 * T z) ^ B :=
    pow_pos (Real.log_pos (by have := hT z; linarith)) B
  have htau : (fouvryTau κ h : ℝ) ≤ (fouvryTau (κ + 1) h : ℝ) := by
    exact_mod_cast fouvryTau_le_succ κ h
  have htau1 : (1 : ℝ) ≤ (fouvryTau (κ + 1) h : ℝ) := by
    exact_mod_cast one_le_fouvryTau_succ κ hh.ne'
  have hAP' : |betaCoprimeAPDiscrepancy (N z) (β z) d h b| ≤
      C * T z * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T z) ^ B := by
    apply (hAP z d h hd hh b hb).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htau (by have := hT z; positivity)) hlog.le
  have hmass' := hmass x (T z) (hT z) hTx (N z) (hN z) (β z) (hβ z)
  calc
    _ ≤ |betaCoprimeAPDiscrepancy (N z) (β z) d h b| +
        2 * ∑ n ∈ N z, |betaHighOmega (β z) (highOmegaCutoff x) n| :=
      betaLowOmega_AP_abs_le (N z) (β z) (highOmegaCutoff x) hd h b
    _ ≤ C * T z * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T z) ^ B +
        2 * (D * T z / Real.log (2 * T z) ^ B) := by gcongr
    _ ≤ C * T z * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T z) ^ B +
        2 * (D * T z * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T z) ^ B) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply div_le_div_of_nonneg_right _ hlog.le
      exact le_mul_of_one_le_right (by have := hT z; positivity) htau1
    _ = _ := by ring

structure BetaLowOmegaIndex {ι : Type*} (T : ι → ℝ) where
  index : ι
  scale : ℝ
  T_le_scale : T index ≤ scale

theorem BetaCoprimeSWFamily.betaLowOmega
    {ι : Type*} {κ k : ℕ} {T : ι → ℝ}
    {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, N z ⊆ Ioc 0 ⌊2 * T z⌋₊)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ)) :
    BetaCoprimeSWFamily (κ + 1)
      (fun z : BetaLowOmegaIndex T => T z.index)
      (fun z : BetaLowOmegaIndex T => N z.index)
      (fun z : BetaLowOmegaIndex T => betaLowOmega (β z.index) (highOmegaCutoff z.scale)) := by
  intro B
  obtain ⟨C, hC, hb⟩ := hSW.betaLowOmega_uniform hT hN hβ B
  exact ⟨C, hC, fun z => hb z.index z.scale z.T_le_scale⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
