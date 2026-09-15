import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaClean
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmallDeltaPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModeBound

/-!
# Uniform Siegel--Walfisz transport under divisor deletion

Every constant is chosen before the original family index, residue and scale.
The extra divisor order absorbs the deleted mass even when the original
sieve order is zero. The logarithmic payment holds at every scale at least one.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

theorem betaCoprimeAPDiscrepancy_add (N : Finset ℕ) (β γ : ℕ → ℝ)
    (d h b : ℕ) :
    betaCoprimeAPDiscrepancy N (fun n => β n + γ n) d h b =
      betaCoprimeAPDiscrepancy N β d h b +
        betaCoprimeAPDiscrepancy N γ d h b := by
  have hi (P : Prop) [Decidable P] (u v : ℝ) :
      (if P then u + v else 0) =
        (if P then u else 0) + (if P then v else 0) := by
    split_ifs <;> simp
  simp only [betaCoprimeAPDiscrepancy, coprimeMass, hi, sum_add_distrib, add_div]
  ring

theorem betaCoprimeAPDiscrepancy_abs_le_twice_mass (N : Finset ℕ)
    (β : ℕ → ℝ) {d : ℕ} (hd : 0 < d) (h b : ℕ) :
    |betaCoprimeAPDiscrepancy N β d h b| ≤ 2 * ∑ n ∈ N, |β n| := by
  have hφ : (1 : ℝ) ≤ d.totient := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have hAP : |∑ n ∈ N, if n.Coprime h ∧ Nat.ModEq d n b then β n else 0| ≤
      ∑ n ∈ N, |β n| := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n _
    split_ifs <;> simp
  have hmain : |coprimeMass N β (d * h) / (d.totient : ℝ)| ≤ ∑ n ∈ N, |β n| := by
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg d.totient : (0 : ℝ) ≤ d.totient)]
    exact (div_le_self (abs_nonneg _) hφ).trans
      (coprimeMass_abs_le_sum_abs N β (d * h))
  exact (abs_sub _ _).trans (by linarith)

/-- Deleting beta on divisors changes any coprime-sieved AP discrepancy
by at most twice the actual deleted mass. -/
theorem betaClean_AP_abs_le (N : Finset ℕ) (β : ℕ → ℝ) (a : ℤ)
    {d : ℕ} (hd : 0 < d) (h b : ℕ) :
    |betaCoprimeAPDiscrepancy N (betaClean β a) d h b| ≤
      |betaCoprimeAPDiscrepancy N β d h b| +
        2 * ∑ n ∈ N, |betaDivisorPart β a n| := by
  have he : betaCoprimeAPDiscrepancy N β d h b =
      betaCoprimeAPDiscrepancy N (betaClean β a) d h b +
        betaCoprimeAPDiscrepancy N (betaDivisorPart β a) d h b := by
    conv_lhs => arg 2; ext n; rw [beta_eq_clean_add_divisorPart β a n]
    exact betaCoprimeAPDiscrepancy_add N _ _ d h b
  have he' : betaCoprimeAPDiscrepancy N (betaClean β a) d h b =
      betaCoprimeAPDiscrepancy N β d h b -
        betaCoprimeAPDiscrepancy N (betaDivisorPart β a) d h b := by
    linarith
  rw [he']
  exact (abs_sub _ _).trans (add_le_add le_rfl
    (betaCoprimeAPDiscrepancy_abs_le_twice_mass N (betaDivisorPart β a) hd h b))

/-- A uniform elementary log-versus-power bound, including the compact
range `1 ≤ T` and the saving order `B = 0`. -/
theorem betaClean_log_pow_le_const_rpow (B : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ L : ℝ, 0 < L ∧ ∀ T : ℝ, 1 ≤ T →
      Real.log (2 * T) ^ B ≤ L * T ^ θ := by
  let ρ : ℝ := θ / ((B : ℝ) + 1)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρθ : ρ * B ≤ θ := by
    dsimp [ρ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) + 1)).mpr
    nlinarith
  refine ⟨(2 : ℝ) ^ θ / ρ ^ B, by positivity, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hbase : 1 ≤ 2 * T := by linarith
  have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg hbase
  calc
    _ ≤ ((2 * T) ^ ρ / ρ) ^ B :=
      pow_le_pow_left₀ hlog (Real.log_le_rpow_div (by positivity) hρ) B
    _ = (2 * T) ^ (ρ * B) / ρ ^ B := by
      rw [div_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 2 * T)]
    _ ≤ (2 * T) ^ θ / ρ ^ B := by
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hbase hρθ) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT0]; ring

/-- Divisor deletion is uniformly cheaper than every SW logarithmic error
at `T ≥ x^ε`; neither `T ≤ x` nor interval support is needed. -/
theorem sum_abs_betaDivisorPart_uniform_log_payment (k B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x T : ℝ, 1 ≤ x → 1 ≤ T → x ^ ε ≤ T →
      ∀ a : ℤ, a ≠ 0 → (a.natAbs : ℝ) ≤ x →
      ∀ N : Finset ℕ, ∀ β : ℕ → ℝ,
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∑ n ∈ N, |betaDivisorPart β a n|) ≤ C * T / Real.log (2 * T) ^ B := by
  obtain ⟨D, hD, hmass⟩ := sum_abs_betaDivisorPart_uniform_rpow k
    (show 0 < ε / 2 by positivity)
  obtain ⟨L, hL, hlog⟩ := betaClean_log_pow_le_const_rpow B
    (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨D * L, by positivity, fun x T hx hT hxT a ha hax N β hβ => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hsqrt : x ^ (ε / 2) ≤ T ^ (1 / 2 : ℝ) := by
    calc
      _ = (x ^ ε) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_mul hx0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hx0 _) hxT (by norm_num)
  have hmass' : (∑ n ∈ N, |betaDivisorPart β a n|) ≤ D * T ^ (1 / 2 : ℝ) :=
    (hmass x hx a ha hax N β hβ).trans (mul_le_mul_of_nonneg_left hsqrt hD.le)
  apply (le_div_iff₀ (pow_pos (Real.log_pos (by linarith : 1 < 2 * T)) B)).mpr
  calc
    _ ≤ (D * T ^ (1 / 2 : ℝ)) * (L * T ^ (1 / 2 : ℝ)) :=
      mul_le_mul hmass' (hlog T hT)
        (pow_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2 * T)) B) (by positivity)
    _ = (D * L) * (T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add (by linarith : 0 < T)]; norm_num

/-- Uniform transport with all changing arithmetic data after the constant.
The original coefficient order `k` and SW sieve order `κ` are independent. -/
theorem BetaCoprimeSWFamily.betaClean_uniform
    {ι : Type*} {κ k : ℕ} {T : ι → ℝ}
    {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ i : ι, 1 ≤ T i → ∀ x : ℝ, 1 ≤ x → x ^ ε ≤ T i →
      ∀ a : ℤ, a ≠ 0 → (a.natAbs : ℝ) ≤ x →
      ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
        |betaCoprimeAPDiscrepancy (N i) (betaClean (β i) a) d h b| ≤
          C * T i * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T i) ^ B := by
  intro B
  obtain ⟨C, hC, hAP⟩ := hSW B
  obtain ⟨D, hD, hmass⟩ := sum_abs_betaDivisorPart_uniform_log_payment k B hε
  refine ⟨C + 2 * D, by positivity, ?_⟩
  intro i hT x hx hxT a ha hax d h hd hh b hb
  have hlog : 0 < Real.log (2 * T i) ^ B :=
    pow_pos (Real.log_pos (by linarith : 1 < 2 * T i)) B
  have htau : (fouvryTau κ h : ℝ) ≤ (fouvryTau (κ + 1) h : ℝ) := by
    exact_mod_cast fouvryTau_le_succ κ h
  have htau1 : (1 : ℝ) ≤ (fouvryTau (κ + 1) h : ℝ) := by
    exact_mod_cast one_le_fouvryTau_succ κ hh.ne'
  have hAP' : |betaCoprimeAPDiscrepancy (N i) (β i) d h b| ≤
      C * T i * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T i) ^ B := by
    apply (hAP i d h hd hh b hb).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htau (by positivity)) hlog.le
  have hmass' := hmass x (T i) hx hT hxT a ha hax (N i) (β i) (hβ i)
  calc
    _ ≤ |betaCoprimeAPDiscrepancy (N i) (β i) d h b| +
        2 * ∑ n ∈ N i, |betaDivisorPart (β i) a n| :=
      betaClean_AP_abs_le (N i) (β i) a hd h b
    _ ≤ C * T i * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T i) ^ B +
        2 * (D * T i / Real.log (2 * T i) ^ B) := by gcongr
    _ ≤ C * T i * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T i) ^ B +
        2 * (D * T i * (fouvryTau (κ + 1) h : ℝ) / Real.log (2 * T i) ^ B) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply div_le_div_of_nonneg_right _ hlog.le
      exact le_mul_of_one_le_right (by positivity) htau1
    _ = _ := by ring

/-- The family really contains all admissible old indices, residues and
scales, not only a fixed residue chosen before the SW constants. -/
structure BetaCleanIndex {ι : Type*} (T : ι → ℝ) (ε : ℝ) where
  index : ι
  residue : ℤ
  scale : ℝ
  one_le_T : 1 ≤ T index
  one_le_scale : 1 ≤ scale
  residue_ne_zero : residue ≠ 0
  residue_le_scale : (residue.natAbs : ℝ) ≤ scale
  scale_rpow_le : scale ^ ε ≤ T index

theorem BetaCoprimeSWFamily.betaClean
    {ι : Type*} {κ k : ℕ} {T : ι → ℝ}
    {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    BetaCoprimeSWFamily (κ + 1)
      (fun j : BetaCleanIndex T ε => T j.index)
      (fun j : BetaCleanIndex T ε => N j.index)
      (fun j : BetaCleanIndex T ε => betaClean (β j.index) j.residue) := by
  intro B
  obtain ⟨C, hC, hbound⟩ := hSW.betaClean_uniform hβ hε B
  refine ⟨C, hC, fun j => ?_⟩
  exact hbound j.index j.one_le_T j.scale j.one_le_scale j.scale_rpow_le
    j.residue j.residue_ne_zero j.residue_le_scale

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
