import MathlibNt.Wu2004MeanValue.LowPrefix

/-! Siegel--Walfisz at a balanced quotient, with the harmonic cofactor gain. -/

namespace Wu2004MeanValue
open Filter Finset
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanLow
open scoped Topology
noncomputable section

theorem balanced_low_primePrefix_nat_div_max (b s eta : ℝ)
    (hb : 0 ≤ b) (hs : 0 < s) (heta : 0 < eta) :
    ∃ J : ℝ, 0 < J ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ a : ℕ, 1 ≤ a → (a : ℝ) ≤ (N : ℝ) ^ (1 - eta) →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      ∀ χ : PrimitiveCharacter q, ∀ y ≤ N / a,
        ‖primePrefix χ.1 y‖ ≤
          (J * (N : ℝ) / Real.log (N : ℝ) ^ s) / (a : ℝ) := by
  obtain ⟨J, hJ, M, hSW⟩ := low_primePrefix_max (b + 1) s
  have hp := ((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (M : ℝ))
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop ((eta⁻¹ : ℝ) ^ b / eta))
  refine ⟨2 * J / eta ^ s, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hp, hl, eventually_ge_atTop (3 : ℕ)] with N hP hL hN
  dsimp only [Function.comp_apply] at hP hL
  intro a ha haN q hq hqb χ y hy
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by positivity
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hLN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hroot : (N : ℝ) ^ eta ≤ (N : ℝ) / a := by
    apply (le_div_iff₀ ha0).mpr
    calc
      _ ≤ (N : ℝ) ^ eta * (N : ℝ) ^ (1 - eta) :=
        mul_le_mul_of_nonneg_left haN (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; simp
  let T : ℕ := ⌈(N : ℝ) / a⌉₊
  have hTlow : (N : ℝ) / a ≤ (T : ℝ) := Nat.le_ceil _
  have hTroot := hroot.trans hTlow
  have hM : M ≤ T := by exact_mod_cast hP.trans hTroot
  have hlogs : eta * Real.log (N : ℝ) ≤ Real.log (T : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hN0 eta) hTroot
    rwa [Real.log_rpow hN0] at h
  have hLT : 0 < Real.log (T : ℝ) := (mul_pos heta hLN).trans_le hlogs
  have hlogs' : Real.log (N : ℝ) ≤ eta⁻¹ * Real.log (T : ℝ) := by
    have := (le_div_iff₀ heta).mpr (by simpa only [mul_comm] using hlogs)
    simpa only [div_eq_mul_inv, mul_comm] using this
  have hpay : (eta⁻¹ : ℝ) ^ b ≤ Real.log (T : ℝ) := by
    have := (div_le_iff₀ heta).mp hL
    nlinarith
  have hconductor : Real.log (N : ℝ) ^ b ≤ Real.log (T : ℝ) ^ (b + 1) := by
    calc
      _ ≤ (eta⁻¹ * Real.log (T : ℝ)) ^ b :=
        Real.rpow_le_rpow hLN.le hlogs' hb
      _ = (eta⁻¹ : ℝ) ^ b * Real.log (T : ℝ) ^ b :=
        Real.mul_rpow (by positivity) hLT.le
      _ ≤ Real.log (T : ℝ) * Real.log (T : ℝ) ^ b :=
        mul_le_mul_of_nonneg_right hpay (by positivity)
      _ = _ := by rw [Real.rpow_add hLT, Real.rpow_one]; ring
  have hyT : y ≤ T := by
    have hdiv : (N / a : ℕ) ≤ (N : ℝ) / a := by
      apply (le_div_iff₀ ha0).mpr
      exact_mod_cast Nat.div_mul_le_self N a
    exact_mod_cast (by exact_mod_cast hy : (y : ℝ) ≤ (N / a : ℕ)).trans
      (hdiv.trans hTlow)
  have hS := hSW T hM q hq (hqb.trans hconductor) χ y hyT
  have hquot1 : 1 ≤ (N : ℝ) / a :=
    (Real.one_le_rpow hN1 heta.le).trans hroot
  have hTupper : (T : ℝ) * a ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) / a by positivity)
    change (T : ℝ) < (N : ℝ) / a + 1 at h
    apply (le_div_iff₀ ha0).mp
    calc
      _ ≤ 2 * ((N : ℝ) / a) := by linarith
      _ = _ := by ring
  have hsaving : eta ^ s * Real.log (N : ℝ) ^ s ≤ Real.log (T : ℝ) ^ s := by
    rw [← Real.mul_rpow heta.le hLN.le]
    exact Real.rpow_le_rpow (by positivity) hlogs hs.le
  refine hS.trans ?_
  apply (le_div_iff₀ ha0).mpr
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hLN s)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hLT s)).mpr
  have hscale := mul_le_mul_of_nonneg_left hsaving
    (show 0 ≤ 2 * J * (N : ℝ) by positivity)
  have hsize := mul_le_mul_of_nonneg_left hTupper
    (show 0 ≤ J * (eta ^ s * Real.log (N : ℝ) ^ s) by positivity)
  rw [show 2 * J / eta ^ s * (N : ℝ) * Real.log (T : ℝ) ^ s =
    (2 * J * N * Real.log (T : ℝ) ^ s) / eta ^ s by ring]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos heta s)).mpr
  nlinarith

end
end Wu2004MeanValue