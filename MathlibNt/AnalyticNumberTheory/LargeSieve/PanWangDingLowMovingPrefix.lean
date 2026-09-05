import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPrimePrefix

/-! Uniform transport to the natural quotient in Pan's low-conductor endpoint. -/
namespace AnalyticNumberTheory.LargeSieve.PanLow
open Filter
open scoped Topology
noncomputable section

private theorem eventually_nat_div_quarter :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℕ, 1 ≤ a →
      (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N / a : ℕ) := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hg, eventually_ge_atTop (1 : ℕ)] with N hG hN
  dsimp only [Function.comp_apply] at hG
  intro a ha haN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hquarter : 1 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  have hsplit : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 12 : ℝ) =
      (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hgap : (N : ℝ) ^ (1 / 4 : ℝ) + 1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg hN0.le (1 / 4 : ℝ))
    rw [hsplit] at h
    linarith
  have hprod : (N : ℝ) ^ (1 / 3 : ℝ) * (a : ℝ) ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left haN (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; norm_num
  have hfloor : (N : ℝ) < (N / a : ℕ) * (a : ℝ) + a := by
    exact_mod_cast (Nat.lt_div_mul_add (show 0 < a by omega) : N < N / a * a + a)
  have hlt : (N : ℝ) ^ (1 / 3 : ℝ) < (N / a : ℕ) + 1 := by
    nlinarith
  linarith

private theorem eventually_quotient_parameters (b : ℝ) (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℕ, 1 ≤ a →
      (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      M ≤ N / a ∧ 0 < Real.log (N : ℝ) ∧
      0 < Real.log (N / a : ℕ) ∧
      Real.log (N : ℝ) ≤ 4 * Real.log (N / a : ℕ) ∧
      (4 : ℝ) ^ b ≤ Real.log (N / a : ℕ) := by
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (M : ℝ))
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (4 * (4 : ℝ) ^ b))
  filter_upwards [eventually_nat_div_quarter, hp, hl, eventually_ge_atTop (2 : ℕ)]
    with N hQ hP hL hN
  dsimp only [Function.comp_apply] at hP hL
  intro a ha haN
  have hQ' := hQ a ha haN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hcomp := Real.log_le_log (Real.rpow_pos_of_pos hN0 (1 / 4 : ℝ)) hQ'
  rw [Real.log_rpow hN0] at hcomp
  have hlogt : 0 < Real.log (N / a : ℕ) := by linarith
  refine ⟨?_, hlogN, hlogt, ?_, ?_⟩
  · exact_mod_cast hP.trans hQ'
  · linarith
  · linarith

/-- The constants and cutoff are chosen before every `a`, modulus and character.
The endpoint is the literal natural quotient; the carrier is the real `N^(2/3)` range. -/
theorem primePrefix_siegelWalfisz_nat_div (b s : ℝ) (hb : 0 ≤ b) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ a : ℕ, 1 ≤ a → (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      ∀ χ : PrimitiveCharacter q, χ.1 ≠ 1 →
        ‖primePrefix χ.1 (N / a)‖ ≤
          (K * (N : ℝ) / Real.log (N : ℝ) ^ s) / (a : ℝ) := by
  obtain ⟨J, hJ, M, hSW⟩ := primePrefix_siegelWalfisz_endpoint (b + 1) s
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_quotient_parameters b M)
  refine ⟨J * (4 : ℝ) ^ s, by positivity, N₀, ?_⟩
  intro N hN a ha haN q hq hqb χ hχ
  obtain ⟨hM, hLN, hLt, hlogs, hpay⟩ := hN₀ N hN a ha haN
  have hconductor : Real.log (N : ℝ) ^ b ≤ Real.log (N / a : ℕ) ^ (b + 1) := by
    calc
      _ ≤ (4 * Real.log (N / a : ℕ)) ^ b := Real.rpow_le_rpow hLN.le hlogs hb
      _ = (4 : ℝ) ^ b * Real.log (N / a : ℕ) ^ b :=
        Real.mul_rpow (by norm_num) hLt.le
      _ ≤ Real.log (N / a : ℕ) * Real.log (N / a : ℕ) ^ b :=
        mul_le_mul_of_nonneg_right hpay (by positivity)
      _ = Real.log (N / a : ℕ) ^ (b + 1) := by
        rw [Real.rpow_add hLt, Real.rpow_one]; ring
  have hS := hSW (N / a) hM q hq (hqb.trans hconductor) χ hχ
  have hsaving : Real.log (N : ℝ) ^ s ≤
      (4 : ℝ) ^ s * Real.log (N / a : ℕ) ^ s := by
    calc
      _ ≤ (4 * Real.log (N / a : ℕ)) ^ s := Real.rpow_le_rpow hLN.le hlogs hs.le
      _ = _ := Real.mul_rpow (by norm_num) hLt.le
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hupper : (N / a : ℕ) * (a : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N a
  have hdenN := Real.rpow_pos_of_pos hLN s
  have hdent := Real.rpow_pos_of_pos hLt s
  refine hS.trans ?_
  apply (le_div_iff₀ ha0).2
  apply (le_div_iff₀ hdenN).2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hdent).2
  calc
    _ ≤ J * ((N / a : ℕ) * (a : ℝ)) *
        ((4 : ℝ) ^ s * Real.log (N / a : ℕ) ^ s) := by
      have h := mul_le_mul_of_nonneg_left hsaving
        (show 0 ≤ J * ((N / a : ℕ) * (a : ℝ)) by positivity)
      simpa only [mul_assoc] using h
    _ ≤ J * (N : ℝ) * ((4 : ℝ) ^ s * Real.log (N / a : ℕ) ^ s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hJ.le) (by positivity)
    _ = _ := by ring

end
end AnalyticNumberTheory.LargeSieve.PanLow