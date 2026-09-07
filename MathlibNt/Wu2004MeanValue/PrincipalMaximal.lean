import MathlibNt.Wu2004MeanValue.RealEndpoints
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Uniform prime-counting error at coefficient-dependent real endpoints

This is the untwisted principal core, not the nonprincipal character estimate
in Wu (2004), Lemma 2.3. It consumes the frozen, proved Standard BV theorem
through its modulus-one term. All constants precede the moving endpoints.
Wu's integral normalization is used exactly, on the domain `[2, infinity)`.
-/

namespace Wu2004MeanValue

open Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanPrincipal

noncomputable section

def realPrimeCount (t : ℝ) : ℝ := primeCount ⌊t⌋₊

def principalError (t : ℝ) : ℝ := realPrimeCount t - wuLi t

theorem realPrimeCount_eq_scaled (t : ℝ) :
    realPrimeCount t = (scaledPrimeCount t 1 0 1 : ℝ) := by
  simp only [realPrimeCount, primeCount, scaledPrimeCount, scaledPrimeSet, Nat.cast_one,
    div_one, Nat.ModEq, Nat.mod_one, and_true]
  rw [Finset.sum_boole]

theorem principalError_le_prefix (N : ℕ) (t : ℝ)
    (ht : 2 ≤ t) (htN : t ≤ N) :
    |principalError t| ≤ standardPrimeAPPrefixMaxError N 1 + 3 / Real.log 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hfloor2 : (2 : ℝ) ≤ ⌊t⌋₊ := by
    exact_mod_cast (Nat.le_floor ht : 2 ≤ ⌊t⌋₊)
  have hfloorN : ⌊t⌋₊ ≤ N := by
    exact_mod_cast (Nat.floor_le ht0).trans htN
  have hprefix :
      |primeCount ⌊t⌋₊ - liuLogarithmicIntegral (2 / Real.log 2) ⌊t⌋₊| ≤
        standardPrimeAPPrefixMaxError N 1 := by
    rw [primeCount_sub_li_eq_standard, ← standardPrimeAPMaxError_one]
    unfold standardPrimeAPPrefixMaxError
    apply Finset.le_max'
    exact mem_image.mpr ⟨⌊t⌋₊, mem_range.mpr (by omega), rfl⟩
  have hshort := abs_li_sub_le_short (2 / Real.log 2) hfloor2
    (Nat.floor_le ht0) (Nat.lt_floor_add_one t).le
  have heq : principalError t =
      (primeCount ⌊t⌋₊ - liuLogarithmicIntegral (2 / Real.log 2) ⌊t⌋₊) +
        (liuLogarithmicIntegral (2 / Real.log 2) ⌊t⌋₊ -
          liuLogarithmicIntegral (2 / Real.log 2) t) + 2 / Real.log 2 := by
    rw [principalError, realPrimeCount, wuLi_sub_frozen]
    ring
  rw [heq]
  have htri := abs_add_le
    (primeCount ⌊t⌋₊ - liuLogarithmicIntegral (2 / Real.log 2) ⌊t⌋₊)
    (liuLogarithmicIntegral (2 / Real.log 2) ⌊t⌋₊ -
      liuLogarithmicIntegral (2 / Real.log 2) t)
  have htri' := abs_add_le
    ((primeCount ⌊t⌋₊ - liuLogarithmicIntegral (2 / Real.log 2) ⌊t⌋₊) +
      (liuLogarithmicIntegral (2 / Real.log 2) ⌊t⌋₊ -
        liuLogarithmicIntegral (2 / Real.log 2) t)) (2 / Real.log 2)
  rw [abs_sub_comm] at hshort
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.log 2)] at htri'
  linarith [show 3 / Real.log 2 = 1 / Real.log 2 + 2 / Real.log 2 by ring]

/-- A genuine maximal estimate over every real prime endpoint in `[2,N]`. -/
theorem principal_real_prefix_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ t : ℝ, 2 ≤ t → t ≤ N →
        |principalError t| ≤ C * N / Real.log N ^ A := by
  obtain ⟨B, _hB, C, hC, hBV⟩ := fourFactor_standardBombieriVinogradov A hA
  refine ⟨C + 3 / Real.log 2, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hBV, eventually_one_le_panModulusCutoff B,
    eventually_log_rpow_le_rpow A 1 (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with N hN hcut hpay hN2
  intro t ht htN
  rw [Real.rpow_one] at hpay
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hsingle : standardPrimeAPPrefixMaxError N 1 ≤
      C * N / Real.log N ^ A := by
    calc
      _ ≤ ∑ q ∈ Icc 1 (panModulusCutoff N B), standardPrimeAPPrefixMaxError N q :=
        single_le_sum (fun q _ => standardPrimeAPPrefixMaxError_nonneg N q)
          (mem_Icc.mpr ⟨le_rfl, hcut⟩)
      _ ≤ _ := hN hN2
  have hpay' : 3 / Real.log 2 ≤
      (3 / Real.log 2) * N / Real.log N ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog A)).mpr
    exact mul_le_mul_of_nonneg_left hpay (by positivity)
  calc
    _ ≤ standardPrimeAPPrefixMaxError N 1 + 3 / Real.log 2 :=
      principalError_le_prefix N t ht htN
    _ ≤ C * N / Real.log N ^ A +
        (3 / Real.log 2) * N / Real.log N ^ A := add_le_add hsingle hpay'
    _ = _ := by ring

/-- Coefficient-dependent endpoints, with the essential harmonic `1/m` gain. -/
theorem principal_moving_term_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Real.sqrt x →
      ∀ r : ℝ, 2 ≤ r → r ≤ x / m →
        |principalError r| ≤ (C * x / Real.log x ^ A) / m := by
  obtain ⟨K, hK, N₀, hbound⟩ := principal_real_prefix_bound A hA
  refine ⟨2 * K * (2 : ℝ) ^ A, by positivity, max 4 ((N₀ : ℝ) ^ 2), ?_⟩
  intro x hx m hm hmx r hr hrx
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsquare := Real.sq_sqrt hx0.le
  have hroot : Real.sqrt x ≤ x / m := by
    apply (le_div_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmx hsqrt.le]
  let T : ℕ := ⌈x / m⌉₊
  have hTlower : x / m ≤ (T : ℝ) := Nat.le_ceil _
  have hTroot : Real.sqrt x ≤ (T : ℝ) := hroot.trans hTlower
  have hNroot : (N₀ : ℝ) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by positivity) hx0.le).mpr
    exact (le_max_right _ _).trans hx
  have hTlarge : N₀ ≤ T := by exact_mod_cast hNroot.trans hTroot
  have hNlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogs : Real.log x ≤ 2 * Real.log (T : ℝ) := by
    have h := Real.log_le_log hsqrt hTroot
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hTlog : 0 < Real.log (T : ℝ) := by linarith
  have hroot2 : 2 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hx0.le).mpr
    norm_num
    exact hx4
  have hquot1 : 1 ≤ x / (m : ℝ) := by linarith
  have hTupper : (T : ℝ) ≤ 2 * x / m := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ x / (m : ℝ))
    change (T : ℝ) < x / (m : ℝ) + 1 at h
    calc
      _ ≤ 2 * (x / m) := by linarith
      _ = _ := by ring
  have hsaving : Real.log x ^ A ≤ (2 : ℝ) ^ A * Real.log (T : ℝ) ^ A := by
    calc
      _ ≤ (2 * Real.log (T : ℝ)) ^ A := Real.rpow_le_rpow hNlog.le hlogs hA.le
      _ = _ := Real.mul_rpow (by norm_num) hTlog.le
  have hmul : (T : ℝ) * m ≤ 2 * x := (le_div_iff₀ hm0).mp hTupper
  refine (hbound T hTlarge r hr (hrx.trans hTlower)).trans ?_
  apply (le_div_iff₀ hm0).mpr
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hNlog A)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hTlog A)).mpr
  calc
    _ ≤ K * ((T : ℝ) * m) * ((2 : ℝ) ^ A * Real.log (T : ℝ) ^ A) := by
      have h := mul_le_mul_of_nonneg_left hsaving
        (show 0 ≤ K * ((T : ℝ) * m) by positivity)
      simpa only [mul_assoc] using h
    _ ≤ K * (2 * x) * ((2 : ℝ) ^ A * Real.log (T : ℝ) ^ A) := by
      gcongr
    _ = _ := by ring

/-- The untwisted principal core for arbitrary bounded weights and moving
endpoints. `S` may include the modulus-dependent coprimality restriction. -/
theorem principal_moving_sum_bound (A F : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ (S : Finset ℕ) (f r : ℕ → ℝ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ r m ≤ x / m) →
        |∑ m ∈ S, f m * principalError (r m)| ≤ C * x / Real.log x ^ A := by
  obtain ⟨K, hK, x₀, hterm⟩ := principal_moving_term_bound (A + 1) (by linarith)
  refine ⟨2 * (F + 1) * K, by positivity, max x₀ (Real.exp 1), ?_⟩
  intro x hx S f r hS hf hr
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hexp : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hexp
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    simpa using h
  have hlog0 : 0 < Real.log x := by linarith
  have hsqrtx : Real.sqrt x ≤ x := by
    have hs := Real.sq_sqrt hx0.le
    have hn := Real.sqrt_nonneg x
    nlinarith
  have hsubset : S ⊆ Icc 1 ⌊x⌋₊ := by
    intro m hm
    exact mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor ((hS m hm).2.trans hsqrtx)⟩
  have hharm : ∑ m ∈ S, (m : ℝ)⁻¹ ≤ 2 * Real.log x := by
    calc
      _ ≤ ∑ m ∈ Icc 1 ⌊x⌋₊, (m : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
      _ = (harmonic ⌊x⌋₊ : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ 1 + Real.log x := harmonic_floor_le_one_add_log x hx1
      _ ≤ _ := by linarith
  calc
    _ ≤ ∑ m ∈ S, |f m * principalError (r m)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S, ((F + 1) * K * x / Real.log x ^ (A + 1)) * (m : ℝ)⁻¹ := by
      apply sum_le_sum
      intro m hm
      obtain ⟨hm1, hmx⟩ := hS m hm
      obtain ⟨hr2, hrx⟩ := hr m hm
      have ht := hterm x hxx₀ m hm1 hmx (r m) hr2 hrx
      rw [abs_mul]
      calc
        _ ≤ (F + 1) * ((K * x / Real.log x ^ (A + 1)) / m) :=
          mul_le_mul (by linarith [hf m hm]) ht (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = ((F + 1) * K * x / Real.log x ^ (A + 1)) *
        (∑ m ∈ S, (m : ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ ((F + 1) * K * x / Real.log x ^ (A + 1)) * (2 * Real.log x) :=
      mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlog0, Real.rpow_one]
      field_simp

/-- The endpoint ratio constant is fixed before the weight and endpoint
families, as required for the principal core of W3. -/
theorem principal_moving_sum_bound_ratio (A F K : ℝ) (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ (S : Finset ℕ) (f r : ℕ → ℝ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
        |∑ m ∈ S, f m * principalError (r m)| ≤ C * x / Real.log x ^ A := by
  obtain ⟨J, hJ, x₀, hbound⟩ := principal_moving_sum_bound A F hA hF
  let k : ℝ := max 1 K
  have hk1 : 1 ≤ k := le_max_left _ _
  have hKk : K ≤ k := le_max_right _ _
  have hk0 : 0 < k := by linarith
  refine ⟨J * k, by positivity, max 2 x₀, ?_⟩
  intro x hx S f r hS hf hr
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hxx₀ : x₀ ≤ x := (le_max_right _ _).trans hx
  have hxx : x ≤ k * x := by nlinarith
  have hS' : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt (k * x) := by
    intro m hm
    exact ⟨(hS m hm).1, (hS m hm).2.trans (Real.sqrt_le_sqrt hxx)⟩
  have hr' : ∀ m ∈ S, 2 ≤ r m ∧ r m ≤ k * x / m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (hS m hm).1
    refine ⟨(hr m hm).1, (le_div_iff₀ hm0).mpr ?_⟩
    have h := (hr m hm).2
    nlinarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogs : Real.log x ≤ Real.log (k * x) := Real.log_le_log hx0 hxx
  calc
    _ ≤ J * (k * x) / Real.log (k * x) ^ A :=
      hbound (k * x) (hxx₀.trans hxx) S f r hS' hf hr'
    _ ≤ J * (k * x) / Real.log x ^ A :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlog A)
        (Real.rpow_le_rpow hlog.le hlogs hA.le)
    _ = _ := by ring

end
end Wu2004MeanValue