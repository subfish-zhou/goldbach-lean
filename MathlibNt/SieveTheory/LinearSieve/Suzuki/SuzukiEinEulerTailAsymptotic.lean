/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiStandardUpperAdjoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The classical Euler--Ein tail asymptotic

This module proves unconditionally that

`x * exp (-Ein x) -> exp (-γ)`

for the Suzuki `Ein` used in `SuzukiStandardUpperAdjoint`.
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

private noncomputable def einNatKernel (n : ℕ) : ℝ → ℝ :=
  Function.update (fun u : ℝ => (1 - Real.exp (-(n : ℝ) * u)) / u) 0 n

private noncomputable def harmonicKernel (n : ℕ) : ℝ → ℝ :=
  Function.update (fun u : ℝ => (1 - (1 - u) ^ n) / u) 0 n

private noncomputable def gapKernel (n : ℕ) : ℝ → ℝ :=
  fun u => harmonicKernel n u - einNatKernel n u

private theorem continuous_einNatKernel (n : ℕ) : Continuous (einNatKernel n) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · have hderiv :
        HasDerivAt (fun y : ℝ => 1 - Real.exp (-(n : ℝ) * y)) n 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id (0 : ℝ)).const_mul (-(n : ℝ))).exp).const_sub 1)
    simpa [einNatKernel] using hderiv.continuousAt_div
  · rw [einNatKernel, continuousAt_update_of_ne hu]
    fun_prop

private theorem continuous_harmonicKernel (n : ℕ) : Continuous (harmonicKernel n) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · have hderiv :
        HasDerivAt (fun y : ℝ => 1 - (1 - y) ^ n) n 0 := by
      simpa using ((((hasDerivAt_id (0 : ℝ)).const_sub 1).pow n).const_sub 1)
    simpa [harmonicKernel] using hderiv.continuousAt_div
  · rw [harmonicKernel, continuousAt_update_of_ne hu]
    fun_prop

private theorem continuous_gapKernel (n : ℕ) : Continuous (gapKernel n) :=
  (continuous_harmonicKernel n).sub (continuous_einNatKernel n)

private theorem suzukiEin_nat_eq_integral_einNatKernel (n : ℕ) :
    suzukiEin n = ∫ u in (0 : ℝ)..1, einNatKernel n u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [suzukiEin, einNatKernel]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    suzukiEin (n : ℝ) = (n : ℝ) * ∫ u in (0 : ℝ)..1, suzukiEinKernel (u * (n : ℝ)) := by
      simpa [suzukiEin] using
        (mul_integral_comp_mul_right (f := suzukiEinKernel) (a := (0 : ℝ)) (b := 1)
          (c := (n : ℝ))).symm
    _ = ∫ u in (0 : ℝ)..1, (n : ℝ) * suzukiEinKernel (u * (n : ℝ)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in (0 : ℝ)..1, einNatKernel n u := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro u hu
      have hu0 : u ≠ 0 := ne_of_gt hu.1
      have hun0 : u * (n : ℝ) ≠ 0 := mul_ne_zero hu0 hn0
      change (n : ℝ) * suzukiEinKernel (u * (n : ℝ)) = einNatKernel n u
      rw [suzukiEinKernel_of_ne hun0]
      simp [einNatKernel, hu0]
      field_simp [hu0, hn0]

private theorem integral_harmonicKernel (n : ℕ) :
    ∫ u in (0 : ℝ)..1, harmonicKernel n u = (harmonic n : ℝ) := by
  calc
    ∫ u in (0 : ℝ)..1, harmonicKernel n u
        = ∫ u in (0 : ℝ)..1, ∑ i ∈ Finset.range n, (1 - u) ^ i := by
            apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
            intro u hu
            have hu0 : u ≠ 0 := ne_of_gt hu.1
            have hneq : 1 - u ≠ (1 : ℝ) := by
              intro h
              apply hu0
              linarith
            simp [harmonicKernel, hu0]
            rw [geom_sum_eq hneq n]
            field_simp [hu0]
            ring
    _ = ∑ i ∈ Finset.range n, ∫ u in (0 : ℝ)..1, (1 - u) ^ i := by
          rw [intervalIntegral.integral_finsetSum]
          intro i hi
          exact ((continuous_const.sub continuous_id).pow i).intervalIntegrable 0 1
    _ = ∑ i ∈ Finset.range n, ((((i + 1 : ℕ) : ℝ)))⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          have hsub :
              ∫ u in (0 : ℝ)..1, (1 - u) ^ i = ∫ u in (0 : ℝ)..1, u ^ i := by
            simpa using
              (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ i)
                (a := (0 : ℝ)) (b := 1) (d := 1))
          rw [hsub]
          simpa [div_eq_mul_inv] using
            (intervalIntegral.integral_pow (a := (0 : ℝ)) (b := 1) (n := i))
    _ = (harmonic n : ℝ) := by
          simp [harmonic]

private theorem harmonic_sub_suzukiEin_eq_integral_gapKernel (n : ℕ) :
    (harmonic n : ℝ) - suzukiEin n = ∫ u in (0 : ℝ)..1, gapKernel n u := by
  have hh : IntervalIntegrable (harmonicKernel n) volume 0 1 :=
    (continuous_harmonicKernel n).intervalIntegrable 0 1
  have he : IntervalIntegrable (einNatKernel n) volume 0 1 :=
    (continuous_einNatKernel n).intervalIntegrable 0 1
  calc
    (harmonic n : ℝ) - suzukiEin n
        = (∫ u in (0 : ℝ)..1, harmonicKernel n u) -
            (∫ u in (0 : ℝ)..1, einNatKernel n u) := by
              rw [integral_harmonicKernel n, suzukiEin_nat_eq_integral_einNatKernel n]
    _ = ∫ u in (0 : ℝ)..1, gapKernel n u := by
          rw [← intervalIntegral.integral_sub hh he]
          rfl

private theorem harmonicKernel_eq_quotient {n : ℕ} {u : ℝ} (hu : u ≠ 0) :
    harmonicKernel n u = (1 - (1 - u) ^ n) / u := by
  simp [harmonicKernel, hu]

private theorem einNatKernel_eq_quotient {n : ℕ} {u : ℝ} (hu : u ≠ 0) :
    einNatKernel n u = (1 - Real.exp (-(n : ℝ) * u)) / u := by
  simp [einNatKernel, hu]

private theorem gapKernel_eq_quotient {n : ℕ} {u : ℝ} (hu : u ≠ 0) :
    gapKernel n u = (Real.exp (-(n : ℝ) * u) - (1 - u) ^ n) / u := by
  rw [gapKernel, harmonicKernel_eq_quotient hu, einNatKernel_eq_quotient hu]
  ring

private theorem gapKernel_nonneg {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ gapKernel n u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [gapKernel, harmonicKernel, einNatKernel, hn]
  have hu_pos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn_pos)
  have hpow :=
    Real.one_sub_div_pow_le_exp_neg (n := n) (t := (n : ℝ) * u)
      (by nlinarith [hu.2])
  have hmain : (1 - u) ^ n ≤ Real.exp (-(n : ℝ) * u) := by
    convert hpow using 1
    field_simp [hn0]
    ring
  rw [gapKernel_eq_quotient hu0]
  exact div_nonneg (sub_nonneg.mpr hmain) hu.1

private theorem gapKernel_le_aux {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    gapKernel n u ≤ (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u) := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [gapKernel, harmonicKernel, einNatKernel, hn]
  have hu_pos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hy_nonneg : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hxy : 1 - u ≤ Real.exp (-u) := by
    simpa using Real.one_sub_le_exp_neg u
  have hxy_nonneg : 0 ≤ Real.exp (-u) - (1 - u) := by linarith
  have hdiff_sq : Real.exp (-u) - (1 - u) ≤ u ^ 2 := by
    have h :=
      Real.abs_exp_sub_one_sub_id_le (x := -u) (by simpa [abs_of_nonneg hu.1] using hu.2)
    have hnonneg : 0 ≤ Real.exp (-u) - 1 - (-u) := by
      linarith [Real.one_sub_le_exp_neg u]
    rw [abs_of_nonneg hnonneg] at h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, pow_two] using h
  let x : ℝ := Real.exp (-u)
  let y : ℝ := 1 - u
  let S : ℝ := ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)
  have hfactor : x ^ n - y ^ n = (x - y) * S := by
    dsimp [S]
    simpa [x, y, mul_comm] using (geom_sum₂_mul x y n).symm
  have hratio_nonneg : 0 ≤ (x - y) / u := by
    exact div_nonneg (by simpa [x, y] using hxy_nonneg) hu.1
  have hratio_le : (x - y) / u ≤ u := by
    rw [div_le_iff₀ hu_pos]
    simpa [x, y, pow_two] using hdiff_sq
  have hS_nonneg : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · exact pow_nonneg (by positivity : 0 ≤ x) _
    · exact pow_nonneg (by simpa [y] using hy_nonneg) _
  have hS_le : S ≤ (n : ℝ) * x ^ (n - 1) := by
    calc
      S ≤ ∑ i ∈ Finset.range n, x ^ i * x ^ (n - 1 - i) := by
            apply Finset.sum_le_sum
            intro i hi
            have hyxpow : y ^ (n - 1 - i) ≤ x ^ (n - 1 - i) := by
              exact pow_le_pow_left₀ (by simpa [y] using hy_nonneg)
                (by simpa [x, y] using hxy) _
            exact mul_le_mul_of_nonneg_left hyxpow (pow_nonneg (by positivity : 0 ≤ x) _)
      _ = (n : ℝ) * x ^ (n - 1) := by
            simpa [S, x, mul_comm, mul_left_comm, mul_assoc] using (geom_sum₂_self x n)
  have hxpow : x ^ n = Real.exp (-(n : ℝ) * u) := by
    simp [x, ← Real.exp_nat_mul, mul_comm, mul_assoc]
  rw [gapKernel_eq_quotient hu0, ← hxpow]
  change (x ^ n - y ^ n) / u ≤
    (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u)
  have hquot :
      (x ^ n - y ^ n) / u = ((x - y) / u) * S := by
    rw [hfactor]
    field_simp [hu0]
  rw [hquot]
  calc
    ((x - y) / u) * S ≤ u * S := by
      exact mul_le_mul_of_nonneg_right hratio_le hS_nonneg
    _ ≤ u * ((n : ℝ) * x ^ (n - 1)) := by
      exact mul_le_mul_of_nonneg_left hS_le hu.1
    _ = (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u) := by
      simp [x, ← Real.exp_nat_mul, mul_comm, mul_left_comm, mul_assoc]

private theorem harmonic_sub_suzukiEin_nonneg (n : ℕ) :
    0 ≤ (harmonic n : ℝ) - suzukiEin n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [suzukiEin]
  rw [harmonic_sub_suzukiEin_eq_integral_gapKernel n]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro u hu
  exact gapKernel_nonneg hn hu

private theorem harmonic_sub_suzukiEin_le (n : ℕ) (hn : 2 ≤ n) :
    (harmonic n : ℝ) - suzukiEin n ≤ (n : ℝ) / (n - 1 : ℝ) ^ 2 := by
  rw [harmonic_sub_suzukiEin_eq_integral_gapKernel n]
  have hupperInt :
      IntervalIntegrable (fun u : ℝ => (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u))
        volume 0 1 := by
    have hcont : Continuous (fun u : ℝ => (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u)) := by
      have hlin : Continuous (fun u : ℝ => -((n - 1 : ℕ) : ℝ) * u) :=
        continuous_const.mul continuous_id
      exact (continuous_const.mul continuous_id).mul
        (Real.continuous_exp.comp hlin)
    exact hcont.intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (f := gapKernel n)
    (g := fun u : ℝ => (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u))
    zero_le_one
    ((continuous_gapKernel n).intervalIntegrable 0 1)
    hupperInt
    (fun u hu => gapKernel_le_aux (Nat.one_le_of_lt hn) hu)
  refine hmono.trans ?_
  have hpos_nat : 0 < n - 1 := Nat.sub_pos_of_lt hn
  have hpos : 0 < (((n - 1 : ℕ) : ℝ)) := by exact_mod_cast hpos_nat
  have h_int :
      ∫ u in (0 : ℝ)..1, (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u)
        ≤ ∫ u : ℝ in Ioi 0, (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact MeasureTheory.integral_mono_measure (volume.restrict_mono_set Ioc_subset_Ioi_self)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        exact mul_nonneg (mul_nonneg hn_nonneg hu.le) (by positivity))
      (by
        have hbase : IntegrableOn
            (fun x : ℝ => x * Real.exp (-((((n - 1 : ℕ) : ℝ)) * x))) (Ioi 0) := by
          simpa [one_mul, Real.rpow_one, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            mul_assoc, mul_left_comm, mul_comm] using
            (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
              (b := (((n - 1 : ℕ) : ℝ))) (by norm_num) le_rfl hpos)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbase.const_mul (n : ℝ))
  refine h_int.trans ?_
  have h_eq :
      ∫ u : ℝ in Ioi 0, (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u)
        = (n : ℝ) * ∫ u : ℝ in Ioi 0, u ^ ((2 : ℝ) - 1) * Real.exp (-((n - 1 : ℕ) : ℝ) * u) := by
    have hfun :
        (fun u : ℝ => (n : ℝ) * u * Real.exp (-((n - 1 : ℕ) : ℝ) * u)) =
          fun u : ℝ => (n : ℝ) * (u * Real.exp (-((n - 1 : ℕ) : ℝ) * u)) := by
      funext u
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    norm_num
  rw [h_eq]
  have hgamma :
      ∫ u : ℝ in Ioi 0, u ^ ((2 : ℝ) - 1) * Real.exp (-((n - 1 : ℕ) : ℝ) * u) =
        (1 / (((n - 1 : ℕ) : ℝ))) ^ (2 : ℝ) * Real.Gamma 2 :=
    by
      simpa using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := (((n - 1 : ℕ) : ℝ)))
          (by positivity) hpos)
  have hgamma' :
      (n : ℝ) * ∫ u : ℝ in Ioi 0, u ^ ((2 : ℝ) - 1) * Real.exp (-((n - 1 : ℕ) : ℝ) * u) =
        (n : ℝ) * ((1 / (((n - 1 : ℕ) : ℝ))) ^ (2 : ℝ) * Real.Gamma 2) := by
    exact congrArg (fun z : ℝ => (n : ℝ) * z) hgamma
  rw [hgamma']
  have hpow : (1 / (((n - 1 : ℕ) : ℝ))) ^ (2 : ℝ) = 1 / (((n - 1 : ℕ) : ℝ)) ^ 2 := by
    have hne : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    field_simp [hne]
  have hG : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  rw [hpow, hG]
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]
    ring
  have hfinal : (n : ℝ) * (1 / (((n - 1 : ℕ) : ℝ)) ^ 2 * 1) = (n : ℝ) / ((n : ℝ) - 1) ^ 2 := by
    rw [hcast]
    ring
  simpa [Nat.cast_sub hn1] using hfinal.le

private theorem tendsto_harmonic_sub_suzukiEin : Tendsto
    (fun n : ℕ => (harmonic n : ℝ) - suzukiEin n) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact harmonic_sub_suzukiEin_nonneg n
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hle := harmonic_sub_suzukiEin_le n (by exact_mod_cast hn)
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hle' : (harmonic n : ℝ) - suzukiEin n ≤ (n : ℝ) / (((n : ℝ) - 1) ^ 2) := by
      simpa [Nat.cast_sub hn.le] using hle
    have hbound : (n : ℝ) / (((n : ℝ) - 1) ^ 2) ≤ (4 : ℝ) / n := by
      have hgt1 : (1 : ℝ) < n := by exact_mod_cast hn
      have hpos1 : 0 < (n : ℝ) - 1 := by linarith
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnreal
      have hsub0 : (n : ℝ) - 1 ≠ 0 := by linarith
      have hineq : (n : ℝ) ^ 2 ≤ 4 * (((n : ℝ) - 1) ^ 2) := by
        have hge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have hfac : 0 ≤ ((n : ℝ) - 2) * (3 * (n : ℝ) - 2) := by
          apply mul_nonneg
          · linarith
          · linarith
        nlinarith
      calc
        (n : ℝ) / (((n : ℝ) - 1) ^ 2)
            = (n : ℝ) ^ 2 / ((n : ℝ) * (((n : ℝ) - 1) ^ 2)) := by
                field_simp [hn0]
        _ ≤ (4 * (((n : ℝ) - 1) ^ 2)) / ((n : ℝ) * (((n : ℝ) - 1) ^ 2)) := by
              gcongr
        _ = (4 : ℝ) / n := by
              field_simp [hn0, hsub0]
    calc
      (harmonic n : ℝ) - suzukiEin n ≤ (n : ℝ) / (((n : ℝ) - 1) ^ 2) := hle'
      _ ≤ (4 : ℝ) / n := hbound
  · simpa [div_eq_mul_inv] using
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (4 : ℝ))

private theorem tendsto_suzukiEin_sub_log_nat :
    Tendsto (fun n : ℕ => suzukiEin n - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  have hharm : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hgap : Tendsto (fun n : ℕ => -((harmonic n : ℝ) - suzukiEin n)) atTop (𝓝 0) :=
    by simpa using tendsto_harmonic_sub_suzukiEin.neg
  have hadd : Tendsto
      (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) + -((harmonic n : ℝ) - suzukiEin n))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa using hharm.add hgap
  refine hadd.congr' ?_
  filter_upwards with n
  ring

private theorem tendsto_suzukiEin_sub_log :
    Tendsto (fun x : ℝ => suzukiEin x - Real.log x) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  let g : ℝ → ℝ := suzukiEin - Real.log
  have hinterior : interior (Ici (1 : ℝ)) = Ioi 1 := interior_Ici
  have hg_cont : ContinuousOn g (Ici 1) := by
    exact continuous_suzukiEin.continuousOn.sub
      (Real.continuousOn_log.mono fun x hx => (zero_lt_one.trans_le hx).ne')
  have hg_diff : DifferentiableOn ℝ g (interior (Ici (1 : ℝ))) := by
    intro x hx
    rw [hinterior] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
    exact ((hasDerivAt_suzukiEin (x := x)).sub
      (Real.hasDerivAt_log hx0)).differentiableAt.differentiableWithinAt
  have hg_deriv_nonpos : ∀ x ∈ interior (Ici (1 : ℝ)), deriv g x ≤ 0 := by
    intro x hx
    rw [hinterior] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
    have hxpos : 0 < x := zero_lt_one.trans hx
    have hderiv := (hasDerivAt_suzukiEin (x := x)).sub (Real.hasDerivAt_log hx0)
    have hvalue : suzukiEinKernel x - x⁻¹ = -(Real.exp (-x) / x) := by
      rw [suzukiEinKernel_of_ne hx0]
      field_simp [hx0]
      ring
    have hderiv' : HasDerivAt g (suzukiEinKernel x - x⁻¹) x := by
      simpa [g] using hderiv
    have hderiv_eq : deriv g x = suzukiEinKernel x - x⁻¹ := hderiv'.deriv
    rw [hderiv_eq, hvalue]
    exact neg_nonpos.mpr (div_nonneg (by positivity) hxpos.le)
  have hg_anti : AntitoneOn g (Ici 1) :=
    antitoneOn_of_deriv_nonpos (convex_Ici (1 : ℝ)) hg_cont hg_diff hg_deriv_nonpos
  have hupper : Tendsto (fun x : ℝ => g (⌊x⌋₊ : ℝ)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine (tendsto_suzukiEin_sub_log_nat.comp tendsto_nat_floor_atTop).congr' ?_
    filter_upwards with x
    simp [g]
  have hlower : Tendsto (fun x : ℝ => g ((⌊x⌋₊ : ℝ) + 1)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    have hshift : Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
    refine (tendsto_suzukiEin_sub_log_nat.comp hshift).congr' ?_
    filter_upwards with x
    simp [g, Nat.cast_add]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun x : ℝ => g x)
    (g := fun x : ℝ => g ((⌊x⌋₊ : ℝ) + 1))
    (h := fun x : ℝ => g (⌊x⌋₊ : ℝ))
    hlower hupper ?_ ?_
  · filter_upwards [Ioi_mem_atTop (1 : ℝ)] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx_mem : x ∈ Ici (1 : ℝ) := by exact hx1.le
    have hceil_mem : ((⌊x⌋₊ : ℝ) + 1) ∈ Ici (1 : ℝ) := by
      show (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1
      have hfloor_nonneg : 0 ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (Nat.zero_le ⌊x⌋₊)
      linarith
    have hx_le : x ≤ (⌊x⌋₊ : ℝ) + 1 := by
      exact (Nat.lt_floor_add_one x).le
    exact hg_anti hx_mem hceil_mem hx_le
  · filter_upwards [Ioi_mem_atTop (1 : ℝ)] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hfloor_mem : (⌊x⌋₊ : ℝ) ∈ Ici (1 : ℝ) := by
      show (1 : ℝ) ≤ (⌊x⌋₊ : ℝ)
      exact_mod_cast (Nat.one_le_floor_iff x).2 hx1.le
    have hx_mem : x ∈ Ici (1 : ℝ) := by exact hx1.le
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (show 0 ≤ x by linarith)
    exact hg_anti hfloor_mem hx_mem hfloor_le

/-- The classical Euler--Ein tail asymptotic needed to normalize Suzuki's
standard upper adjoint. -/
theorem suzukiEinEulerTailAsymptotic_proof : SuzukiEinEulerTailAsymptotic := by
  let g : ℝ → ℝ := suzukiEin - Real.log
  have hg : Tendsto g atTop (𝓝 Real.eulerMascheroniConstant) := tendsto_suzukiEin_sub_log
  have hexp : Tendsto (fun x : ℝ => Real.exp (-g x)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hg.neg
  refine hexp.congr' ?_
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
  simp [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    Real.exp (Real.log x + -suzukiEin x)
        = Real.exp (Real.log x) * Real.exp (-suzukiEin x) := by rw [Real.exp_add]
    _ = x * Real.exp (-suzukiEin x) := by simp [Real.exp_log hx]

/-- The genuine Laplace adjoint has the required value at `1`, with the
Euler--Ein tail discharged internally rather than supplied as a premise. -/
theorem suzukiStandardUpperAdjoint_one_eq_exp_neg_eulerMascheroni_unconditional :
    suzukiStandardUpperAdjoint 1 =
      Real.exp (-Real.eulerMascheroniConstant) :=
  suzukiStandardUpperAdjoint_one_eq_exp_neg_eulerMascheroni
    suzukiEinEulerTailAsymptotic_proof


end

end MathlibNt.SieveTheory
