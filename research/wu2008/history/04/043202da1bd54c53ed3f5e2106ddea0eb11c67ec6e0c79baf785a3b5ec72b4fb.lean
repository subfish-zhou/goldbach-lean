import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralEndpoint

/-!
# Exact half-open prime windows and their continuous endpoint budget

The natural endpoints are `ceil Y - 1` and `ceil Z - 1`, including when
Y or Z is an integer prime. Both remaining continuous pieces have length
at most one. No prime endpoint is silently discarded.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory
open scoped Classical Topology Interval

theorem primeWindow_halfopen_sum_eq {Y Z : ℝ} {a b : ℕ}
    (haY : (a : ℝ) < Y) (hYa : Y ≤ (a + 1 : ℕ))
    (hbZ : (b : ℝ) < Z) (hZb : Z ≤ (b + 1 : ℕ)) (g : ℕ → ℝ) :
    (∑ p ∈ primeWindow 1 Y Z, g p) =
      ∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime), g (n + 1) := by
  symm
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    obtain ⟨hn, hprime⟩ := Finset.mem_filter.mp hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ico.mp hn
    refine mem_primeWindow.mpr ⟨hprime, Nat.coprime_one_right _, ?_, ?_⟩
    · exact hYa.trans (by exact_mod_cast (show a + 1 ≤ n + 1 by omega))
    · exact (by exact_mod_cast (show n + 1 ≤ b by omega) :
        ((n + 1 : ℕ) : ℝ) ≤ b).trans_lt hbZ
  · intro n _ m _ h
    omega
  · intro p hp
    obtain ⟨hpp, _, hYp, hpZ⟩ := mem_primeWindow.mp hp
    have hap : a < p := by exact_mod_cast haY.trans_le hYp
    have hpb : p < b + 1 := by exact_mod_cast hpZ.trans_le hZb
    refine ⟨p - 1, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using hpp
    · omega
  · intro _ _
    rfl

theorem primeWindow_ceil_halfopen_sum_eq {Y Z : ℝ}
    (hY : 0 < Y) (hZ : 0 < Z) (g : ℕ → ℝ) :
    (∑ p ∈ primeWindow 1 Y Z, g p) =
      ∑ n ∈ (Finset.Ico (⌈Y⌉₊ - 1) (⌈Z⌉₊ - 1)).filter (fun n => (n + 1).Prime),
        g (n + 1) := by
  have hCY : 0 < ⌈Y⌉₊ := Nat.ceil_pos.mpr hY
  have hCZ : 0 < ⌈Z⌉₊ := Nat.ceil_pos.mpr hZ
  have h1 := (Nat.ceil_eq_iff hCY.ne').mp (rfl : ⌈Y⌉₊ = ⌈Y⌉₊)
  have h2 := (Nat.ceil_eq_iff hCZ.ne').mp (rfl : ⌈Z⌉₊ = ⌈Z⌉₊)
  exact primeWindow_halfopen_sum_eq h1.1
    (by simpa only [Nat.sub_add_cancel hCY] using h1.2) h2.1
    (by simpa only [Nat.sub_add_cancel hCZ] using h2.2) g

theorem wuPrimeRealWeight_div_log_abs_le {f : ℝ → ℝ} {q B a Z x : ℝ}
    (hB : 0 ≤ B) (hfb : ∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B)
    (hq : 1 < q) (ha : 4 ≤ a) (hx : x ∈ Set.Icc a Z)
    (hZ : Z ≤ q ^ (1 / 2 : ℝ)) (haq : log q / log a - 1 ≤ 10) :
    |wuPrimeRealWeight f q x / log x| ≤ 4 * B / a / log a := by
  have hdom := wuPrime_continuous_argument_mem hq (by linarith : 1 < a) hx hZ haq
  have hker := reboxing_prime_weight_le_four_div hq (ha.trans hx.1) (hx.2.trans hZ)
  have hla : 0 < log a := log_pos (by linarith)
  have hlx : 0 < log x := log_pos (by linarith [hx.1])
  have hw : |wuPrimeRealWeight f q x| ≤ 4 * B / a := by
    unfold wuPrimeRealWeight
    rw [div_eq_mul_inv, abs_mul,
      abs_of_nonneg (show 0 ≤ ((x - 2) * (1 - log x / log q))⁻¹ by
        simpa only [one_div] using hker.1), ← one_div]
    calc
      _ ≤ B * (1 / ((x - 2) * (1 - log x / log q))) :=
        mul_le_mul_of_nonneg_right (hfb _ hdom) hker.1
      _ ≤ B * (4 / x) := mul_le_mul_of_nonneg_left hker.2 hB
      _ ≤ B * (4 / a) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) (by linarith) hx.1) hB
      _ = _ := by ring
  rw [abs_div, abs_of_pos hlx]
  exact (div_le_div_of_nonneg_right hw hlx.le).trans
    (div_le_div_of_nonneg_left (by positivity) hla (log_le_log (by linarith) hx.1))

/-- Uniform endpoint payment, including narrow windows whose two
ceilings coincide. Only monotonicity, not continuity, is used for f. -/
theorem primeCoefficient_continuous_endpoint_budget
    {f : ℝ → ℝ} {q B Y Z : ℝ} {a b : ℕ}
    (hf : MonotoneOn f (Set.Icc 1 10))
    (hB : 0 ≤ B) (hfb : ∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B)
    (ha : 4 ≤ a) (hab : a ≤ b) (hYZ : Y ≤ Z)
    (haY : (a : ℝ) ≤ Y) (hYa : Y ≤ (a : ℝ) + 1)
    (hbZ : (b : ℝ) ≤ Z) (hZb : Z ≤ (b : ℝ) + 1)
    (hq : 1 < q) (hZ : Z ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log (a : ℝ) - 1 ≤ 10) :
    |(∫ x in (a : ℝ)..b, wuPrimeRealWeight f q x / log x) -
      ∫ x in Y..Z, wuPrimeRealWeight f q x / log x| ≤
        8 * B / (a : ℝ) / log a := by
  have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hi := wuPrimeRealWeight_intervalIntegrable hf hq haR (haY.trans hYZ) hZ haq
  have hiab := hi.mono_set (show uIcc (a : ℝ) b ⊆ uIcc (a : ℝ) Z by
    rw [Set.uIcc_of_le habR, Set.uIcc_of_le (haY.trans hYZ)]
    exact Icc_subset_Icc le_rfl hbZ)
  have hiYZ := hi.mono_set (show uIcc Y Z ⊆ uIcc (a : ℝ) Z by
    rw [Set.uIcc_of_le hYZ, Set.uIcc_of_le (haY.trans hYZ)]
    exact Icc_subset_Icc haY le_rfl)
  have hiaY := hi.mono_set (show uIcc (a : ℝ) Y ⊆ uIcc (a : ℝ) Z by
    rw [Set.uIcc_of_le haY, Set.uIcc_of_le (haY.trans hYZ)]
    exact Icc_subset_Icc le_rfl hYZ)
  rw [intervalIntegral.integral_interval_sub_interval_comm hiab hiYZ hiaY]
  have hsmall {c d : ℝ} (hac : (a : ℝ) ≤ c) (hcd : c ≤ d)
      (hdZ : d ≤ Z) (hwidth : d - c ≤ 1) :
      |∫ x in c..d, wuPrimeRealWeight f q x / log x| ≤ 4 * B / (a : ℝ) / log a := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := d) (C := 4 * B / (a : ℝ) / log a)
      (f := fun x => wuPrimeRealWeight f q x / log x) (by
        intro x hx
        rw [Set.uIoc_of_le hcd] at hx
        simpa only [Real.norm_eq_abs] using wuPrimeRealWeight_div_log_abs_le hB hfb
          hq haR ⟨hac.trans hx.1.le, hx.2.trans hdZ⟩ hZ haq)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcd)] at h
    exact h.trans (mul_le_of_le_one_right (by positivity) hwidth)
  have hleft := hsmall le_rfl haY hYZ (by linarith)
  have hright := hsmall habR hbZ le_rfl (by linarith)
  calc
    _ ≤ |∫ x in (a : ℝ)..Y, wuPrimeRealWeight f q x / log x| +
        |∫ x in (b : ℝ)..Z, wuPrimeRealWeight f q x / log x| := abs_sub _ _
    _ ≤ 4 * B / (a : ℝ) / log a + 4 * B / (a : ℝ) / log a := add_le_add hleft hright
    _ = _ := by ring

/-- An all-prime half-open window is compared with its actual continuous
integral. The ceiling cutoff and both full-cell parameter conditions remain
explicit; the source-scale theorem must discharge them uniformly. -/
theorem primeCoefficient_halfopen_continuous :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, ∀ (f : ℝ → ℝ) (B q Y Z : ℝ),
      MonotoneOn f (Set.Icc 1 10) → 0 ≤ B →
      (∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B) →
      0 < Y → Y ≤ Z →
      X0 ≤ ⌈Y⌉₊ - 1 → 4 ≤ ⌈Y⌉₊ - 1 → 1 ≤ log (⌈Y⌉₊ - 1 : ℕ) →
      1 < q → 2 ≤ log q → Z ≤ q ^ (1 / 2 : ℝ) →
      log q / log (⌈Y⌉₊ - 1 : ℕ) - 1 ≤ 10 →
      |(∑ p ∈ primeWindow 1 Y Z, wuPrimeCoefficientWeight f q p) -
        ∫ x in Y..Z, wuPrimeRealWeight f q x / log x| ≤
          C * B / log (⌈Y⌉₊ - 1 : ℕ) := by
  obtain ⟨C, hC, X0, hmain⟩ := primeCoefficient_global_continuous
  refine ⟨C + 8, by linarith, X0, ?_⟩
  intro f B q Y Z hf hB hfb hY hYZ hXa ha hla hq hlq hZ haq
  let a := ⌈Y⌉₊ - 1
  let b := ⌈Z⌉₊ - 1
  have hZ0 := hY.trans_le hYZ
  have hCY : 0 < ⌈Y⌉₊ := Nat.ceil_pos.mpr hY
  have hCZ : 0 < ⌈Z⌉₊ := Nat.ceil_pos.mpr hZ0
  have h1 := (Nat.ceil_eq_iff hCY.ne').mp (rfl : ⌈Y⌉₊ = ⌈Y⌉₊)
  have h2 := (Nat.ceil_eq_iff hCZ.ne').mp (rfl : ⌈Z⌉₊ = ⌈Z⌉₊)
  have hab : a ≤ b := Nat.sub_le_sub_right (Nat.ceil_mono hYZ) 1
  have hYa : Y ≤ (a : ℝ) + 1 := by
    have h := h1.2
    rw [← Nat.sub_add_cancel hCY] at h
    push_cast at h
    exact h
  have hZb : Z ≤ (b : ℝ) + 1 := by
    have h := h2.2
    rw [← Nat.sub_add_cancel hCZ] at h
    push_cast at h
    exact h
  have hprim := hmain f B q hf hB hfb a b hXa ha hab hla hq hlq
    (h2.1.le.trans hZ) haq
  have hend := primeCoefficient_continuous_endpoint_budget hf hB hfb ha hab hYZ
    h1.1.le hYa h2.1.le hZb hq hZ haq
  rw [primeWindow_ceil_halfopen_sum_eq hY hZ0]
  have h := (abs_sub_le
    (∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime),
      wuPrimeCoefficientWeight f q (n + 1))
    (∫ x in (a : ℝ)..b, wuPrimeRealWeight f q x / log x)
    (∫ x in Y..Z, wuPrimeRealWeight f q x / log x)).trans (add_le_add hprim hend)
  apply h.trans
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hsmall := div_le_div_of_nonneg_right (div_le_self (show 0 ≤ 8 * B by positivity) ha1)
    (show 0 ≤ log (a : ℝ) by linarith)
  calc
    _ ≤ C * B / log (a : ℝ) + 8 * B / log (a : ℝ) := add_le_add le_rfl hsmall
    _ = _ := by ring

end Wu2008DoubleSieve
