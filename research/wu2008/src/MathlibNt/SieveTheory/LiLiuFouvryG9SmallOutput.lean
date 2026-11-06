import MathlibNt.SieveTheory.LiLiuFouvryG9MotherSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantActual
import MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal weighted rectangle of outputs below the real cutoff, including zero. -/
def fouvryG9SmallOutputRectangle (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ fouvryG9LongProducts N ρ k,
    ∑ n ∈ fouvryG9RectanglePrimeSupport N ρ k,
      fouvryG9LongAlpha N ρ k m * fouvryG9RectangleBeta N n *
        (if ((((N : ℤ) - (m : ℤ)*n).natAbs : ℕ) : ℝ) < z then 1 else 0)

/-- Sum all small fibres; the range starts at zero and labels need not be injective. -/
theorem g9SmallOutput_fibre_sum {ι : Type*} (S : Finset ι) (a : ι → ℕ)
    (w : ι → ℝ) (z J : ℝ)
    (hf : ∀ r ∈ range ⌈z⌉₊, (∑ x ∈ S, if a x = r then w x else 0) ≤ J) :
    (∑ x ∈ S, w x * (if (a x : ℝ) < z then 1 else 0)) ≤ (⌈z⌉₊ : ℝ)*J := by
  classical
  have heq : ∀ x ∈ S, w x * (if (a x : ℝ) < z then 1 else 0) =
      ∑ r ∈ range ⌈z⌉₊, if a x = r then w x else 0 := by
    intro x _
    by_cases h : (a x : ℝ) < z
    · rw [if_pos h, mul_one]
      symm
      rw [sum_eq_single (a x)]
      · simp
      · intro r _ hr
        simp [Ne.symm hr]
      · intro hn
        exact False.elim (hn (mem_range.mpr (Nat.lt_ceil.mpr h)))
    · rw [if_neg h, mul_zero]
      symm
      apply sum_eq_zero
      intro r hr
      apply if_neg
      intro ha
      apply h
      rw [ha]
      exact Nat.lt_ceil.mp (mem_range.mp hr)
  calc
    _ = ∑ x ∈ S, ∑ r ∈ range ⌈z⌉₊, if a x = r then w x else 0 := sum_congr rfl heq
    _ = ∑ r ∈ range ⌈z⌉₊, ∑ x ∈ S, if a x = r then w x else 0 := sum_comm
    _ ≤ ∑ _r ∈ range ⌈z⌉₊, J := sum_le_sum hf
    _ = _ := by simp

/-- A single actual rectangle has the uniform three-quarter power bound. -/
theorem fouvryG9SmallOutputRectangle_bound {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hfib : ∀ (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (U V : Finset ℕ),
      ∀ r ≤ 4*N, (∑ p ∈ U ×ˢ V,
        if ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs = r then
          fouvryG9LongAlpha N ρ k p.1 * fouvryG9RectangleBeta N p.2 else 0)
            ≤ 2*C₀*(5*(N : ℝ))^(1/4 : ℝ))
    {N : ℕ} (hN : 1 ≤ (N : ℝ)) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
    {z : ℝ} (hz : 0 ≤ z) (hzu : z ≤ Real.sqrt (N : ℝ)) :
    fouvryG9SmallOutputRectangle N ρ k z ≤
      (4*C₀*(5 : ℝ)^(1/4 : ℝ))*(N : ℝ)^(1-(1/4 : ℝ)) := by
  have hN0 : 0 < (N : ℝ) := by linarith
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hN
  have hsN : Real.sqrt (N : ℝ) ≤ N := by
    rw [Real.sqrt_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hN (show (1/2 : ℝ) ≤ 1 by norm_num)
  have hceil : (⌈z⌉₊ : ℝ) ≤ 2*Real.sqrt (N : ℝ) := by
    linarith [Nat.ceil_lt_add_one hz]
  have hf := g9SmallOutput_fibre_sum
    ((fouvryG9LongProducts N ρ k) ×ˢ (fouvryG9RectanglePrimeSupport N ρ k))
    (fun p => ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs)
    (fun p => fouvryG9LongAlpha N ρ k p.1 * fouvryG9RectangleBeta N p.2)
    z (2*C₀*(5*(N : ℝ))^(1/4 : ℝ)) (by
      intro r hr
      apply hfib
      have hrz : (r : ℝ) < z := Nat.lt_ceil.mp (mem_range.mp hr)
      have hrN : (r : ℝ) ≤ 4*(N : ℝ) := by linarith
      exact_mod_cast hrN)
  rw [sum_product] at hf
  change fouvryG9SmallOutputRectangle N ρ k z ≤ _ at hf
  calc
    _ ≤ (⌈z⌉₊ : ℝ)*(2*C₀*(5*(N : ℝ))^(1/4 : ℝ)) := hf
    _ ≤ (2*Real.sqrt (N : ℝ))*(2*C₀*(5*(N : ℝ))^(1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hceil (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hN0.le]
      calc
        _ = (4*C₀*(5 : ℝ)^(1/4 : ℝ))*((N : ℝ)^(1/2 : ℝ)*(N : ℝ)^(1/4 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
