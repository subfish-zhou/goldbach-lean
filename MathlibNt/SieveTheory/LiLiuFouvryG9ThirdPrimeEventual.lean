import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrectionActual
import MathlibNt.SieveTheory.LiLiuFouvryG9MainUpper

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Fixed positive product windows force a large third prime eventually.
The threshold depends on e; nonemptiness alone at finite N does not suffice. -/
theorem g9_third_prime_eventually_large {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ y ∈ fouvryG9Carrier N e,
      (N : ℝ)^(1/3 : ℝ) ≤ ((y.1/y.2.1 : ℕ) : ℝ) := by
  obtain ⟨Nc,hc⟩ := (eventually_atTop.1
    (g9Scale_eventually_const_mul_rpow_le (1/e) (14/15) 1 (by norm_num)))
  refine ⟨max 1 Nc,?_⟩
  intro N hN y hy
  have hN1 : (1 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpow := hc (N : ℝ) ((le_max_right _ _).trans hN)
  rw [Real.rpow_one] at hpow
  have hdiv : (N : ℝ)^(14/15 : ℝ)/e ≤ (N : ℝ) := by
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hpow
  have hpay : (N : ℝ)^(14/15 : ℝ) ≤ e*(N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ he).mp hdiv
  obtain ⟨hs,hn,hd,ht,hcop,hnl,hnu,hsl,hsq,hwin,hupper⟩ :=
    fouvryG9Carrier_geometry hy
  have hs2 : y.2.1^2 ≤ N :=
    (Nat.le_mul_of_pos_left _ hn.pos).trans hsq
  have hs2r : (y.2.1 : ℝ)^2 ≤ N := by exact_mod_cast hs2
  have hsroot : (y.2.1 : ℝ) ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hN0.le,Real.sqrt_nonneg (N : ℝ)]
  have hns : (y.2.2 : ℝ)*y.2.1 ≤ (N : ℝ)^(3/5 : ℝ) := by
    calc
      (y.2.2 : ℝ)*y.2.1 ≤ (N : ℝ)^(1/10 : ℝ)*Real.sqrt N :=
        mul_le_mul hnu.le hsroot (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
      _ = (N : ℝ)^(3/5 : ℝ) := by
        rw [Real.sqrt_eq_rpow,← Real.rpow_add hN0]
        congr 1; norm_num
  have heq : y.2.2*y.1 = y.2.2*y.2.1*(y.1/y.2.1) := by
    rw [Nat.mul_assoc,Nat.mul_div_cancel' hd]
  rw [heq] at hwin
  push_cast at hwin
  by_contra hthird
  have hthird' := (lt_of_not_ge hthird).le
  have hbound := mul_le_mul hns hthird' (Nat.cast_nonneg (y.1/y.2.1))
    (Real.rpow_nonneg hN0.le (3/5 : ℝ))
  have hp : (N : ℝ)^(3/5 : ℝ)*(N : ℝ)^(1/3 : ℝ) =
      (N : ℝ)^(14/15 : ℝ) := by
    rw [← Real.rpow_add hN0]
    congr 1; norm_num
  rw [hp] at hbound
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
