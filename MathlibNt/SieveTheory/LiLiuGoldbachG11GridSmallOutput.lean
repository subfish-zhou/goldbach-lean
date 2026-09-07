import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleFibres
import MathlibNt.SieveTheory.LiLiuGoldbachG11GridSubpowerBudget
import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutput

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Original G11 weighted small outputs, including zero, have a fixed subpower
bound on every finite rectangle. No label-injectivity or rectangle-volume premise. -/
theorem goldbachG11RectangleSmallMass_subpower :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ (N : ℝ) → ∀ U V : Finset ℕ,
      ∀ z : ℝ, 0 ≤ z → z ≤ Real.sqrt (N : ℝ) →
      goldbachG11RectangleSmallMass N U V z ≤ C*(N : ℝ)^(1-(1/4 : ℝ)) := by
  obtain ⟨C₀,hC₀,hfib⟩ := goldbachG11Rectangle_fibres_subpower (by norm_num : (0 : ℝ) < 1/4)
  refine ⟨1600*C₀*(5 : ℝ)^(1/4 : ℝ),by positivity,?_⟩
  intro N hN U V z hz hzu
  have hn : (0 : ℝ) < N := by linarith
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by simpa using Real.sqrt_le_sqrt hN
  have hsN : Real.sqrt (N : ℝ) ≤ N := by
    rw [Real.sqrt_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hN (show (1/2 : ℝ) ≤ 1 by norm_num)
  have hceil : (⌈z⌉₊ : ℝ) ≤ 2*Real.sqrt (N : ℝ) := by linarith [Nat.ceil_lt_add_one hz]
  have hf := g9SmallOutput_fibre_sum (U ×ˢ V)
    (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs)
    (goldbachG11RectangleWeight N) z (800*C₀*(5*(N : ℝ))^(1/4 : ℝ)) (by
      intro r hr
      apply hfib
      have hrz : (r : ℝ) < z := Nat.lt_ceil.mp (mem_range.mp hr)
      have hrN : (r : ℝ) ≤ 4*(N : ℝ) := by linarith
      exact_mod_cast hrN)
  calc
    _ ≤ (⌈z⌉₊ : ℝ)*(800*C₀*(5*(N : ℝ))^(1/4 : ℝ)) := hf
    _ ≤ (2*Real.sqrt (N : ℝ))*(800*C₀*(5*(N : ℝ))^(1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hceil (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hn.le]
      calc
        _ = (1600*C₀*(5 : ℝ)^(1/4 : ℝ))*((N : ℝ)^(1/2 : ℝ)*(N : ℝ)^(1/4 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hn]; norm_num

/-- The entire actual G11 grid pays small outputs. The threshold precedes
all epsilon values and all changing per-cell square-root-window cutoffs. -/
theorem goldbachG11Grid_small_outputs_paid (A : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ (ε : ℝ) (z : (ℕ × ℕ) → ℝ),
      (∀ k ∈ goldbachG11GridUsed N ε ρ, 0 ≤ z k ∧ z k ≤ Real.sqrt (N : ℝ)) →
      (∑ k ∈ goldbachG11GridUsed N ε ρ,
        goldbachG11RectangleSmallMass N (goldbachG11GridLong N ε ρ k)
          (goldbachG11GridShort N ρ k) (z k)) ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,hC,hsmall⟩ := goldbachG11RectangleSmallMass_subpower
  obtain ⟨M,hM⟩ := goldbachG11Grid_subpower_sum A hC.le
    (by norm_num : (0 : ℝ) < 1/4) hρ
  refine ⟨M,?_⟩
  intro N hN ε z hz
  obtain ⟨hn,hl,hpay⟩ := hM N hN
  apply hpay ε
  intro k hk
  have hs := hsmall N hn (goldbachG11GridLong N ε ρ k)
    (goldbachG11GridShort N ρ k) (z k) (hz k hk).1 (hz k hk).2
  have hf : 0 ≤ C*(N : ℝ)^(1-(1/4 : ℝ)) := by positivity
  exact hs.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (one_le_pow₀ hl : (1 : ℝ) ≤ Real.log (N : ℝ)^2) hf)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig