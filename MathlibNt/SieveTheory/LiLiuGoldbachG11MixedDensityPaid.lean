import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridPrimePaid

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact complementary split: equality at the short-cell boundary is low. -/
theorem goldbachG11Grid_low_high_sum (N : ℕ) (ε ρ : ℝ) (f : (ℕ × ℕ) → ℝ) :
    (∑ k ∈ goldbachG11LowGridUsed N ε ρ,f k)+
      (∑ k ∈ goldbachG11HighGridUsed N ε ρ,f k) = ∑ k ∈ goldbachG11GridUsed N ε ρ,f k := by
  simp only [goldbachG11LowGridUsed,goldbachG11HighGridUsed,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  by_cases h : ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ) <;>
    simp only [h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,add_zero,zero_add]

def goldbachG11MixedDensityMain (N : ℕ) (ε ρ δ θ z : ℝ) : ℝ :=
  goldbachG11LowGridDensityMain N ε δ θ ρ (fun _ => fouvryG9SievePrimes N z) (fun _ => z)+
  goldbachG11OrdinaryDensityMain N ε ρ δ θ (goldbachG11HighGridUsed N ε ρ)
    (fun _ => fouvryG9SievePrimes N z) (fun _ => z)

/-- The original good G11 count, with both actual distribution routes and all
small-output/transport errors paid. Only the explicit arithmetic main term remains. -/
theorem goldbachG11GoodSwitchedTotal_le_mixedDensity (A : ℕ) {ε ρ δ θ : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hδ : 0 < δ) (hδu : δ < 1/2) (hθ : 0 < θ) (hθu : θ < 1/8) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ z : ℝ,
      0 ≤ z → z ≤ Real.sqrt (N : ℝ) →
      (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
        goldbachG11MixedDensityMain N ε ρ δ θ z+5*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨Ml,hl⟩ := goldbachG11LowGrid_prime_outputs_paid A hε hεu hδ hδu hθ hθu hρ hρu
  obtain ⟨Mh,hMh,hh⟩ := goldbachG11OrdinaryGrid_prime_outputs_paid A hδ hδu hθ hθu hρ hρu
  obtain ⟨Mg,_hMg,hg⟩ := goldbachG11OrdinaryLevel_gates hδ.le hδu hθ
  refine ⟨max Mh (max ⌈Ml⌉₊ Mg),hMh.trans (le_max_left _ _),?_⟩
  intro N hN z hz hzu
  obtain ⟨hNh,hrest⟩ := max_le_iff.mp hN
  obtain ⟨hNl,hNg⟩ := max_le_iff.mp hrest
  have hn4 : 4 ≤ N := hMh.trans hNh
  have hbig := (hg N hNg).1
  have hlow := hl N ((Nat.le_ceil Ml).trans (by exact_mod_cast hNl)) z hz hzu
  have hhigh := hh N hNh ε (goldbachG11HighGridUsed N ε ρ) (filter_subset _ _) z hz hzu
  have hcount := goldbachG11GoodSwitchedTotal_le_actual_grid (ε := ε) (by omega : 2 ≤ N) hρ hρu hbig
  rw [← goldbachG11Grid_low_high_sum] at hcount
  exact (hcount.trans (add_le_add hlow hhigh)).trans_eq (by unfold goldbachG11MixedDensityMain; ring)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig