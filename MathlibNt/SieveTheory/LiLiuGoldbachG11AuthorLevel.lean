import MathlibNt.SieveTheory.LiLiuGoldbachG11MixedAnalyticMain
import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernel

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Reciprocal-level stability with a fixed explicit loss, uniformly in the
short-prime coordinate. -/
theorem goldbachG11_reciprocal_level_loss {b δ : ℝ}
    (hb : 1/2 ≤ b) (hδ : 0 ≤ δ) (hδu : δ < 1/4) :
    4/(b-δ) ≤ 4/b+32*δ := by
  have hb0 : 0 < b := by linarith
  have hbd : 0 < b-δ := by linarith
  have hprod : (1/8 : ℝ) ≤ b*(b-δ) := by
    have hh := mul_le_mul hb (by linarith : (1/4 : ℝ) ≤ b-δ) (by norm_num) hb0.le
    norm_num at hh
    exact hh
  have he : 4*δ/(b*(b-δ)) ≤ 32*δ := by
    calc
      _ ≤ 4*δ/(1/8 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hprod
      _ = _ := by ring
  calc
    _ = 4/b+4*δ/(b*(b-δ)) := by field_simp; ring
    _ ≤ _ := add_le_add (le_refl _) he

/-- The actual buffered low level and ordinary high level both dominate the
level encoded by the author's clamped weight at EVERY prime in the cell. -/
theorem goldbachG11MixedLevel_log_lower {N : ℕ} {ε ρ δ : ℝ}
    (hN : 4 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ)) {k : ℕ × ℕ}
    (hk : k ∈ goldbachG11GridUsed N ε ρ) {p : ℕ} (hp : p ∈ goldbachG11GridShort N ρ k) :
    ((5/9 : ℝ)*(1-min (Real.log (p : ℝ)/Real.log (N : ℝ)) (1/10))-δ)*Real.log (N : ℝ) ≤
      Real.log (goldbachG11MixedLevel N δ ρ k) := by
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hρ0 : 0 < ρ := by linarith
  have hpbound := ((goldbachG11GridShort_mem_iff hρ hρu hbig hk p).mp hp).1
  have hplo : ρ^k.1 ≤ (p : ℝ) := (le_max_left _ _).trans hpbound
  by_cases hl : ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ)
  · let T : ℝ := (2/3 : ℝ)*ρ^k.1
    have hT0 : 0 < T := mul_pos (by norm_num) (pow_pos hρ0 _)
    have hTcell : T ≤ ρ^k.1 := by dsimp [T]; nlinarith [pow_pos hρ0 k.1]
    have hTp := hTcell.trans hplo
    have hTN := hTcell.trans hl
    have hlogp := Real.log_le_log hT0 hTp
    have hlogt := Real.log_le_log hT0 hTN
    rw [Real.log_rpow hn] at hlogt
    have hh : Real.log T/Real.log (N : ℝ) ≤ min (Real.log (p : ℝ)/Real.log (N : ℝ)) (1/10) :=
      le_min (div_le_div_of_nonneg_right hlogp hlogN.le) ((div_le_iff₀ hlogN).2 (by linarith))
    have hc := (div_le_iff₀ hlogN).mp hh
    rw [goldbachG11MixedLevel,if_pos hl,goldbachG11GridLowLevel]
    change _ ≤ Real.log ((N : ℝ)^(5/9-δ)/T^(5/9 : ℝ))
    rw [Real.log_div (Real.rpow_pos_of_pos hn _).ne' (Real.rpow_pos_of_pos hT0 _).ne',
      Real.log_rpow hn,Real.log_rpow hT0]
    nlinarith only [hc]
  · have hNp : (N : ℝ)^(1/10 : ℝ) ≤ (p : ℝ) := (lt_of_not_ge hl).le.trans hplo
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hn (1/10)) hNp
    rw [Real.log_rpow hn] at hh
    have hr : (1/10 : ℝ) ≤ Real.log (p : ℝ)/Real.log (N : ℝ) :=
      (le_div_iff₀ hlogN).2 (by linarith)
    rw [min_eq_right hr,goldbachG11MixedLevel,if_neg hl,goldbachG11OrdinaryLevel,Real.log_rpow hn]
    nlinarith

/-- The author weight is derived from the literal two-route level, rather than
substituted for the old uniform coefficient 8. -/
theorem goldbachG11MixedLevel_author_weight {N : ℕ} {ε ρ δ : ℝ}
    (hN : 4 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ)) (hδ : 0 ≤ δ) (hδu : δ < 1/4)
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ)
    {p : ℕ} (hp : p ∈ goldbachG11GridShort N ρ k) :
    4*Real.log (N : ℝ)/Real.log (goldbachG11MixedLevel N δ ρ k) ≤
      goldbachG11AuthorWeight (Real.log (p : ℝ)/Real.log (N : ℝ))+32*δ := by
  let r := Real.log (p : ℝ)/Real.log (N : ℝ)
  let b : ℝ := (5/9 : ℝ)*(1-min r (1/10))
  have hb : (1/2 : ℝ) ≤ b := by dsimp [b]; have hh := min_le_right r (1/10 : ℝ); linarith
  have hbd : 0 < b-δ := by linarith
  have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlevel := goldbachG11MixedLevel_log_lower hN hρ hρu hbig hk hp (δ := δ)
  have heq : 4/b = goldbachG11AuthorWeight r := by
    unfold b goldbachG11AuthorWeight
    have hh := min_le_right r (1/10 : ℝ)
    have hn : 1-min r (1/10) ≠ 0 := by linarith
    field_simp
    ring
  calc
    _ ≤ 4*Real.log (N : ℝ)/((b-δ)*Real.log (N : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hbd hln) hlevel
    _ = 4/(b-δ) := by field_simp
    _ ≤ goldbachG11AuthorWeight r+32*δ := by rw [← heq]; exact goldbachG11_reciprocal_level_loss hb hδ hδu

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig