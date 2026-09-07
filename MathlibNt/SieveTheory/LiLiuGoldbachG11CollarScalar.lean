import MathlibNt.SieveTheory.LiLiuGoldbachG11GridDisjointEnvelope
import MathlibNt.SieveTheory.PrimeReciprocalLogScale

open Finset Filter
open scoped BigOperators Topology Classical
open MathlibNt.SieveTheory.PrimeReciprocalLogScale
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The strict lower integer endpoint avoids an artificial +1 loss in the
ordering collar. Dropping primality here is an upper bound, not an identity. -/
theorem goldbachG11_integer_collar_reciprocal {q : ℕ} {ρ : ℝ} (hq : 0 < q) (hρ : 1 ≤ ρ) :
    (∑ p ∈ Ioc q ⌊ρ*(q : ℝ)⌋₊,1/(p : ℝ)) ≤ ρ-1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hρ0 : 0 ≤ ρ := by linarith
  have hlow : (q : ℝ) ≤ ρ*q := by nlinarith
  have hfloor : q ≤ ⌊ρ*(q : ℝ)⌋₊ := (Nat.le_floor_iff (by positivity)).2 hlow
  have hcard : ((Ioc q ⌊ρ*(q : ℝ)⌋₊).card : ℝ) ≤ (ρ-1)*q := by
    simp only [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hh := Nat.floor_le (mul_nonneg hρ0 hqR.le)
    nlinarith
  calc
    _ ≤ ∑ _p ∈ Ioc q ⌊ρ*(q : ℝ)⌋₊,1/(q : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hqR (by exact_mod_cast (mem_Ioc.mp hp).1.le)
    _ = ((Ioc q ⌊ρ*(q : ℝ)⌋₊).card : ℝ)*(1/(q : ℝ)) := by simp
    _ ≤ ((ρ-1)*q)*(1/(q : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

/-- Reuse Mertens' fixed logarithmic-window limit. The slightly wider lower
exponent includes the original closed endpoint without changing the main term. -/
theorem goldbachG11_prime_reciprocal_bounded :
    ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    (∑ p ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)),1/(p : ℝ)) ≤ B := by
  let L : ℝ := Real.log ((4/33 : ℝ)/(2/53))
  let B : ℝ := |L|+1
  have hB : 0 < B := by dsimp [B]; positivity
  have ht := tendsto_primeReciprocalLogInterval (by norm_num : (0 : ℝ) < 2/53)
    (by norm_num : (2/53 : ℝ) < 4/33)
  have hLB : L < B := by have hh := le_abs_self L; dsimp [B]; linarith
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hLB))
  refine ⟨B,hB,max 4 M,le_max_left _ _,?_⟩
  intro N hN
  obtain ⟨hn4,hNm⟩ := max_le_iff.mp hN
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpow : (N : ℝ)^(2/53 : ℝ) < (N : ℝ)^(4/53 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hn1 (by norm_num)
  apply le_trans _ (hM N hNm).le
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpP,_hpN,hpl,hpu⟩ := mem_goldbachClosedPrimes_iff.mp hp
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_,hpP,hpow.trans_le hpl,hpu⟩
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)).2 hpu)
  · intro p _ _
    positivity

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig