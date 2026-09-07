import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutput

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A prime output at or above the cutoff survives the literal sieve carrier.
No coprimality of the output with N is needed. -/
theorem fouvryG9PrimeOutput_coprime {N r : ℕ} {z : ℝ}
    (hr : r.Prime) (hz : z ≤ (r : ℝ)) :
    r.Coprime ((fouvryG9SievePrimes N z).prod id) := by
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  obtain ⟨hpp,_,hpz⟩ := (fouvryG9SievePrimes_mem N p z).mp hp
  change r.Coprime p
  rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
  intro hd
  have he : r = p := (hr.dvd_iff_eq hpp.ne_one).mp hd
  subst r
  linarith

/-- The exact pointwise split retains small prime outputs as an explicit cost. -/
theorem fouvryG9PrimeOutput_indicator (N r : ℕ) (z : ℝ) :
    (if r.Prime then (1 : ℝ) else 0) ≤
      (if r.Coprime ((fouvryG9SievePrimes N z).prod id) then 1 else 0) +
      (if (r : ℝ) < z then 1 else 0) := by
  by_cases hs : (r : ℝ) < z
  · simp only [if_pos hs]
    split_ifs <;> norm_num
  · by_cases hp : r.Prime
    · have hc := fouvryG9PrimeOutput_coprime (N := N) hp (le_of_not_gt hs)
      simp only [if_pos hp, if_pos hc, if_neg hs, add_zero, le_refl]
    · simp only [if_neg hp,if_neg hs,add_zero]
      split_ifs <;> norm_num

/-- Prime-output count on the original labelled positive-prefix atoms. -/
def fouvryG9MotherPrimeOutput (N : ℕ) (e : ℝ) : ℝ :=
  ∑ a ∈ goldbachB9LowPositivePrefixAtoms N e,
    if (((N : ℤ)-((a.1.2*a.2 : ℕ) : ℤ)*a.1.1).natAbs).Prime then 1 else 0

/-- The real positive-cover theorem, applied to the small-output indicator. -/
theorem fouvryG9SmallOutput_mother_le_rectangles {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (z : ℝ)
    (hbig : ∀ k ∈ fouvryG9GridUsed N e ρ, 3 ≤ ρ^k.1) :
    (∑ a ∈ goldbachB9LowPositivePrefixAtoms N e,
      if (((N : ℤ)-((a.1.2*a.2 : ℕ) : ℤ)*a.1.1).natAbs : ℝ) < z then (1 : ℝ) else 0) ≤
      ∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9SmallOutputRectangle N ρ k z := by
  let F := fun n m : ℕ => if (((N : ℤ)-(m : ℤ)*n).natAbs : ℝ) < z then (1 : ℝ) else 0
  change (∑ a ∈ goldbachB9LowPositivePrefixAtoms N e, F a.1.1 (a.1.2*a.2)) ≤ _
  rw [fouvryG9_sum_reindex, ← fouvryG9GridCell_sum N e ρ]
  apply sum_le_sum
  intro k hk
  exact fouvryG9Long_cell_le_prime_rectangle hN hρ hρu k (hbig k hk)
    (fouvryG9GridCell_nonempty_iff.mpr hk) F (by intro n m; dsimp [F]; split_ifs <;> norm_num)

/-- Correct replacement for the false claim that every prime output is sifted. -/
theorem fouvryG9MotherPrimeOutput_le_sifted_add_small {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (z : ℝ)
    (hbig : ∀ k ∈ fouvryG9GridUsed N e ρ, 3 ≤ ρ^k.1) :
    fouvryG9MotherPrimeOutput N e ≤
      fouvryG9MotherSifted N e (fouvryG9SievePrimes N z) +
        ∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9SmallOutputRectangle N ρ k z := by
  calc
    _ ≤ fouvryG9MotherSifted N e (fouvryG9SievePrimes N z) +
        (∑ a ∈ goldbachB9LowPositivePrefixAtoms N e,
          if (((N : ℤ)-((a.1.2*a.2 : ℕ) : ℤ)*a.1.1).natAbs : ℝ) < z then (1 : ℝ) else 0) := by
      unfold fouvryG9MotherPrimeOutput fouvryG9MotherSifted
      rw [← sum_add_distrib]
      exact sum_le_sum (fun a _ => fouvryG9PrimeOutput_indicator N _ z)
    _ ≤ _ := add_le_add (le_refl _) (fouvryG9SmallOutput_mother_le_rectangles hN hρ hρu z hbig)

/-- The corrected prime-output upper sieve. Both error budgets use A+1. -/
theorem fouvryG9MotherPrimeOutput_total (A : ℕ) {e ε δ η ρ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ z : ℝ,
      0 ≤ z → z ≤ Real.sqrt (N : ℝ) →
      fouvryG9MotherPrimeOutput N e ≤
        (∑ k ∈ fouvryG9GridUsed N e ρ,
          fouvryG9RectangleMain N ρ δ η k (fouvryG9SievePrimes N z) z) +
            (N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨N₁,h₁⟩ := fouvryG9MotherSifted_total (A+1) he he1 hε hεa hεδ hδ hη hηu hρ hρu
  obtain ⟨N₂,h₂⟩ := fouvryG9SmallOutput_total (A+1) hρ
  obtain ⟨N₃,h₃⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (4/53) (by norm_num))
  refine ⟨max N₁ (max (N₂ : ℝ) (max N₃ (Real.exp 2))), ?_⟩
  intro N hN z hz hzu
  have hN₁ : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have ha := (le_max_right _ _).trans hN
  have hN₂ : N₂ ≤ N := by exact_mod_cast (le_max_left _ _).trans ha
  have hb := (le_max_right _ _).trans ha
  have hN₃ : N₃ ≤ (N : ℝ) := (le_max_left _ _).trans hb
  have hexp : Real.exp 2 ≤ (N : ℝ) := (le_max_right _ _).trans hb
  have hN0 : 0 < (N : ℝ) := (Real.exp_pos 2).trans_le hexp
  have hlog : 2 ≤ Real.log (N : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 2) hexp
  have hN1 : 1 ≤ N := by
    exact_mod_cast (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hexp
  have hsix : 6 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using h₃ N hN₃
  have hbig : ∀ k ∈ fouvryG9GridUsed N e ρ, 3 ≤ ρ^k.1 := by
    intro k hk
    have hg := fouvryG9Grid_buffered_geometry he hρ hρu (fouvryG9GridCell_nonempty_iff.mpr hk)
    dsimp only at hg
    linarith [hg.2.2.2.1]
  have hpay : (N : ℝ)/Real.log (N : ℝ)^(A+1) +
      (N : ℝ)/Real.log (N : ℝ)^(A+1) ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
    have hl0 : 0 < Real.log (N : ℝ) := by linarith
    rw [pow_succ, div_mul_eq_div_div]
    have hp0 : 0 ≤ (N : ℝ)/Real.log (N : ℝ)^A := by positivity
    have hh : ((N : ℝ)/Real.log (N : ℝ)^A)/Real.log (N : ℝ) ≤
        ((N : ℝ)/Real.log (N : ℝ)^A)/2 :=
      div_le_div_of_nonneg_left hp0 (by norm_num) hlog
    linarith
  calc
    _ ≤ fouvryG9MotherSifted N e (fouvryG9SievePrimes N z) +
        ∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9SmallOutputRectangle N ρ k z :=
      fouvryG9MotherPrimeOutput_le_sifted_add_small hN1 hρ hρu z hbig
    _ ≤ ((∑ k ∈ fouvryG9GridUsed N e ρ,
        fouvryG9RectangleMain N ρ δ η k (fouvryG9SievePrimes N z) z) +
        (N : ℝ)/Real.log (N : ℝ)^(A+1)) + (N : ℝ)/Real.log (N : ℝ)^(A+1) :=
      add_le_add (h₁ N hN₁ z) (h₂ N hN₂ e z hz hzu)
    _ ≤ _ := by linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
