import MathlibNt.SieveTheory.LiLiuFouvryG9SieveTotal
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9PositiveCover

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exactly the primes strictly below z that do not divide the actual N. -/
def fouvryG9SievePrimes (N : ℕ) (z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter (fun p => p.Prime ∧ p.Coprime N)

theorem fouvryG9SievePrimes_mem (N p : ℕ) (z : ℝ) :
    p ∈ fouvryG9SievePrimes N z ↔ p.Prime ∧ p.Coprime N ∧ (p : ℝ) < z := by
  simp only [fouvryG9SievePrimes,mem_filter,mem_range,Nat.lt_ceil]
  tauto

/-- Actual labelled mother count with a common sieve carrier; no label is merged. -/
def fouvryG9MotherSifted (N : ℕ) (e : ℝ) (P : Finset ℕ) : ℝ :=
  ∑ a ∈ goldbachB9LowPositivePrefixAtoms N e,
    if (((N : ℤ)-((a.1.2*a.2 : ℕ) : ℤ)*a.1.1).natAbs).Coprime (P.prod id) then 1 else 0

/-- Positive coverage transfers literal mother sieving into the actual rectangles. -/
theorem fouvryG9MotherSifted_le_rectangles {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (P : Finset ℕ)
    (hbig : ∀ k ∈ fouvryG9GridUsed N e ρ, 3 ≤ ρ^k.1) :
    fouvryG9MotherSifted N e P ≤
      ∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9RectangleSifted N ρ k P := by
  let F := fun n m : ℕ => if (((N : ℤ)-(m : ℤ)*n).natAbs).Coprime (P.prod id)
    then (1 : ℝ) else 0
  change (∑ a ∈ goldbachB9LowPositivePrefixAtoms N e, F a.1.1 (a.1.2*a.2)) ≤ _
  rw [fouvryG9_sum_reindex, ← fouvryG9GridCell_sum N e ρ]
  apply sum_le_sum
  intro k hk
  have h := fouvryG9Long_cell_le_prime_rectangle hN hρ hρu k (hbig k hk)
    (fouvryG9GridCell_nonempty_iff.mpr hk) F (by intro n m; dsimp [F]; split_ifs <;> norm_num)
  unfold fouvryG9RectangleSifted MathlibNt.SieveTheory.LiLiuPrereqWF.weightedSequenceSifted
  rw [sum_product]
  exact h

/-- A genuine mother-set upper sieve with the literal prime carrier. The only
remaining main-term task is the analytic estimate of the displayed densities. -/
theorem fouvryG9MotherSifted_total (A : ℕ) {e ε δ η ρ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ z : ℝ,
      fouvryG9MotherSifted N e (fouvryG9SievePrimes N z) ≤
        (∑ k ∈ fouvryG9GridUsed N e ρ,
          fouvryG9RectangleMain N ρ δ η k (fouvryG9SievePrimes N z) z) +
            (N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨N₁,h₁⟩ := fouvryG9Sieve_total A he he1 hε hεa hεδ hδ hη hηu hρ hρu
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (4/53) (by norm_num))
  refine ⟨max N₁ (max N₂ 1), ?_⟩
  intro N hN z
  have hN₁ := (le_max_left _ _).trans hN
  have hr := (le_max_right _ _).trans hN
  have hN₂ := (le_max_left _ _).trans hr
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_right _ _).trans hr
  have hsix : 6 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using h₂ N hN₂
  have hbig : ∀ k ∈ fouvryG9GridUsed N e ρ, 3 ≤ ρ^k.1 := by
    intro k hk
    have hg := fouvryG9Grid_buffered_geometry he hρ hρu (fouvryG9GridCell_nonempty_iff.mpr hk)
    dsimp only at hg
    linarith [hg.2.2.2.1]
  apply (fouvryG9MotherSifted_le_rectangles hN1 hρ hρu _ hbig).trans
  apply h₁ N hN₁ (fun _ => fouvryG9SievePrimes N z) (fun _ => z)
  · intro k hk p hp
    exact (fouvryG9SievePrimes_mem N p z |>.mp hp).1
  · intro k hk p hp
    exact (fouvryG9SievePrimes_mem N p z |>.mp hp).2.1
  · intro k hk p hp
    exact (fouvryG9SievePrimes_mem N p z |>.mp hp).2.2

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
