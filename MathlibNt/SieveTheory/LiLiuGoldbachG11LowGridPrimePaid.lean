import MathlibNt.SieveTheory.LiLiuGoldbachG11LowGridSiftedPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11GridSmallOutput

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11RectangleSmallMass_nonneg (N : ℕ) (U V : Finset ℕ) (z : ℝ) :
    0 ≤ goldbachG11RectangleSmallMass N U V z := by
  apply sum_nonneg
  intro v _
  exact mul_nonneg (goldbachG11RectangleWeight_nonneg N v) (by split_ifs <;> norm_num)

/-- Low-grid actual prime outputs, after fully paying both distribution and
small-output losses, with the canonical output sieve and no external premises. -/
theorem goldbachG11LowGrid_prime_outputs_paid (A : ℕ) {ε δ θ ρ : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1) (hδ : 0 < δ) (hδu : δ < 1/2)
    (hθ : 0 < θ) (hθu : θ < 1/8) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ z : ℝ,
      0 ≤ z → z ≤ Real.sqrt (N : ℝ) →
      (∑ k ∈ goldbachG11LowGridUsed N ε ρ,
        goldbachG11RectanglePrimeMass N (goldbachG11GridLong N ε ρ k)
          (goldbachG11GridShort N ρ k)) ≤
        goldbachG11LowGridDensityMain N ε δ θ ρ (fun _ => fouvryG9SievePrimes N z) (fun _ => z) +
          3*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨Ns,hs⟩ := goldbachG11LowGrid_sifted_paid A hε hεu hδ hδu hθ hθu hρ hρu
  obtain ⟨Nb,hb⟩ := goldbachG11Grid_small_outputs_paid A hρ
  refine ⟨max Ns Nb,?_⟩
  intro N hN z hz hzu
  obtain ⟨hNs,hNb⟩ := max_le_iff.mp hN
  have hS := hs N hNs (fun _ => fouvryG9SievePrimes N z) (fun _ => z)
    (fun _ _ p hp => ((fouvryG9SievePrimes_mem N p z).mp hp).1)
    (fun _ _ p hp => ((fouvryG9SievePrimes_mem N p z).mp hp).2.1)
    (fun _ _ p hp => ((fouvryG9SievePrimes_mem N p z).mp hp).2.2)
  have hB := hb N hNb ε (fun _ => z) (fun _ _ => ⟨hz,hzu⟩)
  have hsmall : (∑ k ∈ goldbachG11LowGridUsed N ε ρ,
      goldbachG11RectangleSmallMass N (goldbachG11GridLong N ε ρ k)
        (goldbachG11GridShort N ρ k) z) ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
    apply le_trans _ hB
    apply sum_le_sum_of_subset_of_nonneg
    · exact filter_subset _ _
    · intro k _ _
      exact goldbachG11RectangleSmallMass_nonneg N _ _ z
  have hp := sum_le_sum (s := goldbachG11LowGridUsed N ε ρ)
    (fun k _ => goldbachG11RectanglePrimeMass_le_sifted_add_small N
      (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k) z)
  rw [sum_add_distrib] at hp
  exact (hp.trans (add_le_add hS hsmall)).trans_eq (by ring)

/-- The original restricted first-prime fibres inherit the paid estimate;
all product-coefficient multiplicities are the existing literal ones. -/
theorem goldbachG11LowGrid_mother_outputs_paid (A : ℕ) {ε δ θ ρ : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1) (hδ : 0 < δ) (hδu : δ < 1/2)
    (hθ : 0 < θ) (hθu : θ < 1/8) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ z : ℝ,
      0 ≤ z → z ≤ Real.sqrt (N : ℝ) →
      (∑ k ∈ goldbachG11LowGridUsed N ε ρ,
        goldbachG11RectangleMotherCount N ε (goldbachG11GridLong N ε ρ k)
          (goldbachG11GridShort N ρ k)) ≤
        goldbachG11LowGridDensityMain N ε δ θ ρ (fun _ => fouvryG9SievePrimes N z) (fun _ => z) +
          3*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨M,hM⟩ := goldbachG11LowGrid_prime_outputs_paid A hε hεu hδ hδu hθ hθu hρ hρu
  refine ⟨M,?_⟩
  intro N hN z hz hzu
  exact (sum_le_sum (fun k _ => goldbachG11RectangleMotherCount_le_primeMass N ε
    (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k))).trans (hM N hN z hz hzu)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig