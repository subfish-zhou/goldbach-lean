import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryFiniteSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridErrorPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11GridSmallOutput

open Finset
open scoped BigOperators Classical
open Wu2004MeanValue
open MathlibNt.SieveTheory.LiLiuPrereqWF
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original ordinary pi-centered main term on any selected actual cells. -/
def goldbachG11OrdinaryDensityMain (N : ℕ) (ε ρ δ θ : ℝ) (S : Finset (ℕ × ℕ))
    (P : (ℕ × ℕ) → Finset ℕ) (z : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ k ∈ S, ∑ m ∈ goldbachG11GridLong N ε ρ k,
    (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ)*
    (realPrimeCount (goldbachG11GridProfileHi ρ k)-realPrimeCount (goldbachG11GridProfileLo N ρ k))*
    externalDensity true (P k) (externalInternalLevel (goldbachG11OrdinaryLevel N δ) θ) θ (z k)
      (progressionDensity m)

/-- Fully paid ordinary sifted counts on any subset of occupied cells.
The threshold precedes epsilon, the cell subset and all changing sieve data. -/
theorem goldbachG11OrdinaryGrid_sifted_paid (A : ℕ) {δ θ ρ : ℝ}
    (hδ : 0 < δ) (hδu : δ < 1/2) (hθ : 0 < θ) (hθu : θ < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ,
      ∀ S : Finset (ℕ × ℕ), S ⊆ goldbachG11GridUsed N ε ρ →
      ∀ (P : (ℕ × ℕ) → Finset ℕ) (z : (ℕ × ℕ) → ℝ),
      (∀ k ∈ S, ∀ p ∈ P k, p.Prime) → (∀ k ∈ S, ∀ p ∈ P k, p.Coprime N) →
      (∀ k ∈ S, ∀ p ∈ P k, (p : ℝ) < z k) →
      (∑ k ∈ S, goldbachG11AllPrimeSiftedMass N (goldbachG11GridLong N ε ρ k)
        (goldbachG11GridShort N ρ k) (P k)) ≤
        goldbachG11OrdinaryDensityMain N ε ρ δ θ S P z+(N : ℝ)/Real.log (N : ℝ)^A := by
  let F : ℝ := Real.exp (8*(θ⁻¹)^3)
  obtain ⟨Me,hMe,he⟩ := goldbachG11OrdinaryGrid_error_total A F (Real.exp_pos _).le hδ hρ hρu
  obtain ⟨Mg,_hMg,hg⟩ := goldbachG11OrdinaryLevel_gates hδ.le hδu hθ
  refine ⟨max Me Mg,hMe.trans (le_max_left _ _),?_⟩
  intro N hN ε S hS P z hP hPN hcut
  obtain ⟨hNe,hNg⟩ := max_le_iff.mp hN
  obtain ⟨hbig,hQ,hD,_hQN⟩ := hg N hNg
  let E := fun k => ∑ d ∈ goldbachG11LinkedModuli N ⌊goldbachG11OrdinaryLevel N δ⌋₊,
    |goldbachG11OrdinaryRectangleResidual N ε ρ k d N|
  have herr : F*(∑ k ∈ S,E k) ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
    apply le_trans _ (he N hNe ε)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply sum_le_sum_of_subset_of_nonneg hS
    intro k _ _
    exact sum_nonneg fun d _ => abs_nonneg _
  have hu := sum_le_sum (s := S) (fun k hk =>
    goldbachG11OrdinaryGrid_sifted_upper hρ hρu hbig (hS hk) (P k)
      (hP k hk) (hPN k hk) hQ hD hθ hθu (hcut k hk))
  rw [sum_add_distrib,← mul_sum] at hu
  exact hu.trans (add_le_add (le_refl _) herr)

/-- Only the sifted part is enlarged to all primes. The original already-paid
small-output budget is retained, so no new all-prime fibre estimate is needed. -/
theorem goldbachG11OrdinaryGrid_prime_outputs_paid (A : ℕ) {δ θ ρ : ℝ}
    (hδ : 0 < δ) (hδu : δ < 1/2) (hθ : 0 < θ) (hθu : θ < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ,
      ∀ S : Finset (ℕ × ℕ), S ⊆ goldbachG11GridUsed N ε ρ →
      ∀ z : ℝ, 0 ≤ z → z ≤ Real.sqrt (N : ℝ) →
      (∑ k ∈ S, goldbachG11RectanglePrimeMass N (goldbachG11GridLong N ε ρ k)
        (goldbachG11GridShort N ρ k)) ≤
        goldbachG11OrdinaryDensityMain N ε ρ δ θ S
          (fun _ => fouvryG9SievePrimes N z) (fun _ => z)+2*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨Ms,hMs,hs⟩ := goldbachG11OrdinaryGrid_sifted_paid A hδ hδu hθ hθu hρ hρu
  obtain ⟨Mb,hb⟩ := goldbachG11Grid_small_outputs_paid A hρ
  refine ⟨max Ms ⌈Mb⌉₊,hMs.trans (le_max_left _ _),?_⟩
  intro N hN ε S hS z hz hzu
  obtain ⟨hNs,hNb⟩ := max_le_iff.mp hN
  have hNbR : Mb ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNb)
  have hmain := hs N hNs ε S hS (fun _ => fouvryG9SievePrimes N z) (fun _ => z)
    (fun _ _ p hp => ((fouvryG9SievePrimes_mem N p z).mp hp).1)
    (fun _ _ p hp => ((fouvryG9SievePrimes_mem N p z).mp hp).2.1)
    (fun _ _ p hp => ((fouvryG9SievePrimes_mem N p z).mp hp).2.2)
  have hsmallAll := hb N hNbR ε (fun _ => z) (fun _ _ => ⟨hz,hzu⟩)
  have hsmall : (∑ k ∈ S,goldbachG11RectangleSmallMass N (goldbachG11GridLong N ε ρ k)
      (goldbachG11GridShort N ρ k) z) ≤ (N : ℝ)/Real.log (N : ℝ)^A := by
    apply le_trans _ hsmallAll
    apply sum_le_sum_of_subset_of_nonneg hS
    intro k _ _
    apply sum_nonneg
    intro v _
    exact mul_nonneg (goldbachG11RectangleWeight_nonneg N v) (by split_ifs <;> norm_num)
  have hu := sum_le_sum (s := S) (fun k _ =>
    goldbachG11RectanglePrimeMass_le_allPrime_sifted_add_small N
      (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k) z)
  rw [sum_add_distrib] at hu
  exact (hu.trans (add_le_add hmain hsmall)).trans_eq (by ring)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig