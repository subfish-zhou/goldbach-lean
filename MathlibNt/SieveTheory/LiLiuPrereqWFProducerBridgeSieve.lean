import MathlibNt.SieveTheory.LiLiuPrereqWFRounding
import MathlibNt.SieveTheory.LiLiuPrereqWFZeroDensity
import Mathlib.NumberTheory.SelbergSieve

/-!
# A genuine density sieve on the zero-deleted small-prime carrier

The counting data are empty: this object is used only for its actual
`BoundingSieve.nu`, prime carrier, and `mainSum`. Its density function is the
original multiplicative function, not a new density chosen to fit a conclusion.
Deleting its zero primes preserves both entire signed Rosser densities and the
Euler product, including when the surviving carrier is empty.

No unadmitted producer module is imported here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset
open scoped Classical

/-- The analytic sieve with the original density and exactly its nonzero
primes in `B`. The empty counting support imposes no extra hypothesis on `g`. -/
noncomputable def densityBoundingSieve (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) (g : ArithmeticFunction ℝ)
    (hgm : g.IsMultiplicative) (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p < 1) :
    BoundingSieve where
  support := ∅
  prodPrimes := (nonzeroDensityPrimes B g).prod id
  prodPrimes_squarefree := primeProduct_squarefree _
    (fun p hp => hB p (nonzeroDensityPrimes_subset B g hp))
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := g
  nu_mult := hgm
  nu_pos_of_prime := by
    intro p hp hpd
    have hpf : ((nonzeroDensityPrimes B g).prod id).primeFactors =
        nonzeroDensityPrimes B g := by
      simpa only [id_eq] using Nat.primeFactors_prod
        (fun q hq => hB q (nonzeroDensityPrimes_subset B g hq))
    have hmem : p ∈ nonzeroDensityPrimes B g := by
      rw [← hpf, Nat.mem_primeFactors]
      exact ⟨hp, hpd, (primeProduct_squarefree _
        (fun q hq => hB q (nonzeroDensityPrimes_subset B g hq))).ne_zero⟩
    exact (nonzeroDensityPrimes_pos hg p hmem).1
  nu_lt_one_of_prime := by
    intro p hp hpd
    have hpf : ((nonzeroDensityPrimes B g).prod id).primeFactors =
        nonzeroDensityPrimes B g := by
      simpa only [id_eq] using Nat.primeFactors_prod
        (fun q hq => hB q (nonzeroDensityPrimes_subset B g hq))
    have hmem : p ∈ nonzeroDensityPrimes B g := by
      rw [← hpf, Nat.mem_primeFactors]
      exact ⟨hp, hpd, (primeProduct_squarefree _
        (fun q hq => hB q (nonzeroDensityPrimes_subset B g hq))).ne_zero⟩
    exact (nonzeroDensityPrimes_pos hg p hmem).2

variable (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
  (g : ArithmeticFunction ℝ) (hgm : g.IsMultiplicative)
  (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p < 1)

@[simp]
theorem densityBoundingSieve_nu :
    (densityBoundingSieve B hB g hgm hg).nu = g := rfl

@[simp]
theorem densityBoundingSieve_primeFactors :
    (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors =
      nonzeroDensityPrimes B g := by
  change ((nonzeroDensityPrimes B g).prod id).primeFactors = _
  simpa only [id_eq] using Nat.primeFactors_prod
    (fun p hp => hB p (nonzeroDensityPrimes_subset B g hp))

theorem densityBoundingSieve_mem_primeFactors (p : ℕ) :
    p ∈ (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors ↔
      p ∈ B ∧ g p ≠ 0 := by
  rw [densityBoundingSieve_primeFactors]
  exact Finset.mem_filter

theorem densityBoundingSieve_prime_lt_ceil {u : ℝ}
    (hcut : ∀ p ∈ B, (p : ℝ) < u) :
    ∀ p ∈ (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors,
      p < ⌈u⌉₊ := by
  intro p hp
  exact Nat.lt_ceil.mpr
    (hcut p ((densityBoundingSieve_mem_primeFactors B hB g hgm hg p).mp hp).1)

theorem densityBoundingSieve_rounded_carrier {L u : ℝ}
    (hL : 1 < L) (hu : 1 < u) (hcut : ∀ p ∈ B, (p : ℝ) < u) :
    (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors.filter
      (fun p => p < ⌈(⌈L⌉₊ : ℝ) ^ (1 / roundedSieveCoordinate L u)⌉₊) =
        nonzeroDensityPrimes B g := by
  rw [roundedSieveCoordinate_cutoff hL hu, Finset.filter_eq_self.mpr
    (densityBoundingSieve_prime_lt_ceil B hB g hgm hg hcut),
    densityBoundingSieve_primeFactors]

theorem densityBoundingSieve_euler :
    (∏ p ∈ (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors,
      (1 - (densityBoundingSieve B hB g hgm hg).nu p)) =
        ∏ p ∈ B, (1 - g p) := by
  rw [densityBoundingSieve_primeFactors, densityBoundingSieve_nu,
    eulerProduct_delete_zero]

/-- The level and the carrier are both changed, but the entire signed density
of each of the original weights is preserved exactly. -/
theorem densityBoundingSieve_mainSums (L : ℝ) :
    let S := densityBoundingSieve B hB g hgm hg
    S.mainSum (lowerWeight S.prodPrimes (⌈L⌉₊ : ℝ)) =
        ∑ d ∈ (B.prod id).divisors, lowerWeight (B.prod id) L d * g d ∧
    S.mainSum (upperWeight S.prodPrimes (⌈L⌉₊ : ℝ)) =
        ∑ d ∈ (B.prod id).divisors, upperWeight (B.prod id) L d * g d := by
  dsimp only
  rw [lowerWeight_ceil, upperWeight_ceil]
  exact weightDensities_delete_zero B L hB hgm

theorem densityBoundingSieve_mainSums_eq_setDensities (L : ℝ) :
    let S := densityBoundingSieve B hB g hgm hg
    S.mainSum (lowerWeight S.prodPrimes (⌈L⌉₊ : ℝ)) = lowerSetDensity L g B ∧
    S.mainSum (upperWeight S.prodPrimes (⌈L⌉₊ : ℝ)) = upperSetDensity L g B := by
  have hpf : (B.prod id).primeFactors = B := by
    simpa only [id_eq] using Nat.primeFactors_prod hB
  have h := densityBoundingSieve_mainSums B hB g hgm hg L
  rw [lowerWeight_density_eq_setDensity L hgm (primeProduct_squarefree B hB),
    upperWeight_density_eq_setDensity L hgm (primeProduct_squarefree B hB), hpf] at h
  exact h

/-- The lower sign remains minus; the upper sign remains plus. These are the
whole original defects, not only a truncation or high-minimum part. -/
theorem densityBoundingSieve_mainSums_eq_fullDefects {L : ℝ}
    (hL : 1 < L) (hcut : ∀ p ∈ B, (p : ℝ) < L) :
    let S := densityBoundingSieve B hB g hgm hg
    S.mainSum (lowerWeight S.prodPrimes (⌈L⌉₊ : ℝ)) =
        (∏ p ∈ B, (1 - g p)) - lowerDensityDefect L g (B.sort (· ≤ ·)) ∧
    S.mainSum (upperWeight S.prodPrimes (⌈L⌉₊ : ℝ)) =
        (∏ p ∈ B, (1 - g p)) + upperDensityDefect L g (B.sort (· ≤ ·)) := by
  have h := densityBoundingSieve_mainSums B hB g hgm hg L
  rw [lowerWeight_density_eq_euler_sub_defect B hL hB hcut hgm,
    upperWeight_density_eq_euler_add_defect B hL hB hgm] at h
  exact h

theorem densityBoundingSieve_dimensionOne {K : ℝ}
    (hdim : DimensionOneProductBound B g K) :
    DimensionOneProductBound
      (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors
      (densityBoundingSieve B hB g hgm hg).nu K := by
  rw [densityBoundingSieve_primeFactors, densityBoundingSieve_nu]
  exact dimensionOneProductBound_delete_zero hdim

/-- The producer's product formula has `w ≤ z`, unlike the local strict
interval convention. The extra diagonal case requires only `K ≥ 0`. -/
theorem densityBoundingSieve_localProduct {K : ℝ} (hK : 0 ≤ K)
    (hdim : DimensionOneProductBound B g K) :
    let S := densityBoundingSieve B hB g hgm hg
    ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (∏ p ∈ S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - S.nu p)⁻¹) ≤
          Real.log z / Real.log w * (1 + K / Real.log w) := by
  dsimp only
  intro w z hw hwz
  obtain rfl | hwz := hwz.eq_or_lt
  · have hE :
        (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p _ hp
      exact not_lt_of_ge hp.1 hp.2
    have hlog : 0 < Real.log w := Real.log_pos (by linarith)
    rw [hE, Finset.prod_empty, div_self hlog.ne', one_mul]
    exact le_add_of_nonneg_right (div_nonneg hK hlog.le)
  · have hfilter :
        (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors.filter
          (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) =
        (densityBoundingSieve B hB g hgm hg).prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
      ext p
      simp only [Finset.mem_filter]
      exact and_congr_right (fun hp =>
        and_iff_right (Nat.prime_of_mem_primeFactors hp))
    rw [← hfilter]
    exact densityBoundingSieve_dimensionOne B hB g hgm hg hdim w z hw hwz

theorem densityBoundingSieve_empty_carrier
    (hz : ∀ p ∈ B, g p = 0) :
    (densityBoundingSieve B hB g hgm hg).prodPrimes = 1 := by
  have hE : nonzeroDensityPrimes B g = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact (Finset.mem_filter.mp hp).2 (hz p (Finset.mem_filter.mp hp).1)
  change (nonzeroDensityPrimes B g).prod id = 1
  rw [hE, Finset.prod_empty]

#check densityBoundingSieve
#print axioms densityBoundingSieve
#print axioms densityBoundingSieve_mainSums_eq_fullDefects
#print axioms densityBoundingSieve_rounded_carrier
#print axioms densityBoundingSieve_dimensionOne
#print axioms densityBoundingSieve_localProduct

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
