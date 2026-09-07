import MathlibNt.SieveTheory.LiLiuPrereqWFIntervalDensity

/-!
# Deleting zero-density primes without changing the actual density

The coefficients are unchanged on every surviving subset. Subsets containing
a deleted prime have zero density, irrespective of their Rosser admissibility.
In particular both entire defects, not merely their high-minimum parts, survive
this reduction exactly.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset
open scoped Classical

noncomputable def nonzeroDensityPrimes (B : Finset ℕ) (g : ℕ → ℝ) : Finset ℕ :=
  B.filter (fun p => g p ≠ 0)

theorem nonzeroDensityPrimes_subset (B : Finset ℕ) (g : ℕ → ℝ) :
    nonzeroDensityPrimes B g ⊆ B := Finset.filter_subset _ _

theorem nonzeroDensityPrimes_pos {B : Finset ℕ} {g : ℕ → ℝ}
    (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p < 1) :
    ∀ p ∈ nonzeroDensityPrimes B g, 0 < g p ∧ g p < 1 := by
  intro p hp
  obtain ⟨hpB, hp0⟩ := Finset.mem_filter.mp hp
  exact ⟨lt_of_le_of_ne (hg p hpB).1 (Ne.symm hp0), (hg p hpB).2⟩

theorem density_product_zero_of_not_subset {B s : Finset ℕ} {g : ℕ → ℝ}
    (hs : s ⊆ B) (hn : ¬s ⊆ nonzeroDensityPrimes B g) :
    ∏ p ∈ s, g p = 0 := by
  obtain ⟨p, hp, hpn⟩ := Finset.not_subset.mp hn
  have hp0 : g p = 0 := by
    simpa only [nonzeroDensityPrimes, Finset.mem_filter, hs hp, true_and,
      not_not] using hpn
  exact Finset.prod_eq_zero hp hp0

/-- Valid for the actual signed coefficient, with no bound or sign assumption. -/
theorem subsetDensity_delete_zero (c : Finset ℕ → ℝ) (B : Finset ℕ) (g : ℕ → ℝ) :
    (∑ s ∈ (nonzeroDensityPrimes B g).powerset, c s * ∏ p ∈ s, g p) =
      ∑ s ∈ B.powerset, c s * ∏ p ∈ s, g p := by
  apply Finset.sum_subset
    (Finset.powerset_mono.mpr (nonzeroDensityPrimes_subset B g))
  intro s hs hsn
  rw [density_product_zero_of_not_subset (Finset.mem_powerset.mp hs)
    (by simpa only [Finset.mem_powerset] using hsn), mul_zero]

theorem lowerSetDensity_delete_zero (L : ℝ) (B : Finset ℕ) (g : ℕ → ℝ) :
    lowerSetDensity L g (nonzeroDensityPrimes B g) = lowerSetDensity L g B :=
  subsetDensity_delete_zero (setWeight L) B g

theorem upperSetDensity_delete_zero (L : ℝ) (B : Finset ℕ) (g : ℕ → ℝ) :
    upperSetDensity L g (nonzeroDensityPrimes B g) = upperSetDensity L g B :=
  subsetDensity_delete_zero (upperSetWeight L) B g

theorem eulerProduct_delete_zero (B : Finset ℕ) (g : ℕ → ℝ) :
    (∏ p ∈ nonzeroDensityPrimes B g, (1 - g p)) =
      ∏ p ∈ B, (1 - g p) := by
  apply Finset.prod_subset (nonzeroDensityPrimes_subset B g)
  intro p hp hpn
  have hp0 : g p = 0 := by
    simpa only [nonzeroDensityPrimes, Finset.mem_filter, hp, true_and,
      not_not] using hpn
  simp only [hp0, sub_zero]

theorem dimensionOneProductBound_delete_zero {P : Finset ℕ} {g : ℕ → ℝ} {K : ℝ}
    (h : DimensionOneProductBound P g K) :
    DimensionOneProductBound (nonzeroDensityPrimes P g) g K := by
  intro w z hw hwz
  have heq : (nonzeroDensityPrimes P g).filter
      (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) =
      nonzeroDensityPrimes
        (P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)) g := by
    ext p
    simp only [nonzeroDensityPrimes, Finset.mem_filter]
    tauto
  rw [heq, Finset.prod_inv_distrib, eulerProduct_delete_zero,
    ← Finset.prod_inv_distrib]
  exact h w z hw hwz

/-- Truncation at the actual cutoff uses the product hypothesis at `min z u`.
No density assumption on primes above `u` is needed. -/
theorem dimensionOneProductBound_truncate {P : Finset ℕ} {g : ℕ → ℝ} {K : ℝ}
    (h : DimensionOneProductBound P g K) (hK : 0 ≤ K) (u : ℝ) :
    DimensionOneProductBound
      (P.filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < u)) g K := by
  intro w z hw hwz
  have hwlog : 0 < Real.log w := Real.log_pos (by linarith)
  have hzlog : Real.log w ≤ Real.log z :=
    Real.log_le_log (by linarith) hwz.le
  have hfactor : 1 ≤ 1 + K / Real.log w :=
    le_add_of_nonneg_right (div_nonneg hK hwlog.le)
  by_cases hwu : w < u
  · have hwm : w < min z u := lt_min hwz hwu
    have heq : (P.filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < u)).filter
        (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) =
        P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < min z u) := by
      ext p
      simp only [Finset.mem_filter, lt_min_iff]
      tauto
    rw [heq]
    exact (h w (min z u) hw hwm).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (Real.log_le_log (by linarith) (min_le_left z u)) hwlog.le)
        (zero_le_one.trans hfactor))
  · have heq : (P.filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < u)).filter
        (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨⟨_, _, hpu⟩, _, hwp, _⟩ := Finset.mem_filter.mp hp |>.imp_left
        (fun ht => Finset.mem_filter.mp ht)
      exact hwu (hwp.trans_lt hpu)
    rw [heq, Finset.prod_empty]
    have hratio : 1 ≤ Real.log z / Real.log w := (one_le_div hwlog).mpr hzlog
    exact one_le_mul_of_one_le_of_one_le hratio hfactor

theorem densityDefects_delete_zero (B : Finset ℕ) {L : ℝ} (g : ℕ → ℝ)
    (hL : 1 < L) (hB : ∀ p ∈ B, p.Prime) (hcut : ∀ p ∈ B, (p : ℝ) < L) :
    lowerDensityDefect L g ((nonzeroDensityPrimes B g).sort (· ≤ ·)) =
      lowerDensityDefect L g (B.sort (· ≤ ·)) ∧
    upperDensityDefect L g ((nonzeroDensityPrimes B g).sort (· ≤ ·)) =
      upperDensityDefect L g (B.sort (· ≤ ·)) := by
  have hlo (T : Finset ℕ) (hT : T ⊆ B) :=
    lowerSetDensity_eq_euler_sub_defect g hL (T.sort (· ≤ ·))
      (T.sort_nodup _) (T.pairwise_sort _)
      (fun p hp => hB p (hT (by simpa using hp)))
      (fun p hp => hcut p (hT (by simpa using hp)))
  have hup (T : Finset ℕ) (hT : T ⊆ B) :=
    upperSetDensity_eq_euler_add_defect g hL (T.sort (· ≤ ·))
      (T.sort_nodup _) (T.pairwise_sort _)
      (fun p hp => hB p (hT (by simpa using hp)))
  have hlB := hlo B (Finset.Subset.refl _)
  have hlT := hlo _ (nonzeroDensityPrimes_subset B g)
  have huB := hup B (Finset.Subset.refl _)
  have huT := hup _ (nonzeroDensityPrimes_subset B g)
  simp only [Finset.sort_toFinset, lowerSetDensity_delete_zero,
    upperSetDensity_delete_zero, eulerProduct_delete_zero] at hlB hlT huB huT
  constructor <;> linarith

/-- Exact density of the original divisor weights after deleting zero primes. -/
theorem weightDensities_delete_zero (B : Finset ℕ) (L : ℝ)
    (hB : ∀ p ∈ B, p.Prime) {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    (∑ d ∈ ((nonzeroDensityPrimes B g).prod id).divisors,
      lowerWeight ((nonzeroDensityPrimes B g).prod id) L d * g d) =
        ∑ d ∈ (B.prod id).divisors, lowerWeight (B.prod id) L d * g d ∧
    (∑ d ∈ ((nonzeroDensityPrimes B g).prod id).divisors,
      upperWeight ((nonzeroDensityPrimes B g).prod id) L d * g d) =
        ∑ d ∈ (B.prod id).divisors, upperWeight (B.prod id) L d * g d := by
  have hT : ∀ p ∈ nonzeroDensityPrimes B g, p.Prime :=
    fun p hp => hB p (nonzeroDensityPrimes_subset B g hp)
  have hpfB : (B.prod id).primeFactors = B := by
    simpa only [id_eq] using Nat.primeFactors_prod hB
  have hpfT : ((nonzeroDensityPrimes B g).prod id).primeFactors =
      nonzeroDensityPrimes B g := by
    simpa only [id_eq] using Nat.primeFactors_prod hT
  rw [lowerWeight_density_eq_setDensity L hg (primeProduct_squarefree _ hT),
    lowerWeight_density_eq_setDensity L hg (primeProduct_squarefree _ hB),
    upperWeight_density_eq_setDensity L hg (primeProduct_squarefree _ hT),
    upperWeight_density_eq_setDensity L hg (primeProduct_squarefree _ hB), hpfB, hpfT]
  exact ⟨lowerSetDensity_delete_zero L B g, upperSetDensity_delete_zero L B g⟩

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
