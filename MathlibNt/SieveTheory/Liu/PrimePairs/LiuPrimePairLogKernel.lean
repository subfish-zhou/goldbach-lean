import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainSum
import MathlibNt.SieveTheory.Arithmetic.PrimeReciprocalLogRectangle

/-!
# Liu's prime-pair logarithmic kernel

This module rewrites Liu's reciprocal-log pair sum as the exact kernel in the
logarithmic prime coordinates `log p / log N`.  It then bounds the contribution
from a fixed exponent rectangle by the corresponding ordered-prime reciprocal
mass, and aggregates any finite rectangle cover.  Overlap in the cover is
allowed; no moving-boundary or limit transfer is asserted.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset
open PrimeReciprocalLogScale PrimeReciprocalLogRectangle

/-- The logarithmic exponent coordinate of a prime relative to `N`. -/
noncomputable def primeLogExponent (N p : ℕ) : ℝ :=
  Real.log (p : ℝ) / Real.log (N : ℝ)

/-- Membership in the fixed exponent rectangle `(a₀, a₁] × (b₀, b₁]`. -/
def LiuPairInLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) (p : ℕ × ℕ) : Prop :=
  a₀ < primeLogExponent N p.1 ∧ primeLogExponent N p.1 ≤ a₁ ∧
    b₀ < primeLogExponent N p.2 ∧ primeLogExponent N p.2 ≤ b₁

/-- Liu pairs whose logarithmic coordinates lie in one fixed rectangle. -/
noncomputable def liuPairsInLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).filter
      (LiuPairInLogRectangle N a₀ a₁ b₀ b₁)

/-- The exact normalized logarithmic kernel attached to an ordered pair. -/
noncomputable def liuPairLogKernel (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  1 / (((p.1 : ℝ) * p.2) *
    (1 - primeLogExponent N p.1 - primeLogExponent N p.2))

/-- The full finite logarithmic-kernel sum over Liu's ordered prime pairs. -/
noncomputable def liuPairLogKernelSum (N : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    liuPairLogKernel N p

/-- The logarithmic-kernel contribution from Liu pairs in one fixed rectangle. -/
noncomputable def liuPairLogKernelRectangleContribution
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : ℝ :=
  ∑ p ∈ liuPairsInLogRectangle N a₀ a₁ b₀ b₁, liuPairLogKernel N p

/-- Positive bases have the expected power-cutoff interpretation in logarithmic
coordinates. -/
theorem primeLogExponent_mem_interval_iff {N p : ℕ} (hN : 1 < N) (hp : 0 < p)
    (a₀ a₁ : ℝ) :
    (a₀ < primeLogExponent N p ∧ primeLogExponent N p ≤ a₁) ↔
      ((N : ℝ) ^ a₀ < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ a₁) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [primeLogExponent, lt_div_iff₀ hlogN] at hlower
      rw [Real.rpow_def_of_pos hNpos, ← Real.exp_log hpReal, Real.exp_lt_exp]
      simpa [mul_comm] using hlower
    · rw [primeLogExponent, div_le_iff₀ hlogN] at hupper
      rw [← Real.exp_log hpReal, Real.rpow_def_of_pos hNpos, Real.exp_le_exp]
      simpa [mul_comm] using hupper
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [Real.rpow_def_of_pos hNpos, ← Real.exp_log hpReal,
        Real.exp_lt_exp] at hlower
      rw [primeLogExponent, lt_div_iff₀ hlogN]
      simpa [mul_comm] using hlower
    · rw [← Real.exp_log hpReal, Real.rpow_def_of_pos hNpos,
        Real.exp_le_exp] at hupper
      rw [primeLogExponent, div_le_iff₀ hlogN]
      simpa [mul_comm] using hupper

/-- Exact logarithmic change of variables for every Liu source pair. -/
theorem log_div_pair_eq_log_mul_one_sub_exponents
    {N : ℕ} (hN : 8 ≤ N) {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    Real.log ((N : ℝ) / ((p.1 : ℝ) * p.2)) =
      Real.log (N : ℝ) *
        (1 - primeLogExponent N p.1 - primeLogExponent N p.2) := by
  have hconditions := mem_liuWeightPairs.mp hp
  have hNpos : (0 : ℝ) < N := by positivity
  have hp₁pos : (0 : ℝ) < p.1 := by exact_mod_cast hconditions.1.pos
  have hp₂pos : (0 : ℝ) < p.2 := by exact_mod_cast hconditions.2.1.pos
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  rw [Real.log_div (ne_of_gt hNpos)
      (mul_ne_zero (ne_of_gt hp₁pos) (ne_of_gt hp₂pos)),
    Real.log_mul (ne_of_gt hp₁pos) (ne_of_gt hp₂pos)]
  unfold primeLogExponent
  field_simp [hlogN]
  ring

/-- The kernel denominator is positive on every Liu source pair. -/
theorem one_sub_primeLogExponent_pos
    {N : ℕ} (hN : 8 ≤ N) {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    0 < 1 - primeLogExponent N p.1 - primeLogExponent N p.2 := by
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogdiv : 0 < Real.log ((N : ℝ) / ((p.1 : ℝ) * p.2)) :=
    Real.log_pos (by
      have htwo := two_le_div_of_mem_liuWeightPairs hN hp
      exact lt_of_lt_of_le (by norm_num) htwo)
  rw [log_div_pair_eq_log_mul_one_sub_exponents hN hp] at hlogdiv
  exact pos_of_mul_pos_right hlogdiv hlogN.le

/-- Multiplying Liu's reciprocal-log sum by `log N` gives the exact finite
logarithmic-kernel sum, with ordered pairs and real division unchanged. -/
theorem log_mul_liuSourceReciprocalLogSum_eq_pairLogKernelSum
    (N : ℕ) (hN : 8 ≤ N) :
    Real.log (N : ℝ) * liuSourceReciprocalLogSum N =
      liuPairLogKernelSum N := by
  unfold liuSourceReciprocalLogSum liuPairLogKernelSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hconditions := mem_liuWeightPairs.mp hp
  have hp₁pos : (0 : ℝ) < p.1 := by exact_mod_cast hconditions.1.pos
  have hp₂pos : (0 : ℝ) < p.2 := by exact_mod_cast hconditions.2.1.pos
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hkernel :
      1 - primeLogExponent N p.1 - primeLogExponent N p.2 ≠ 0 :=
    ne_of_gt (one_sub_primeLogExponent_pos hN hp)
  rw [log_div_pair_eq_log_mul_one_sub_exponents hN hp]
  unfold liuPairLogKernel
  field_simp [hlogN, hkernel, ne_of_gt hp₁pos, ne_of_gt hp₂pos]

/-- Every kernel summand on the Liu pair set is nonnegative. -/
theorem liuPairLogKernel_nonneg
    {N : ℕ} (hN : 8 ≤ N) {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    0 ≤ liuPairLogKernel N p := by
  have hprod : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    exact_mod_cast liuWeightPairs_product_pos hp
  exact one_div_nonneg.mpr
    (mul_nonneg hprod.le (one_sub_primeLogExponent_pos hN hp).le)

/-- The kernel contribution of any fixed exponent rectangle is nonnegative. -/
theorem liuPairLogKernelRectangleContribution_nonneg
    (N : ℕ) (hN : 8 ≤ N) (a₀ a₁ b₀ b₁ : ℝ) :
    0 ≤ liuPairLogKernelRectangleContribution N a₀ a₁ b₀ b₁ := by
  classical
  unfold liuPairLogKernelRectangleContribution
  apply Finset.sum_nonneg
  intro p hp
  rw [liuPairsInLogRectangle, Finset.mem_filter] at hp
  exact liuPairLogKernel_nonneg hN hp.1

/-- The finite product carrier underlying `primeReciprocalLogRectangle`. -/
noncomputable def primeLogRectanglePairs
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (rpowFloor N a₁ + 1)).filter fun p₁ : ℕ =>
      p₁.Prime ∧ (N : ℝ) ^ a₀ < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ a₁) ×ˢ
    ((Finset.range (rpowFloor N b₁ + 1)).filter fun p₂ : ℕ =>
      p₂.Prime ∧ (N : ℝ) ^ b₀ < (p₂ : ℝ) ∧ (p₂ : ℝ) ≤ (N : ℝ) ^ b₁)

/-- The product-carrier reciprocal sum is exactly the existing ordered-prime
rectangle mass. -/
theorem sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) :
    (∑ p ∈ primeLogRectanglePairs N a₀ a₁ b₀ b₁,
      1 / ((p.1 : ℝ) * p.2)) =
        primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ := by
  unfold primeLogRectanglePairs primeReciprocalLogRectangle
  rw [Finset.sum_product]

/-- Liu pairs selected by exponent coordinates form a subset of the existing
ordered-prime rectangle carrier. -/
theorem liuPairsInLogRectangle_subset_primeLogRectanglePairs
    {N : ℕ} (hN : 1 < N) (a₀ a₁ b₀ b₁ : ℝ) :
    liuPairsInLogRectangle N a₀ a₁ b₀ b₁ ⊆
      primeLogRectanglePairs N a₀ a₁ b₀ b₁ := by
  classical
  intro p hp
  rw [liuPairsInLogRectangle, Finset.mem_filter] at hp
  have hconditions := mem_liuWeightPairs.mp hp.1
  have hp₁bounds := (primeLogExponent_mem_interval_iff hN hconditions.1.pos
    a₀ a₁).mp ⟨hp.2.1, hp.2.2.1⟩
  have hp₂bounds := (primeLogExponent_mem_interval_iff hN hconditions.2.1.pos
    b₀ b₁).mp ⟨hp.2.2.2.1, hp.2.2.2.2⟩
  rw [primeLogRectanglePairs, Finset.mem_product]
  constructor
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hp₁bounds.2)),
      hconditions.1, hp₁bounds⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hp₂bounds.2)),
      hconditions.2.1, hp₂bounds⟩

/-- On a rectangle below `α + β = 1`, each kernel value is bounded by the
upper-right-corner kernel times the reciprocal pair weight. -/
theorem liuPairLogKernel_le_rectangleCorner
    {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N))
    {a₀ a₁ b₀ b₁ : ℝ}
    (hrect : LiuPairInLogRectangle N a₀ a₁ b₀ b₁ p)
    (hupper : a₁ + b₁ < 1) :
    liuPairLogKernel N p ≤
      (1 / (1 - a₁ - b₁)) * (1 / ((p.1 : ℝ) * p.2)) := by
  have hcorner : 0 < 1 - a₁ - b₁ := by linarith
  have hdenom :
      1 - a₁ - b₁ ≤
        1 - primeLogExponent N p.1 - primeLogExponent N p.2 := by
    linarith [hrect.2.1, hrect.2.2.2]
  have hinv :
      1 / (1 - primeLogExponent N p.1 - primeLogExponent N p.2) ≤
        1 / (1 - a₁ - b₁) :=
    one_div_le_one_div_of_le hcorner hdenom
  have hpair : 0 ≤ 1 / ((p.1 : ℝ) * p.2) := by
    exact one_div_nonneg.mpr (by
      exact_mod_cast (liuWeightPairs_product_pos hp).le)
  unfold liuPairLogKernel
  calc
    1 / (((p.1 : ℝ) * p.2) *
        (1 - primeLogExponent N p.1 - primeLogExponent N p.2)) =
        (1 / ((p.1 : ℝ) * p.2)) *
          (1 / (1 - primeLogExponent N p.1 - primeLogExponent N p.2)) := by
            simp only [one_div, mul_inv]
    _ ≤ (1 / ((p.1 : ℝ) * p.2)) * (1 / (1 - a₁ - b₁)) :=
      mul_le_mul_of_nonneg_left hinv hpair
    _ = (1 / (1 - a₁ - b₁)) * (1 / ((p.1 : ℝ) * p.2)) := by ring

/-- A fixed rectangle below the singular boundary contributes at most its
upper-right-corner kernel times the full ordered-prime rectangle mass. -/
theorem liuPairLogKernelRectangleContribution_le
    (N : ℕ) (hN : 8 ≤ N) (a₀ a₁ b₀ b₁ : ℝ)
    (hupper : a₁ + b₁ < 1) :
    liuPairLogKernelRectangleContribution N a₀ a₁ b₀ b₁ ≤
      (1 / (1 - a₁ - b₁)) *
        primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ := by
  have hcorner : 0 ≤ 1 / (1 - a₁ - b₁) := by
    exact one_div_nonneg.mpr (by linarith)
  have hsubset := liuPairsInLogRectangle_subset_primeLogRectanglePairs
    (show 1 < N by omega) a₀ a₁ b₀ b₁
  unfold liuPairLogKernelRectangleContribution
  calc
    (∑ p ∈ liuPairsInLogRectangle N a₀ a₁ b₀ b₁, liuPairLogKernel N p) ≤
        ∑ p ∈ liuPairsInLogRectangle N a₀ a₁ b₀ b₁,
          (1 / (1 - a₁ - b₁)) * (1 / ((p.1 : ℝ) * p.2)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N) ∧
          LiuPairInLogRectangle N a₀ a₁ b₀ b₁ p := by
        simpa [liuPairsInLogRectangle] using hp
      exact liuPairLogKernel_le_rectangleCorner hmem.1 hmem.2 hupper
    _ = (1 / (1 - a₁ - b₁)) *
        (∑ p ∈ liuPairsInLogRectangle N a₀ a₁ b₀ b₁,
          1 / ((p.1 : ℝ) * p.2)) := by rw [Finset.mul_sum]
    _ ≤ (1 / (1 - a₁ - b₁)) *
        (∑ p ∈ primeLogRectanglePairs N a₀ a₁ b₀ b₁,
          1 / ((p.1 : ℝ) * p.2)) := by
      apply mul_le_mul_of_nonneg_left _ hcorner
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp _
      rw [primeLogRectanglePairs, Finset.mem_product] at hp
      exact one_div_nonneg.mpr (mul_nonneg
        (Nat.cast_nonneg p.1) (Nat.cast_nonneg p.2))
    _ = (1 / (1 - a₁ - b₁)) *
        primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ := by
      rw [sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle]

/-- A finite family of positive rectangles may overlap: if it covers every Liu
pair and stays below `α + β = 1`, the full kernel sum is bounded by the sum of
the rectangle majorants. -/
theorem liuPairLogKernelSum_le_sum_rectangleMajorants_of_cover
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a₀ a₁ b₀ b₁ : ι → ℝ) (N : ℕ) (hN : 8 ≤ N)
    (_ha₀ : ∀ i ∈ s, 0 < a₀ i) (_ha : ∀ i ∈ s, a₀ i < a₁ i)
    (_hb₀ : ∀ i ∈ s, 0 < b₀ i) (_hb : ∀ i ∈ s, b₀ i < b₁ i)
    (hupper : ∀ i ∈ s, a₁ i + b₁ i < 1)
    (hcover : ∀ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
      ∃ i ∈ s, LiuPairInLogRectangle N (a₀ i) (a₁ i) (b₀ i) (b₁ i) p) :
    liuPairLogKernelSum N ≤
      ∑ i ∈ s, (1 / (1 - a₁ i - b₁ i)) *
        primeReciprocalLogRectangle N (a₀ i) (a₁ i) (b₀ i) (b₁ i) := by
  classical
  have hcoverSum :
      liuPairLogKernelSum N ≤
        ∑ i ∈ s, liuPairLogKernelRectangleContribution
          N (a₀ i) (a₁ i) (b₀ i) (b₁ i) := by
    unfold liuPairLogKernelSum
    calc
      (∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          liuPairLogKernel N p) ≤
          ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
            ∑ i ∈ s, if LiuPairInLogRectangle
                N (a₀ i) (a₁ i) (b₀ i) (b₁ i) p then
              liuPairLogKernel N p else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨i, hi, hip⟩ := hcover p hp
        have hsingle : ({i} : Finset ι) ⊆ s := by simpa using hi
        have hle :
            (∑ j ∈ ({i} : Finset ι), if LiuPairInLogRectangle
                N (a₀ j) (a₁ j) (b₀ j) (b₁ j) p then
              liuPairLogKernel N p else 0) ≤
              ∑ j ∈ s, if LiuPairInLogRectangle
                  N (a₀ j) (a₁ j) (b₀ j) (b₁ j) p then
                liuPairLogKernel N p else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsingle (fun j hj _ => by
            split_ifs
            · exact liuPairLogKernel_nonneg hN hp
            · exact le_rfl)
        simpa [hip] using hle
      _ = ∑ i ∈ s, liuPairLogKernelRectangleContribution
          N (a₀ i) (a₁ i) (b₀ i) (b₁ i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        unfold liuPairLogKernelRectangleContribution liuPairsInLogRectangle
        rw [Finset.sum_filter]
  exact hcoverSum.trans (Finset.sum_le_sum fun i hi =>
    liuPairLogKernelRectangleContribution_le N hN
      (a₀ i) (a₁ i) (b₀ i) (b₁ i) (hupper i hi))

end MathlibNt.SieveTheory.LiuWeight
