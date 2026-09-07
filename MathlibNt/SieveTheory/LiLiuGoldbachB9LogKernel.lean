import MathlibNt.SieveTheory.LiLiuGoldbachB9MainMassTransport
import MathlibNt.SieveTheory.LiLiuGoldbachB8LogKernel

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Finset
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle PrimeReciprocalLogScale

noncomputable local instance instDecidablePropB9LogKernel (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Closed C10 geometry, with no deletion of endpoints or repeated factors. -/
theorem goldbachB9Pair_logGeometry
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    (4 / 53 : ℝ) ≤ primeLogExponent N rs.1 ∧
      primeLogExponent N rs.1 ≤ (1 / 3 : ℝ) ∧
      (1 / 3 : ℝ) ≤ primeLogExponent N rs.2 ∧
      primeLogExponent N rs.1 + 2 * primeLogExponent N rs.2 ≤ 1 := by
  obtain ⟨hr, hs, _, hcut, hrupper, hslower, hprod⟩ := mem_goldbachC10Pairs_iff.mp hrs
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hrp : (0 : ℝ) < rs.1 := by exact_mod_cast hr.pos
  have hsp : (0 : ℝ) < rs.2 := by exact_mod_cast hs.pos
  have hcutlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hcut
  have hrlog := Real.log_le_log hrp hrupper
  have hslog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hslower
  rw [Real.log_rpow hNp] at hcutlog hrlog hslog
  have hprodR : (rs.1 : ℝ) * (rs.2 : ℝ) ^ 2 ≤ N := by exact_mod_cast hprod
  have hprodlog := Real.log_le_log (mul_pos hrp (pow_pos hsp 2)) hprodR
  rw [Real.log_mul hrp.ne' (pow_ne_zero 2 hsp.ne'), Real.log_pow] at hprodlog
  refine ⟨(le_div_iff₀ hln).mpr hcutlog, (div_le_iff₀ hln).mpr hrlog,
    (le_div_iff₀ hln).mpr hslog, ?_⟩
  unfold primeLogExponent
  rw [show Real.log (rs.1 : ℝ) / Real.log (N : ℝ) +
      2 * (Real.log (rs.2 : ℝ) / Real.log (N : ℝ)) =
      (Real.log (rs.1 : ℝ) + 2 * Real.log (rs.2 : ℝ)) /
        Real.log (N : ℝ) by ring]
  exact (div_le_one hln).mpr (by simpa using hprodlog)

theorem goldbachB9PrimeLogExponent_second_le_upper
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    primeLogExponent N rs.2 ≤ (1 / 2 : ℝ) := by
  obtain ⟨hlow, _, _, htriangle⟩ := goldbachB9Pair_logGeometry hN hrs
  linarith

theorem goldbachB9OneSubPrimeLogExponent_pos
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    0 < 1 - primeLogExponent N rs.1 - primeLogExponent N rs.2 := by
  have hfirst := (goldbachB9Pair_logGeometry hN hrs).2.1
  have hsecond := goldbachB9PrimeLogExponent_second_le_upper hN hrs
  linarith

theorem goldbachB9LogProd_eq
    {N : ℕ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    Real.log (goldbachC10Prod rs : ℝ) =
      Real.log (rs.1 : ℝ) + Real.log (rs.2 : ℝ) := by
  have h := mem_goldbachC10Pairs_iff.mp hrs
  have hrp : (0 : ℝ) < rs.1 := by exact_mod_cast h.1.pos
  have hsp : (0 : ℝ) < rs.2 := by exact_mod_cast h.2.1.pos
  simp only [goldbachC10Prod, Nat.cast_mul, Real.log_mul hrp.ne' hsp.ne']

theorem goldbachB9PairLogKernelTerm_eq
    {N : ℕ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    1 / ((goldbachC10Prod rs : ℝ) *
      (1 - Real.log (goldbachC10Prod rs : ℝ) / Real.log (N : ℝ))) =
        liuPairLogKernel N rs := by
  rw [goldbachB9LogProd_eq hrs]
  simp only [goldbachC10Prod, Nat.cast_mul, liuPairLogKernel, primeLogExponent,
    add_div, sub_sub]

theorem goldbachB9PairLogKernel_eq_logCoordinateSum (N : ℕ) :
    goldbachB9PairLogKernel N =
      ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), liuPairLogKernel N rs := by
  unfold goldbachB9PairLogKernel
  exact Finset.sum_congr rfl (fun _ hrs => goldbachB9PairLogKernelTerm_eq hrs)

theorem goldbachB9PairLogKernelTerm_nonneg
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    0 ≤ liuPairLogKernel N rs :=
  one_div_nonneg.mpr
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg rs.1) (Nat.cast_nonneg rs.2))
      (goldbachB9OneSubPrimeLogExponent_pos hN hrs).le)

theorem goldbachB9PairLogKernel_nonneg {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ goldbachB9PairLogKernel N := by
  rw [goldbachB9PairLogKernel_eq_logCoordinateSum]
  exact Finset.sum_nonneg (fun _ hrs => goldbachB9PairLogKernelTerm_nonneg hN hrs)

noncomputable def goldbachB9PairsInLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))).filter
    (LiuPairInLogRectangle N a₀ a₁ b₀ b₁)

noncomputable def goldbachB9PairLogKernelRectangleContribution
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : ℝ :=
  ∑ rs ∈ goldbachB9PairsInLogRectangle N a₀ a₁ b₀ b₁, liuPairLogKernel N rs

/-- Coprimality and source geometry are dropped only in this upper-bound inclusion. -/
theorem goldbachB9PairsInLogRectangle_subset_primeLogRectanglePairs
    {N : ℕ} (hN : 2 ≤ N) (a₀ a₁ b₀ b₁ : ℝ) :
    goldbachB9PairsInLogRectangle N a₀ a₁ b₀ b₁ ⊆
      primeLogRectanglePairs N a₀ a₁ b₀ b₁ := by
  intro rs hrs
  obtain ⟨hsource, hrect⟩ := Finset.mem_filter.mp hrs
  have h := mem_goldbachC10Pairs_iff.mp hsource
  have hrBounds := (primeLogExponent_mem_interval_iff
    (show 1 < N by omega) h.1.pos a₀ a₁).mp ⟨hrect.1, hrect.2.1⟩
  have hsBounds := (primeLogExponent_mem_interval_iff
    (show 1 < N by omega) h.2.1.pos b₀ b₁).mp ⟨hrect.2.2.1, hrect.2.2.2⟩
  rw [primeLogRectanglePairs, Finset.mem_product]
  constructor
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hrBounds.2)), h.1, hrBounds⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hsBounds.2)), h.2.1, hsBounds⟩

theorem goldbachB9PairLogKernelRectangleContribution_le
    (N : ℕ) (hN : 2 ≤ N) (a₀ a₁ b₀ b₁ : ℝ)
    (hupper : a₁ + b₁ < 1) :
    goldbachB9PairLogKernelRectangleContribution N a₀ a₁ b₀ b₁ ≤
      (1 / (1 - a₁ - b₁)) *
        primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ := by
  have hcorner : 0 ≤ 1 / (1 - a₁ - b₁) := one_div_nonneg.mpr (by linarith)
  unfold goldbachB9PairLogKernelRectangleContribution
  calc
    _ ≤ ∑ rs ∈ goldbachB9PairsInLogRectangle N a₀ a₁ b₀ b₁,
        (1 / (1 - a₁ - b₁)) * (1 / ((rs.1 : ℝ) * rs.2)) := by
      apply Finset.sum_le_sum
      intro rs hrs
      exact goldbachB8PairLogKernelTerm_le_rectangleCorner
        (Finset.mem_filter.mp hrs).2 hupper
    _ = (1 / (1 - a₁ - b₁)) *
        (∑ rs ∈ goldbachB9PairsInLogRectangle N a₀ a₁ b₀ b₁,
          1 / ((rs.1 : ℝ) * rs.2)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / (1 - a₁ - b₁)) *
        (∑ rs ∈ primeLogRectanglePairs N a₀ a₁ b₀ b₁,
          1 / ((rs.1 : ℝ) * rs.2)) := by
      apply mul_le_mul_of_nonneg_left _ hcorner
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (goldbachB9PairsInLogRectangle_subset_primeLogRectanglePairs hN a₀ a₁ b₀ b₁)
        (fun _ _ _ => by positivity)
    _ = _ := by rw [sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig