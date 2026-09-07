import MathlibNt.SieveTheory.LiLiuGoldbachB8MainMassTransport
import MathlibNt.SieveTheory.LiLiuGoldbachS4CarrierGeometry
import MathlibNt.SieveTheory.LiuPrimePairLogKernel

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Finset
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle PrimeReciprocalLogScale

noncomputable local instance instDecidablePropB8LogKernel (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def goldbachB8Gamma : ℝ := 3 / 11

/-- The closed logarithmic geometry of the actual S4 carrier, including the diagonal. -/
theorem goldbachB8Pair_logGeometry
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))) :
    goldbachB8Gamma ≤ primeLogExponent N rs.1 ∧
      primeLogExponent N rs.1 ≤ (1 / 3 : ℝ) ∧
      primeLogExponent N rs.1 ≤ primeLogExponent N rs.2 ∧
      primeLogExponent N rs.1 + 2 * primeLogExponent N rs.2 ≤ 1 := by
  obtain ⟨hr, hs, _, hcut, hrsle, hprod⟩ := mem_goldbachS4Pairs_iff.mp hrs
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hrp : (0 : ℝ) < rs.1 := by exact_mod_cast hr.pos
  have hsp : (0 : ℝ) < rs.2 := by exact_mod_cast hs.pos
  have hcutlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hcut
  rw [Real.log_rpow hNp] at hcutlog
  have hlow : goldbachB8Gamma ≤ primeLogExponent N rs.1 :=
    (le_div_iff₀ hln).mpr hcutlog
  have horder : primeLogExponent N rs.1 ≤ primeLogExponent N rs.2 :=
    div_le_div_of_nonneg_right
      (Real.log_le_log hrp (by exact_mod_cast hrsle)) hln.le
  have hprodR : (rs.1 : ℝ) * (rs.2 : ℝ) ^ 2 ≤ N := by exact_mod_cast hprod
  have hprodlog := Real.log_le_log (mul_pos hrp (pow_pos hsp 2)) hprodR
  rw [Real.log_mul hrp.ne' (pow_ne_zero 2 hsp.ne'), Real.log_pow] at hprodlog
  have htriangle : primeLogExponent N rs.1 + 2 * primeLogExponent N rs.2 ≤ 1 := by
    unfold primeLogExponent
    rw [show Real.log (rs.1 : ℝ) / Real.log (N : ℝ) +
        2 * (Real.log (rs.2 : ℝ) / Real.log (N : ℝ)) =
        (Real.log (rs.1 : ℝ) + 2 * Real.log (rs.2 : ℝ)) /
          Real.log (N : ℝ) by ring]
    exact (div_le_one hln).mpr (by simpa using hprodlog)
  exact ⟨hlow, by linarith, horder, htriangle⟩

theorem goldbachB8PrimeLogExponent_second_le_upper
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))) :
    primeLogExponent N rs.2 ≤ (4 / 11 : ℝ) := by
  obtain ⟨hlow, _, _, htriangle⟩ := goldbachB8Pair_logGeometry hN hrs
  dsimp [goldbachB8Gamma] at hlow
  linarith

theorem goldbachB8OneSubPrimeLogExponent_pos
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))) :
    0 < 1 - primeLogExponent N rs.1 - primeLogExponent N rs.2 := by
  have hfirst := (goldbachB8Pair_logGeometry hN hrs).2.1
  have hsecond := goldbachB8PrimeLogExponent_second_le_upper hN hrs
  linarith

theorem goldbachB8LogProd_eq
    {N : ℕ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))) :
    Real.log (goldbachC8Prod rs : ℝ) =
      Real.log (rs.1 : ℝ) + Real.log (rs.2 : ℝ) := by
  have h := mem_goldbachS4Pairs_iff.mp hrs
  have hrp : (0 : ℝ) < rs.1 := by exact_mod_cast h.1.pos
  have hsp : (0 : ℝ) < rs.2 := by exact_mod_cast h.2.1.pos
  simp only [goldbachC8Prod, Nat.cast_mul, Real.log_mul hrp.ne' hsp.ne']

/-- This is an identity on the actual carrier, not a replacement by all prime pairs. -/
theorem goldbachB8PairLogKernelTerm_eq
    {N : ℕ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))) :
    1 / ((goldbachC8Prod rs : ℝ) *
      (1 - Real.log (goldbachC8Prod rs : ℝ) / Real.log (N : ℝ))) =
        liuPairLogKernel N rs := by
  rw [goldbachB8LogProd_eq hrs]
  simp only [goldbachC8Prod, Nat.cast_mul, liuPairLogKernel, primeLogExponent,
    add_div, sub_sub]

theorem goldbachB8PairLogKernel_eq_logCoordinateSum (N : ℕ) :
    goldbachB8PairLogKernel N =
      ∑ rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ)), liuPairLogKernel N rs := by
  unfold goldbachB8PairLogKernel
  exact Finset.sum_congr rfl (fun _ hrs => goldbachB8PairLogKernelTerm_eq hrs)

theorem goldbachB8PairLogKernelTerm_nonneg
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))) :
    0 ≤ liuPairLogKernel N rs := by
  exact one_div_nonneg.mpr
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg rs.1) (Nat.cast_nonneg rs.2))
      (goldbachB8OneSubPrimeLogExponent_pos hN hrs).le)

noncomputable def goldbachB8PairsInLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachS4Pairs N ((N : ℝ) ^ (3 / 11 : ℝ))).filter
    (LiuPairInLogRectangle N a₀ a₁ b₀ b₁)

noncomputable def goldbachB8PairLogKernelRectangleContribution
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : ℝ :=
  ∑ rs ∈ goldbachB8PairsInLogRectangle N a₀ a₁ b₀ b₁, liuPairLogKernel N rs

/-- Only a subset inclusion: the target rectangle drops coprimality and source geometry. -/
theorem goldbachB8PairsInLogRectangle_subset_primeLogRectanglePairs
    {N : ℕ} (hN : 2 ≤ N) (a₀ a₁ b₀ b₁ : ℝ) :
    goldbachB8PairsInLogRectangle N a₀ a₁ b₀ b₁ ⊆
      primeLogRectanglePairs N a₀ a₁ b₀ b₁ := by
  intro rs hrs
  obtain ⟨hsource, hrect⟩ := Finset.mem_filter.mp hrs
  have h := mem_goldbachS4Pairs_iff.mp hsource
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

/-- The coordinate kernel is generic; no Liu or C10 carrier theorem is used here. -/
theorem goldbachB8PairLogKernelTerm_le_rectangleCorner
    {N : ℕ} {rs : ℕ × ℕ} {a₀ a₁ b₀ b₁ : ℝ}
    (hrect : LiuPairInLogRectangle N a₀ a₁ b₀ b₁ rs)
    (hupper : a₁ + b₁ < 1) :
    liuPairLogKernel N rs ≤
      (1 / (1 - a₁ - b₁)) * (1 / ((rs.1 : ℝ) * rs.2)) := by
  have hcorner : 0 < 1 - a₁ - b₁ := by linarith
  have hdenom : 1 - a₁ - b₁ ≤
      1 - primeLogExponent N rs.1 - primeLogExponent N rs.2 := by
    linarith [hrect.2.1, hrect.2.2.2]
  have hinv := one_div_le_one_div_of_le hcorner hdenom
  have hpair : 0 ≤ 1 / ((rs.1 : ℝ) * rs.2) := by positivity
  calc
    liuPairLogKernel N rs =
        (1 / ((rs.1 : ℝ) * rs.2)) *
          (1 / (1 - primeLogExponent N rs.1 - primeLogExponent N rs.2)) := by
      simp only [liuPairLogKernel, one_div, mul_inv]
    _ ≤ (1 / ((rs.1 : ℝ) * rs.2)) * (1 / (1 - a₁ - b₁)) :=
      mul_le_mul_of_nonneg_left hinv hpair
    _ = _ := mul_comm _ _

theorem goldbachB8PairLogKernelRectangleContribution_le
    (N : ℕ) (hN : 2 ≤ N) (a₀ a₁ b₀ b₁ : ℝ)
    (hupper : a₁ + b₁ < 1) :
    goldbachB8PairLogKernelRectangleContribution N a₀ a₁ b₀ b₁ ≤
      (1 / (1 - a₁ - b₁)) *
        primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ := by
  have hcorner : 0 ≤ 1 / (1 - a₁ - b₁) := one_div_nonneg.mpr (by linarith)
  unfold goldbachB8PairLogKernelRectangleContribution
  calc
    _ ≤ ∑ rs ∈ goldbachB8PairsInLogRectangle N a₀ a₁ b₀ b₁,
        (1 / (1 - a₁ - b₁)) * (1 / ((rs.1 : ℝ) * rs.2)) := by
      apply Finset.sum_le_sum
      intro rs hrs
      exact goldbachB8PairLogKernelTerm_le_rectangleCorner
        (Finset.mem_filter.mp hrs).2 hupper
    _ = (1 / (1 - a₁ - b₁)) *
        (∑ rs ∈ goldbachB8PairsInLogRectangle N a₀ a₁ b₀ b₁,
          1 / ((rs.1 : ℝ) * rs.2)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / (1 - a₁ - b₁)) *
        (∑ rs ∈ primeLogRectanglePairs N a₀ a₁ b₀ b₁,
          1 / ((rs.1 : ℝ) * rs.2)) := by
      apply mul_le_mul_of_nonneg_left _ hcorner
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (goldbachB8PairsInLogRectangle_subset_primeLogRectanglePairs hN a₀ a₁ b₀ b₁)
        (fun _ _ _ => by positivity)
    _ = _ := by rw [sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig