import MathlibNt.SieveTheory.LiLiuGoldbachG10Cofactor
import MathlibNt.SieveTheory.LiuPrimePairLogKernel

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Finset
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle PrimeReciprocalLogScale

/-- The fixed lower exponent `β = 4/33` from Liu's printed `I10`. -/
noncomputable def goldbachB10Beta : ℝ := 4 / 33

/-- The fixed upper/lower exponent `γ = 3/11` from Liu's printed `I10`. -/
noncomputable def goldbachB10Gamma : ℝ := 3 / 11

/-- The exact `C10` kernel rectangle predicate in logarithmic coordinates. -/
def goldbachB10PairInLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) (rs : ℕ × ℕ) : Prop :=
  a₀ < primeLogExponent N rs.1 ∧ primeLogExponent N rs.1 ≤ a₁ ∧
    b₀ < primeLogExponent N rs.2 ∧ primeLogExponent N rs.2 ≤ b₁

/-- The `C10` pairs whose logarithmic coordinates lie in one fixed rectangle. -/
noncomputable def goldbachB10PairsInLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)).filter
    (goldbachB10PairInLogRectangle N a₀ a₁ b₀ b₁)

/-- The exact logarithmic kernel on the actual ordered `C10` prime pairs. -/
noncomputable def goldbachB10PairLogKernel (N : ℕ) (rs : ℕ × ℕ) : ℝ :=
  1 / (((rs.1 : ℝ) * rs.2) *
    (1 - primeLogExponent N rs.1 - primeLogExponent N rs.2))

/-- The actual finite `C10` logarithmic-kernel sum corresponding to `I10`. -/
noncomputable def goldbachB10PairLogKernelSum (N : ℕ) : ℝ :=
  ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma),
    goldbachB10PairLogKernel N rs

/-- The contribution from the actual `C10` pairs lying in one fixed exponent
rectangle. -/
noncomputable def goldbachB10PairLogKernelRectangleContribution
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : ℝ :=
  ∑ rs ∈ goldbachB10PairsInLogRectangle N a₀ a₁ b₀ b₁,
    goldbachB10PairLogKernel N rs

private lemma goldbachB10Beta_gt_one_tenth : (1 / 10 : ℝ) < goldbachB10Beta := by
  dsimp [goldbachB10Beta]
  norm_num

private lemma goldbachB10Gamma_gt_one_fourth : (1 / 4 : ℝ) < goldbachB10Gamma := by
  dsimp [goldbachB10Gamma]
  norm_num

private lemma goldbachB10Beta_pos : 0 < goldbachB10Beta := by
  dsimp [goldbachB10Beta]
  norm_num

private lemma goldbachB10Gamma_pos : 0 < goldbachB10Gamma := by
  dsimp [goldbachB10Gamma]
  norm_num

private lemma goldbachB10Beta_lt_gamma : goldbachB10Beta < goldbachB10Gamma := by
  dsimp [goldbachB10Beta, goldbachB10Gamma]
  norm_num

private lemma goldbachB10Gamma_lt_one : goldbachB10Gamma < 1 := by
  dsimp [goldbachB10Gamma]
  norm_num

private lemma goldbachB10SecondUpper_eq : (1 - goldbachB10Beta) / 2 = (29 / 66 : ℝ) := by
  dsimp [goldbachB10Beta]
  ring

/-- The actual `C10` product condition becomes `α + 2β ≤ 1` in logarithmic
coordinates. -/
theorem goldbachB10PrimeLogExponent_add_two_mul_le_one
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    primeLogExponent N rs.1 + 2 * primeLogExponent N rs.2 ≤ 1 := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, hprod⟩
  have hrpos : (0 : ℝ) < rs.1 := by exact_mod_cast hrPrime.pos
  have hspos : (0 : ℝ) < rs.2 := by exact_mod_cast hsPrime.pos
  have hprodR : (rs.1 : ℝ) * (rs.2 : ℝ) ^ 2 ≤ N := by exact_mod_cast hprod
  have hlog :
      Real.log ((rs.1 : ℝ) * (rs.2 : ℝ) ^ 2) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (mul_pos hrpos (pow_pos hspos 2)) hprodR
  rw [Real.log_mul (ne_of_gt hrpos) (pow_ne_zero 2 (ne_of_gt hspos)),
    Real.log_pow] at hlog
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold primeLogExponent
  calc
    Real.log ↑rs.1 / Real.log ↑N + 2 * (Real.log ↑rs.2 / Real.log ↑N) =
        (Real.log ↑rs.1 + 2 * Real.log ↑rs.2) / Real.log ↑N := by ring
    _ ≤ 1 := (div_le_one hlogN).mpr (by
      norm_num at hlog ⊢
      exact hlog)

theorem goldbachB10PrimeLogExponent_ge_beta
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    goldbachB10Beta ≤ primeLogExponent N rs.1 := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, _, _, hbr, _, _, _⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrpos : (0 : ℝ) < rs.1 := by exact_mod_cast hrPrime.pos
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog : Real.log ((N : ℝ) ^ goldbachB10Beta) ≤ Real.log rs.1 :=
    Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hbr
  rw [Real.log_rpow hNpos] at hlog
  unfold primeLogExponent
  exact (le_div_iff₀ hlogN).2 hlog

theorem goldbachB10PrimeLogExponent_le_gamma
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    primeLogExponent N rs.1 ≤ goldbachB10Gamma := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, _, _, _, hrc, _, _⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrpos : (0 : ℝ) < rs.1 := by exact_mod_cast hrPrime.pos
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog : Real.log rs.1 ≤ Real.log ((N : ℝ) ^ goldbachB10Gamma) :=
    Real.log_le_log hrpos hrc
  rw [Real.log_rpow hNpos] at hlog
  unfold primeLogExponent
  exact (div_le_iff₀ hlogN).2 hlog

theorem goldbachB10PrimeLogExponent_second_pos
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    0 < primeLogExponent N rs.2 := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, hsPrime, _, _, _, _, _⟩
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsone : (1 : ℝ) < rs.2 := by exact_mod_cast hsPrime.one_lt
  unfold primeLogExponent
  exact div_pos (Real.log_pos hsone) hlogN

theorem goldbachB10PrimeLogExponent_second_le_upper
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    primeLogExponent N rs.2 ≤ (29 / 66 : ℝ) := by
  have hsum := goldbachB10PrimeLogExponent_add_two_mul_le_one hN hrs
  have hbeta := goldbachB10PrimeLogExponent_ge_beta hN hrs
  rw [← goldbachB10SecondUpper_eq]
  linarith

/-- The remaining kernel denominator is strictly positive on the actual `C10`
carrier. -/
theorem goldbachB10OneSubPrimeLogExponent_pos
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    0 < 1 - primeLogExponent N rs.1 - primeLogExponent N rs.2 := by
  have hsum := goldbachB10PrimeLogExponent_add_two_mul_le_one hN hrs
  have hspos := goldbachB10PrimeLogExponent_second_pos hN hrs
  linarith

private theorem goldbachB10PairLogKernel_nonneg
    {N : ℕ} (hN : 2 ≤ N) {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma)) :
    0 ≤ goldbachB10PairLogKernel N rs := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, _⟩
  have hprod : 0 ≤ ((rs.1 : ℝ) * rs.2) := by
    exact mul_nonneg (Nat.cast_nonneg rs.1) (Nat.cast_nonneg rs.2)
  have hden : 0 ≤ 1 - primeLogExponent N rs.1 - primeLogExponent N rs.2 :=
    (goldbachB10OneSubPrimeLogExponent_pos hN hrs).le
  unfold goldbachB10PairLogKernel
  exact one_div_nonneg.mpr (mul_nonneg hprod hden)

private theorem goldbachB10PairsInLogRectangle_subset_primeLogRectanglePairs
    {N : ℕ} (hN : 2 ≤ N) (a₀ a₁ b₀ b₁ : ℝ) :
    goldbachB10PairsInLogRectangle N a₀ a₁ b₀ b₁ ⊆
      primeLogRectanglePairs N a₀ a₁ b₀ b₁ := by
  classical
  intro rs hrs
  rw [goldbachB10PairsInLogRectangle, Finset.mem_filter] at hrs
  rcases mem_goldbachC10Pairs_iff.mp hrs.1 with ⟨hrPrime, hsPrime, _, _, _, _, _⟩
  have hrBounds := (primeLogExponent_mem_interval_iff
    (show 1 < N by omega) hrPrime.pos a₀ a₁).mp ⟨hrs.2.1, hrs.2.2.1⟩
  have hsBounds := (primeLogExponent_mem_interval_iff
    (show 1 < N by omega) hsPrime.pos b₀ b₁).mp ⟨hrs.2.2.2.1, hrs.2.2.2.2⟩
  rw [primeLogRectanglePairs, Finset.mem_product]
  constructor
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hrBounds.2)),
      hrPrime, hrBounds⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hsBounds.2)),
      hsPrime, hsBounds⟩

private theorem goldbachB10PairLogKernel_le_rectangleCorner
    {N : ℕ} {rs : ℕ × ℕ}
    (_hrs : rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma))
    {a₀ a₁ b₀ b₁ : ℝ}
    (hrect : goldbachB10PairInLogRectangle N a₀ a₁ b₀ b₁ rs)
    (hupper : a₁ + b₁ < 1) :
    goldbachB10PairLogKernel N rs ≤
      (1 / (1 - a₁ - b₁)) * (1 / ((rs.1 : ℝ) * rs.2)) := by
  have hcorner : 0 < 1 - a₁ - b₁ := by linarith
  have hdenom :
      1 - a₁ - b₁ ≤
        1 - primeLogExponent N rs.1 - primeLogExponent N rs.2 := by
    linarith [hrect.2.1, hrect.2.2.2]
  have hinv :
      1 / (1 - primeLogExponent N rs.1 - primeLogExponent N rs.2) ≤
        1 / (1 - a₁ - b₁) :=
    one_div_le_one_div_of_le hcorner hdenom
  have hpair : 0 ≤ 1 / ((rs.1 : ℝ) * rs.2) := by
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg rs.1) (Nat.cast_nonneg rs.2))
  unfold goldbachB10PairLogKernel
  calc
    1 / (((rs.1 : ℝ) * rs.2) *
        (1 - primeLogExponent N rs.1 - primeLogExponent N rs.2)) =
        (1 / ((rs.1 : ℝ) * rs.2)) *
          (1 / (1 - primeLogExponent N rs.1 - primeLogExponent N rs.2)) := by
            simp only [one_div, mul_inv]
    _ ≤ (1 / ((rs.1 : ℝ) * rs.2)) * (1 / (1 - a₁ - b₁)) :=
      mul_le_mul_of_nonneg_left hinv hpair
    _ = (1 / (1 - a₁ - b₁)) * (1 / ((rs.1 : ℝ) * rs.2)) := by ring

private theorem goldbachB10PairLogKernelRectangleContribution_le
    (N : ℕ) (hN : 2 ≤ N) (a₀ a₁ b₀ b₁ : ℝ)
    (hupper : a₁ + b₁ < 1) :
    goldbachB10PairLogKernelRectangleContribution N a₀ a₁ b₀ b₁ ≤
      (1 / (1 - a₁ - b₁)) *
        primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ := by
  have hcorner : 0 ≤ 1 / (1 - a₁ - b₁) := by
    exact one_div_nonneg.mpr (by linarith)
  have hsubset :=
    goldbachB10PairsInLogRectangle_subset_primeLogRectanglePairs hN a₀ a₁ b₀ b₁
  unfold goldbachB10PairLogKernelRectangleContribution
  calc
    (∑ rs ∈ goldbachB10PairsInLogRectangle N a₀ a₁ b₀ b₁,
        goldbachB10PairLogKernel N rs) ≤
        ∑ rs ∈ goldbachB10PairsInLogRectangle N a₀ a₁ b₀ b₁,
          (1 / (1 - a₁ - b₁)) * (1 / ((rs.1 : ℝ) * rs.2)) := by
      apply Finset.sum_le_sum
      intro rs hrs
      have hmem :
          rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) ∧
            goldbachB10PairInLogRectangle N a₀ a₁ b₀ b₁ rs := by
        simpa [goldbachB10PairsInLogRectangle] using hrs
      exact goldbachB10PairLogKernel_le_rectangleCorner hmem.1 hmem.2 hupper
    _ = (1 / (1 - a₁ - b₁)) *
        (∑ rs ∈ goldbachB10PairsInLogRectangle N a₀ a₁ b₀ b₁,
          1 / ((rs.1 : ℝ) * rs.2)) := by
            rw [Finset.mul_sum]
    _ ≤ (1 / (1 - a₁ - b₁)) *
        (∑ rs ∈ primeLogRectanglePairs N a₀ a₁ b₀ b₁,
          1 / ((rs.1 : ℝ) * rs.2)) := by
      apply mul_le_mul_of_nonneg_left _ hcorner
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro rs hrs _
      rw [primeLogRectanglePairs, Finset.mem_product] at hrs
      exact one_div_nonneg.mpr
        (mul_nonneg (Nat.cast_nonneg rs.1) (Nat.cast_nonneg rs.2))
    _ = (1 / (1 - a₁ - b₁)) * primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ := by
      rw [sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle]

/-- A finite family of fixed positive rectangles may overlap: if it covers
every actual `C10` pair and stays below `u + v = 1`, then the full `C10`
logarithmic-kernel sum is bounded by the sum of the rectangle majorants. -/
theorem goldbachB10PairLogKernelSum_le_sum_rectangleMajorants_of_cover
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a₀ a₁ b₀ b₁ : ι → ℝ) (N : ℕ) (hN : 2 ≤ N)
    (_ha₀ : ∀ i ∈ s, 0 < a₀ i) (_ha : ∀ i ∈ s, a₀ i < a₁ i)
    (_hb₀ : ∀ i ∈ s, 0 < b₀ i) (_hb : ∀ i ∈ s, b₀ i < b₁ i)
    (hupper : ∀ i ∈ s, a₁ i + b₁ i < 1)
    (hcover : ∀ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma),
      ∃ i ∈ s, goldbachB10PairInLogRectangle N (a₀ i) (a₁ i) (b₀ i) (b₁ i) rs) :
    goldbachB10PairLogKernelSum N ≤
      ∑ i ∈ s, (1 / (1 - a₁ i - b₁ i)) *
        primeReciprocalLogRectangle N (a₀ i) (a₁ i) (b₀ i) (b₁ i) := by
  classical
  have hcoverSum :
      goldbachB10PairLogKernelSum N ≤
        ∑ i ∈ s, goldbachB10PairLogKernelRectangleContribution
          N (a₀ i) (a₁ i) (b₀ i) (b₁ i) := by
    unfold goldbachB10PairLogKernelSum
    calc
      (∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma),
          goldbachB10PairLogKernel N rs) ≤
          ∑ rs ∈ goldbachC10Pairs N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma),
            ∑ i ∈ s, if goldbachB10PairInLogRectangle
                N (a₀ i) (a₁ i) (b₀ i) (b₁ i) rs then
              goldbachB10PairLogKernel N rs else 0 := by
        apply Finset.sum_le_sum
        intro rs hrs
        obtain ⟨i, hi, hirs⟩ := hcover rs hrs
        have hsingle : ({i} : Finset ι) ⊆ s := by simpa using hi
        have hle :
            (∑ j ∈ ({i} : Finset ι), if goldbachB10PairInLogRectangle
                N (a₀ j) (a₁ j) (b₀ j) (b₁ j) rs then
              goldbachB10PairLogKernel N rs else 0) ≤
              ∑ j ∈ s, if goldbachB10PairInLogRectangle
                  N (a₀ j) (a₁ j) (b₀ j) (b₁ j) rs then
                goldbachB10PairLogKernel N rs else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsingle (fun j hj _ => by
            split_ifs
            · exact goldbachB10PairLogKernel_nonneg hN hrs
            · exact le_rfl)
        simpa [hirs] using hle
      _ = ∑ i ∈ s, goldbachB10PairLogKernelRectangleContribution
          N (a₀ i) (a₁ i) (b₀ i) (b₁ i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        unfold goldbachB10PairLogKernelRectangleContribution
          goldbachB10PairsInLogRectangle
        rw [Finset.sum_filter]
  exact hcoverSum.trans (Finset.sum_le_sum fun i hi =>
    goldbachB10PairLogKernelRectangleContribution_le N hN
      (a₀ i) (a₁ i) (b₀ i) (b₁ i) (hupper i hi))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig