import MathlibNt.SieveTheory.Liu.LogarithmicIntegral.LiuTrueLiPanSigned

/-!
# Exact split of Liu's signed Pan residual

This module separates the existing signed residual into its two exact analytic
inputs. The signed-main absolute value remains outside the complete
source-faithful combination; it is not split termwise. The second input retains
the AP prime-power correction, the exact source weight, both maxima, and the
original modulus weight and cutoff.

For the full Pan family these inputs are required for every fixed `A > 0`.
For the final M1 use, it is enough analytically to obtain a residual
`o(N / log(N)^2)` or `O(N / log(N)^(2 + delta))`; no existing contract is
changed here.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve

/-- The maximum over coprime residues of the absolute value of the complete
source-faithful signed-main sum. The absolute value is not distributed across
the terms of `liuPanSignedMainKernel`. -/
noncomputable def liuPanSignedMainMaxL
    (distMain : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |liuPanSignedMainSum distMain y X q l f u v|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

/-- The maximum of the complete signed-main residue maximum over `y ≤ x`. -/
noncomputable def liuPanSignedMainMaxY
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanSignedMainMaxL distMain y X q f u v)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The maximum over coprime residues of the exact AP prime-power correction
with the source weight retained inside `liuPanSignedCorrectionBound`. -/
noncomputable def liuPanAPPrimePowerCorrectionMaxL
    (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => liuPanSignedCorrectionBound y X q l f)).max'
      (Finset.image_nonempty.mpr h)
  else 0

/-- The maximum of the AP prime-power correction over `y ≤ x`. -/
noncomputable def liuPanAPPrimePowerCorrectionMaxY
    (X q x : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanAPPrimePowerCorrectionMaxL y X q f)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

private noncomputable def liuPanSignedCombinedMaxL
    (distMain : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |liuPanSignedMainSum distMain y X q l f u v| +
      liuPanSignedCorrectionBound y X q l f)).max'
      (Finset.image_nonempty.mpr h)
  else 0

private noncomputable def liuPanSignedCombinedMaxY
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanSignedCombinedMaxL distMain y X q f u v)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

private theorem liuPanSignedResidualMaxY_eq_combined
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanSignedResidualMaxY distMain X q x f u v =
      liuPanSignedCombinedMaxY distMain X q x f u v := by
  rfl

/-- The complete signed-main residue maximum is nonnegative. -/
theorem liuPanSignedMainMaxL_nonneg
    (distMain : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ liuPanSignedMainMaxL distMain y X q f u v := by
  unfold liuPanSignedMainMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · rw [dif_pos hS]
    rcases hS with ⟨l, hl⟩
    refine (abs_nonneg (liuPanSignedMainSum distMain y X q l f u v)).trans
      (Finset.le_max' _ _ ?_)
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  · simp [hS]

/-- The complete signed-main `y`-maximum is nonnegative. -/
theorem liuPanSignedMainMaxY_nonneg
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ liuPanSignedMainMaxY distMain X q x f u v := by
  unfold liuPanSignedMainMaxY
  refine (liuPanSignedMainMaxL_nonneg distMain 0 X q f u v).trans
    (Finset.le_max' _ _ ?_)
  exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩

/-- The AP prime-power residue maximum is nonnegative. -/
theorem liuPanAPPrimePowerCorrectionMaxL_nonneg
    (y X q : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuPanAPPrimePowerCorrectionMaxL y X q f := by
  unfold liuPanAPPrimePowerCorrectionMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · rw [dif_pos hS]
    rcases hS with ⟨l, hl⟩
    refine (liuPanSignedCorrectionBound_nonneg y X q l f).trans
      (Finset.le_max' _ _ ?_)
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  · simp [hS]

/-- The AP prime-power `y`-maximum is nonnegative. -/
theorem liuPanAPPrimePowerCorrectionMaxY_nonneg
    (X q x : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuPanAPPrimePowerCorrectionMaxY X q x f := by
  unfold liuPanAPPrimePowerCorrectionMaxY
  refine (liuPanAPPrimePowerCorrectionMaxL_nonneg 0 X q f).trans
    (Finset.le_max' _ _ ?_)
  exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩

private theorem liuPanSignedCombinedMaxL_le
    (distMain : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanSignedCombinedMaxL distMain y X q f u v ≤
      liuPanSignedMainMaxL distMain y X q f u v +
        liuPanAPPrimePowerCorrectionMaxL y X q f := by
  unfold liuPanSignedCombinedMaxL liuPanSignedMainMaxL
    liuPanAPPrimePowerCorrectionMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · simp only [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hmain := Finset.le_max'
      ((unitResidues q).image (fun l =>
        |liuPanSignedMainSum distMain y X q l f u v|))
      |liuPanSignedMainSum distMain y X q l f u v|
      (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have hpp := Finset.le_max'
      ((unitResidues q).image (fun l =>
        liuPanSignedCorrectionBound y X q l f))
      (liuPanSignedCorrectionBound y X q l f)
      (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    exact add_le_add hmain hpp
  · simp [hS]

/-- The audited residual maximum is bounded by the sum of its two exact
component maxima. Only the two finite maxima are split; the signed-main
absolute value remains intact. -/
theorem liuPanSignedResidualMaxY_le_split
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanSignedResidualMaxY distMain X q x f u v ≤
      liuPanSignedMainMaxY distMain X q x f u v +
        liuPanAPPrimePowerCorrectionMaxY X q x f := by
  rw [liuPanSignedResidualMaxY_eq_combined]
  unfold liuPanSignedCombinedMaxY liuPanSignedMainMaxY
    liuPanAPPrimePowerCorrectionMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hpoint := liuPanSignedCombinedMaxL_le distMain y X q f u v
  have hmain := Finset.le_max'
    ((range (x + 1)).image (fun y =>
      liuPanSignedMainMaxL distMain y X q f u v))
    (liuPanSignedMainMaxL distMain y X q f u v)
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have hpp := Finset.le_max'
    ((range (x + 1)).image (fun y =>
      liuPanAPPrimePowerCorrectionMaxL y X q f))
    (liuPanAPPrimePowerCorrectionMaxL y X q f)
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  exact hpoint.trans (add_le_add hmain hpp)

/-- Fixed-`N` bound for the complete signed-main average. This retains one
absolute value around the entire source-faithful signed sum. -/
def LiuMainPanSignedMainBoundAt
    (distMain : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ)
    (A B Cmain : ℝ) (u v : ℕ) : Prop :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanSignedMainMaxY distMain N q N f u v ≤
    Cmain * N / Real.log N ^ A

/-- Fixed-`N` bound for the AP prime-power correction average, with the exact
source weight, modulus cutoff, arithmetic weight, and both maxima retained. -/
def LiuMainPanAPPrimePowerCorrectionBoundAt
    (N : ℕ) (f : ℕ → ℝ) (A B Cpp : ℝ) : Prop :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanAPPrimePowerCorrectionMaxY N q N f ≤
    Cpp * N / Real.log N ^ A

/-- The complete signed-main weighted average is nonnegative. -/
theorem liuMainPanSignedMain_average_nonneg
    (distMain : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ) (B : ℝ) (u v : ℕ) :
    0 ≤ ∑ q ∈ range (panModulusCutoff N B + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
        liuPanSignedMainMaxY distMain N q N f u v := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (panTypeI_weight_nonneg q)
    (liuPanSignedMainMaxY_nonneg distMain N q N f u v)

/-- The AP prime-power correction weighted average is nonnegative. -/
theorem liuMainPanAPPrimePowerCorrection_average_nonneg
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) :
    0 ≤ ∑ q ∈ range (panModulusCutoff N B + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
        liuPanAPPrimePowerCorrectionMaxY N q N f := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (panTypeI_weight_nonneg q)
    (liuPanAPPrimePowerCorrectionMaxY_nonneg N q N f)

/-- The two exact fixed-`N` component bounds imply the existing signed residual
bound with the sum of constants and unchanged parameters and cutoff. -/
theorem LiuMainPanSignedResidualBoundAt.of_splitBoundsAt
    {distMain : ℝ → ℝ} {N : ℕ} {f : ℕ → ℝ}
    {A B Cmain Cpp : ℝ} {u v : ℕ}
    (hmain : LiuMainPanSignedMainBoundAt distMain N f A B Cmain u v)
    (hpp : LiuMainPanAPPrimePowerCorrectionBoundAt N f A B Cpp) :
    LiuMainPanSignedResidualBoundAt distMain N f A B (Cmain + Cpp) u v := by
  unfold LiuMainPanSignedMainBoundAt at hmain
  unfold LiuMainPanAPPrimePowerCorrectionBoundAt at hpp
  unfold LiuMainPanSignedResidualBoundAt
  let w : ℕ → ℝ := fun q =>
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card
  let main : ℕ → ℝ := fun q =>
    liuPanSignedMainMaxY distMain N q N f u v
  let pp : ℕ → ℝ := fun q =>
    liuPanAPPrimePowerCorrectionMaxY N q N f
  let residual : ℕ → ℝ := fun q =>
    liuPanSignedResidualMaxY distMain N q N f u v
  change (∑ q ∈ range (panModulusCutoff N B + 1), w q * main q) ≤
    Cmain * N / Real.log N ^ A at hmain
  change (∑ q ∈ range (panModulusCutoff N B + 1), w q * pp q) ≤
    Cpp * N / Real.log N ^ A at hpp
  change (∑ q ∈ range (panModulusCutoff N B + 1), w q * residual q) ≤
    (Cmain + Cpp) * N / Real.log N ^ A
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1), w q * residual q) ≤
        ∑ q ∈ range (panModulusCutoff N B + 1),
          w q * (main q + pp q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (liuPanSignedResidualMaxY_le_split distMain N q N f u v)
        (panTypeI_weight_nonneg q)
    _ = (∑ q ∈ range (panModulusCutoff N B + 1), w q * main q) +
          ∑ q ∈ range (panModulusCutoff N B + 1), w q * pp q := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ Cmain * N / Real.log N ^ A + Cpp * N / Real.log N ^ A :=
      add_le_add hmain hpp
    _ = (Cmain + Cpp) * N / Real.log N ^ A := by ring

/-- Eventual source-family packaging of the two fixed-`N` components. The
parameters `A`, `B`, `Cmain`, `Cpp`, `u`, and `v` are fixed before `N → ∞`. -/
def LiuMainPanSignedResidualSplitSourceFamilyInputs
    (distMain : ℝ → ℝ) (A B Cmain Cpp : ℝ) (u v : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    LiuMainPanSignedMainBoundAt distMain N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B Cmain u v ∧
    LiuMainPanAPPrimePowerCorrectionBoundAt N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B Cpp

/-- Eventual component bounds, each quantified after all analytic parameters,
give the eventual existing residual bound. -/
theorem eventually_liuMainPanSignedResidualBoundAt_of_splitBoundsAt
    {distMain : ℝ → ℝ} {A B Cmain Cpp : ℝ} {u v : ℕ}
    (hmain : ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedMainBoundAt distMain N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B Cmain u v)
    (hpp : ∀ᶠ N : ℕ in atTop,
      LiuMainPanAPPrimePowerCorrectionBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B Cpp) :
    ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt distMain N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
        A B (Cmain + Cpp) u v := by
  filter_upwards [hmain, hpp] with N hmainN hppN
  exact LiuMainPanSignedResidualBoundAt.of_splitBoundsAt hmainN hppN

/-- The packaged split source-family input implies the existing eventual
residual input with constants added. -/
theorem LiuMainPanSignedResidualSplitSourceFamilyInputs.signedResidual
    {distMain : ℝ → ℝ} {A B Cmain Cpp : ℝ} {u v : ℕ}
    (h : LiuMainPanSignedResidualSplitSourceFamilyInputs
      distMain A B Cmain Cpp u v) :
    ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt distMain N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
        A B (Cmain + Cpp) u v := by
  filter_upwards [h] with N hN
  exact LiuMainPanSignedResidualBoundAt.of_splitBoundsAt hN.1 hN.2

end MathlibNt.SieveTheory.LiuWeight
