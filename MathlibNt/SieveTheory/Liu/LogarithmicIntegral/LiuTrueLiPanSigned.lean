import MathlibNt.SieveTheory.Liu.LogarithmicIntegral.LiuTrueLiPan

/-!
# Source-faithful signed Pan assembly for arbitrary distribution mains

This is the finite Vaughan/Chebyshev decomposition used by the Liu `eqn-r`
lane, with the distribution main left as an explicit parameter.  In
particular, the genuine logarithmic integral is never identified with ANT's
historical `x / log x` compatibility function.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve

/-! ## Exact signed kernels -/

/-- The exact source-faithful signed residual after the aggregate Type I and
Type II kernels have been removed. -/
noncomputable def liuPanSignedMainKernel
    (distMain : ℝ → ℝ) (y a q l u v : ℕ) : ℝ :=
  let ya := y / a
  let la := natInvMod q a * l % q
  (apV1Log ya q la u - apV1 ya q la u / Real.log (ya : ℝ)) +
    (apV3Log ya q la u v - apV3 ya q la u v / Real.log (ya : ℝ)) -
    apMiddleLog ya q la u v + apSmallLog ya q la v -
    distMain ((y : ℝ) / a) / Nat.totient q

/-- The prime-power correction in the exact `ψ / log` to `π` conversion. -/
noncomputable def liuPanSignedCorrectionKernel (y a q l : ℕ) : ℝ :=
  apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)

/-- Coprime signed main residual.  The coprimality condition is deliberately
displayed here rather than hidden in the kernel. -/
noncomputable def liuPanSignedMainSum
    (distMain : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, if a.Coprime q then
    f a * liuPanSignedMainKernel distMain y a q l u v else 0

/-- Coprime signed prime-power correction. -/
noncomputable def liuPanSignedCorrectionSum
    (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 X, if a.Coprime q then
    f a * liuPanSignedCorrectionKernel y a q l else 0

/-- Nonnegative termwise majorant for the prime-power correction. -/
noncomputable def liuPanSignedCorrectionBound
    (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 X, if a.Coprime q then
    |f a| * liuPanSignedCorrectionKernel y a q l else 0

theorem liuPanSignedCorrectionBound_nonneg
    (y X q l : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuPanSignedCorrectionBound y X q l f := by
  unfold liuPanSignedCorrectionBound
  apply Finset.sum_nonneg
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop]
    exact mul_nonneg (abs_nonneg _) (apPrimePowerCorrection_nonneg _ _ _)
  · simp [hcop]

private theorem liu_sum_range_eq_Icc
    (X : ℕ) (g : ℕ → ℝ) (hg : g 0 = 0) :
    (∑ a ∈ range (X + 1), g a) = ∑ a ∈ Icc 1 X, g a := by
  have hset : range (X + 1) = insert 0 (Icc 1 X) := by
    ext a
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert]
  · simp [hg]
  · simp

/-- Exact finite identity for the arbitrary-main coprime Pan sum.  It is
constructed from the live Vaughan and Chebyshev identities, not an assumed
pointwise split. -/
theorem liuMainPanCoprimeSum_eq_sourceFaithfulSigned
    (distMain : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    liuMainPanCoprimeSum distMain y X q l f =
      panPieceSum y X q l f
          (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
        panPieceSum y X q l f
          (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
        liuPanSignedMainSum distMain y X q l f u v -
        liuPanSignedCorrectionSum y X q l f := by
  let delta : ℕ → ℝ := fun a =>
    if a.Coprime q then
      f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q -
        distMain ((y : ℝ) / a) / Nat.totient q)
    else 0
  have hdelta0 : delta 0 = 0 := by simp [delta, hf0]
  have hdiff :
      liuMainPanCoprimeSum distMain y X q l f =
        panDistributionSum y X q l f + ∑ a ∈ Icc 1 X, delta a := by
    unfold liuMainPanCoprimeSum panDistributionSum liuScaledAPError
      panDistributionError
    rw [liu_sum_range_eq_Icc X _ (by simp [hf0]),
      liu_sum_range_eq_Icc X _ (by simp [hf0]), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      simp only [delta, if_pos hcop]
      ring
    · simp only [if_neg hcop]
      simp only [delta, if_neg hcop]
      simp
  have hproxy :
      panDistributionSum y X q l f =
        panPieceSum y X q l f
            (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
          panPieceSum y X q l f
            (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
          panSignedMainSum y X q l f u v -
          panSignedCorrectionSum y X q l f := by
    rw [panDistributionSum_eq_mainStep y X q l f hf0]
    unfold panPieceSum panSignedMainSum panSignedCorrectionSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      rw [apLogVonMangoldt_eq_logPieces]
      simp only [panSignedMainKernel, panSignedCorrectionKernel]
      ring
    · simp [hcop]
  have hmain :
      liuPanSignedMainSum distMain y X q l f u v =
        panSignedMainSum y X q l f u v + ∑ a ∈ Icc 1 X, delta a := by
    unfold liuPanSignedMainSum panSignedMainSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      simp only [delta, if_pos hcop, liuPanSignedMainKernel,
        panSignedMainKernel]
      ring
    · simp only [if_neg hcop]
      simp only [delta, if_neg hcop]
      simp
  have hcorr :
      liuPanSignedCorrectionSum y X q l f =
        panSignedCorrectionSum y X q l f := rfl
  rw [hdiff, hproxy, hcorr]
  linarith [hmain]

theorem abs_liuPanSignedCorrectionSum_le
    (y X q l : ℕ) (f : ℕ → ℝ) :
    |liuPanSignedCorrectionSum y X q l f| ≤
      liuPanSignedCorrectionBound y X q l f := by
  unfold liuPanSignedCorrectionSum liuPanSignedCorrectionBound
  calc
    |∑ a ∈ Icc 1 X, (if a.Coprime q then
        f a * liuPanSignedCorrectionKernel y a q l else 0)| ≤
        ∑ a ∈ Icc 1 X, |if a.Coprime q then
          f a * liuPanSignedCorrectionKernel y a q l else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 X, (if a.Coprime q then
          |f a| * liuPanSignedCorrectionKernel y a q l else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop, abs_mul]
        have hk : 0 ≤ liuPanSignedCorrectionKernel y a q l :=
          apPrimePowerCorrection_nonneg _ _ _
        rw [abs_of_nonneg hk]
      · simp [hcop]

/-- Pointwise absolute-value form of the exact arbitrary-main decomposition. -/
theorem abs_liuMainPanCoprimeSum_le_sourceFaithfulSigned
    (distMain : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    |liuMainPanCoprimeSum distMain y X q l f| ≤
      |panPieceSum y X q l f
          (fun y q l => apV1 y q l u / Real.log (y : ℝ))| +
        |panPieceSum y X q l f
          (fun y q l => apV3 y q l u v / Real.log (y : ℝ))| +
        (|liuPanSignedMainSum distMain y X q l f u v| +
          liuPanSignedCorrectionBound y X q l f) := by
  rw [liuMainPanCoprimeSum_eq_sourceFaithfulSigned distMain y X q l f u v hf0]
  have htri : ∀ a b c d : ℝ,
      |a + b + c - d| ≤ |a| + |b| + (|c| + |d|) := by
    intro a b c d
    calc
      |a + b + c - d| ≤ |a + b| + |c - d| := by
        have heq : a + b + c - d = (a + b) + (c - d) := by ring
        rw [heq]
        exact abs_add_le _ _
      _ ≤ (|a| + |b|) + (|c| + |d|) := by
        gcongr
        · exact abs_add_le _ _
        · simpa [sub_eq_add_neg, abs_neg] using abs_add_le c (-d)
      _ = |a| + |b| + (|c| + |d|) := by ring
  exact (htri _ _ _ _).trans (by
    gcongr
    exact abs_liuPanSignedCorrectionSum_le y X q l f)

/-! ## Canonical residue and source-parameter maxima -/

private noncomputable def liuPanScoreMaxL
    (q : ℕ) (score : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image score).max' (Finset.image_nonempty.mpr h)
  else 0

private noncomputable def liuPanScoreMaxY
    (q x : ℕ) (score : ℕ → ℕ → ℝ) : ℝ :=
  ((range (x + 1)).image (fun y => liuPanScoreMaxL q (score y))).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

@[simp] private theorem liuPanScoreMaxL_one (score : ℕ → ℝ) :
    liuPanScoreMaxL 1 score = score 0 := by
  simp [liuPanScoreMaxL]

private theorem liuPanScoreMaxL_nonneg
    (q : ℕ) (score : ℕ → ℝ) (hscore : ∀ l, 0 ≤ score l) :
    0 ≤ liuPanScoreMaxL q score := by
  unfold liuPanScoreMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · rw [dif_pos hS]
    rcases hS with ⟨l, hl⟩
    exact (hscore l).trans
      (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩))
  · simp [hS]

private theorem liuPanScoreMaxY_nonneg
    (q x : ℕ) (score : ℕ → ℕ → ℝ)
    (hscore : ∀ y l, 0 ≤ score y l) :
    0 ≤ liuPanScoreMaxY q x score := by
  unfold liuPanScoreMaxY
  have hzero : 0 ∈ range (x + 1) := by simp
  exact (liuPanScoreMaxL_nonneg q (score 0) (hscore 0)).trans
    (Finset.le_max'
      ((range (x + 1)).image (fun y => liuPanScoreMaxL q (score y)))
      (liuPanScoreMaxL q (score 0))
      (Finset.mem_image.mpr ⟨0, hzero, rfl⟩))

/-- The double maximum of the concrete signed residual and its separate
prime-power correction.  For `q = 1`, its canonical residue is `0`. -/
noncomputable def liuPanSignedResidualMaxY
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  liuPanScoreMaxY q x (fun y l =>
    |liuPanSignedMainSum distMain y X q l f u v| +
      liuPanSignedCorrectionBound y X q l f)

theorem liuPanSignedResidualMaxY_one
    (distMain : ℝ → ℝ) (X x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanSignedResidualMaxY distMain X 1 x f u v =
      ((range (x + 1)).image (fun y =>
        |liuPanSignedMainSum distMain y X 1 0 f u v| +
          liuPanSignedCorrectionBound y X 1 0 f)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold liuPanSignedResidualMaxY liuPanScoreMaxY
  simp only [liuPanScoreMaxL_one]

theorem liuPanSignedResidualMaxY_nonneg
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ liuPanSignedResidualMaxY distMain X q x f u v := by
  apply liuPanScoreMaxY_nonneg
  intro y l
  exact add_nonneg (abs_nonneg _)
    (liuPanSignedCorrectionBound_nonneg y X q l f)

private theorem liuPanScoreMaxL_le_three
    (q : ℕ) (s t₁ t₂ t₃ : ℕ → ℝ)
    (h : ∀ l, l.Coprime q → s l ≤ t₁ l + t₂ l + t₃ l) :
    liuPanScoreMaxL q s ≤
      liuPanScoreMaxL q t₁ + liuPanScoreMaxL q t₂ + liuPanScoreMaxL q t₃ := by
  unfold liuPanScoreMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · simp only [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hcop : l.Coprime q := (Finset.mem_filter.mp hl).2
    have h₁ := Finset.le_max'
      ((unitResidues q).image t₁) (t₁ l)
      (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h₂ := Finset.le_max'
      ((unitResidues q).image t₂) (t₂ l)
      (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h₃ := Finset.le_max'
      ((unitResidues q).image t₃) (t₃ l)
      (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    linarith [h l hcop]
  · simp [hS]

private theorem liuPanScoreMaxY_le_three
    (q x : ℕ) (s t₁ t₂ t₃ : ℕ → ℕ → ℝ)
    (h : ∀ y l, l.Coprime q →
      s y l ≤ t₁ y l + t₂ y l + t₃ y l) :
    liuPanScoreMaxY q x s ≤
      liuPanScoreMaxY q x t₁ + liuPanScoreMaxY q x t₂ +
        liuPanScoreMaxY q x t₃ := by
  unfold liuPanScoreMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hpoint := liuPanScoreMaxL_le_three q (s y) (t₁ y) (t₂ y) (t₃ y) (h y)
  have h₁ := Finset.le_max'
    ((range (x + 1)).image (fun y => liuPanScoreMaxL q (t₁ y)))
    (liuPanScoreMaxL q (t₁ y)) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have h₂ := Finset.le_max'
    ((range (x + 1)).image (fun y => liuPanScoreMaxL q (t₂ y)))
    (liuPanScoreMaxL q (t₂ y)) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have h₃ := Finset.le_max'
    ((range (x + 1)).image (fun y => liuPanScoreMaxL q (t₃ y)))
    (liuPanScoreMaxL q (t₃ y)) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  linarith

/-- Maximal pointwise signed decomposition for the arbitrary distribution main. -/
theorem liuMainPanMaxY_le_sourceFaithfulSigned
    (distMain : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    liuMainPanMaxY distMain X q x f ≤
      panPieceMaxY X q x f
          (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
        panPieceMaxY X q x f
          (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
        liuPanSignedResidualMaxY distMain X q x f u v := by
  change liuPanScoreMaxY q x
      (fun y l => |liuMainPanCoprimeSum distMain y X q l f|) ≤
    liuPanScoreMaxY q x (fun y l =>
      |panPieceSum y X q l f
        (fun y q l => apV1 y q l u / Real.log (y : ℝ))|) +
      liuPanScoreMaxY q x (fun y l =>
        |panPieceSum y X q l f
          (fun y q l => apV3 y q l u v / Real.log (y : ℝ))|) +
      liuPanScoreMaxY q x (fun y l =>
        |liuPanSignedMainSum distMain y X q l f u v| +
          liuPanSignedCorrectionBound y X q l f)
  exact liuPanScoreMaxY_le_three q x _ _ _ _
    (fun y l hl =>
      abs_liuMainPanCoprimeSum_le_sourceFaithfulSigned
        distMain y X q l f u v hf0)

/-! ## Uniform source-faithful assembly -/

/-- The exact inverse-log weighted bound for the concrete arbitrary-main signed
residual. -/
def LiuMainPanSourceFaithfulSignedMainBound
    (distMain : ℝ → ℝ) (x f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (Real.log (x X)) ^ B) + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
          liuPanSignedResidualMaxY distMain X q (Nat.floor (x X)) f u v ≤
        C * x X / (Real.log (x X)) ^ A

/-- The main-parametric analogue of ANT's global Pan mean-value predicate. -/
def LiuMainPanMeanValueUniform
    (distMain : ℝ → ℝ) (x f : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (Real.log (x X)) ^ B) + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
          liuMainPanMaxY distMain X q (Nat.floor (x X)) f ≤
        C * x X / (Real.log (x X)) ^ A

theorem LiuMainPanMeanValueUniform.of_sourceFaithfulSignedInputs
    {distMain : ℝ → ℝ} {x f : ℕ → ℝ} {u v : ℕ}
    (hI : PanTypeICharacterMeanValue x f u)
    (hII : PanTypeIICharacterMeanValue x f u v)
    (hM : LiuMainPanSourceFaithfulSignedMainBound distMain x f u v)
    (hfin : PanLogEventuallyLarge x)
    (hf0 : f 0 = 0) :
    LiuMainPanMeanValueUniform distMain x f := by
  have hI' : PanTypeIWeightedBound x f u :=
    PanTypeIWeightedBound.of_characterMeanValue hI
  have hII' : PanTypeIIWeightedBound x f u v :=
    PanTypeIIWeightedBound.of_characterMeanValue hII
  rcases hfin with ⟨X₀, hX₀⟩
  intro A hA
  rcases hI' A hA with ⟨C1, hC1, B1, x₀1, hI1⟩
  rcases hII' A hA with ⟨C2, hC2, B2, x₀2, hII1⟩
  rcases hM A hA with ⟨C3, hC3, B3, x₀3, hM1⟩
  refine ⟨C1 + C2 + C3, add_pos (add_pos hC1 hC2) hC3,
    max B1 (max B2 B3), max (max x₀1 (max x₀2 x₀3)) X₀, ?_⟩
  intro X hX
  have hX1 : x₀1 ≤ X := by omega
  have hX2 : x₀2 ≤ X := by omega
  have hX3 : x₀3 ≤ X := by omega
  have hX0 : X₀ ≤ X := by omega
  have hL : 1 ≤ Real.log (x X) := hX₀ X hX0
  have hsqrt : 0 ≤ (x X) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  let B : ℝ := max B1 (max B2 B3)
  let Q : ℕ :=
    Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B)
  have hQ1 : Q ≤ Nat.floor
      ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) :=
    panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_max_left _ _)
  have hQ2 : Q ≤ Nat.floor
      ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2) :=
    panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_trans (le_max_left _ _) (le_max_right _ _))
  have hQ3 : Q ≤ Nat.floor
      ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3) :=
    panAssembly_floor_le _ _ _ _ hsqrt hL (by
      dsimp [B]
      exact le_trans (le_max_right _ _) (le_max_right _ _))
  let w : ℕ → ℝ := fun q =>
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card
  let pI : ℕ → ℝ := fun q =>
    panPieceMaxY X q (Nat.floor (x X)) f
      (fun y q l => apV1 y q l u / Real.log (y : ℝ))
  let pII : ℕ → ℝ := fun q =>
    panPieceMaxY X q (Nat.floor (x X)) f
      (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
  let pM : ℕ → ℝ := fun q =>
    liuPanSignedResidualMaxY distMain X q (Nat.floor (x X)) f u v
  have hw : ∀ q, 0 ≤ w q := by
    intro q
    dsimp [w]
    exact panTypeI_weight_nonneg q
  have hpI : ∀ q, 0 ≤ pI q := by
    intro q
    change 0 ≤ liuPanScoreMaxY q (Nat.floor (x X)) (fun y l =>
      |panPieceSum y X q l f
        (fun y q l => apV1 y q l u / Real.log (y : ℝ))|)
    exact liuPanScoreMaxY_nonneg _ _ _ (fun y l => abs_nonneg _)
  have hpII : ∀ q, 0 ≤ pII q := by
    intro q
    change 0 ≤ liuPanScoreMaxY q (Nat.floor (x X)) (fun y l =>
      |panPieceSum y X q l f
        (fun y q l => apV3 y q l u v / Real.log (y : ℝ))|)
    exact liuPanScoreMaxY_nonneg _ _ _ (fun y l => abs_nonneg _)
  have hpM : ∀ q, 0 ≤ pM q := fun q =>
    liuPanSignedResidualMaxY_nonneg _ _ _ _ _ _ _
  have hI2 : (∑ q ∈ range (Q + 1), w q * pI q) ≤
      C1 * x X / (Real.log (x X)) ^ A :=
    (panAssembly_sum_le_sum Q _ _ hQ1
      (fun q => mul_nonneg (hw q) (hpI q))).trans
      (by simpa [w, pI] using hI1 X hX1)
  have hII2 : (∑ q ∈ range (Q + 1), w q * pII q) ≤
      C2 * x X / (Real.log (x X)) ^ A :=
    (panAssembly_sum_le_sum Q _ _ hQ2
      (fun q => mul_nonneg (hw q) (hpII q))).trans
      (by simpa [w, pII] using hII1 X hX2)
  have hM2 : (∑ q ∈ range (Q + 1), w q * pM q) ≤
      C3 * x X / (Real.log (x X)) ^ A :=
    (panAssembly_sum_le_sum Q _ _ hQ3
      (fun q => mul_nonneg (hw q) (hpM q))).trans
      (by simpa [w, pM] using hM1 X hX3)
  calc
    (∑ q ∈ range (Q + 1),
        w q * liuMainPanMaxY distMain X q (Nat.floor (x X)) f) ≤
        ∑ q ∈ range (Q + 1), w q * (pI q + pII q + pM q) := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hq0 : q = 0
      · subst q
        have hμ : (ArithmeticFunction.moebius 0 : ℤ) = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree
            not_squarefree_zero
        simp [w, hμ]
      · exact mul_le_mul_of_nonneg_left
          (by simpa [pI, pII, pM] using
            (liuMainPanMaxY_le_sourceFaithfulSigned
              distMain X q (Nat.floor (x X)) f u v hf0))
          (hw q)
    _ = (∑ q ∈ range (Q + 1), w q * pI q) +
          (∑ q ∈ range (Q + 1), w q * pII q) +
          (∑ q ∈ range (Q + 1), w q * pM q) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ C1 * x X / (Real.log (x X)) ^ A +
          C2 * x X / (Real.log (x X)) ^ A +
          C3 * x X / (Real.log (x X)) ^ A :=
      add_le_add (add_le_add hI2 hII2) hM2
    _ = (C1 + C2 + C3) * x X / (Real.log (x X)) ^ A := by ring

/-! ## Fixed-source transparent inputs and the Liu endpoint -/

/-- Exact weighted Type I finite input at the source parameter `N`. -/
def LiuMainPanTypeIPieceBoundAt
    (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) (u : ℕ) : Prop :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      panPieceMaxY N q N f
        (fun y q l => apV1 y q l u / Real.log (y : ℝ)) ≤
    C * N / Real.log N ^ A

/-- Exact weighted Type II finite input at the source parameter `N`. -/
def LiuMainPanTypeIIPieceBoundAt
    (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) (u v : ℕ) : Prop :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      panPieceMaxY N q N f
        (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) ≤
    C * N / Real.log N ^ A

/-- Exact weighted finite input for the concrete signed main and prime-power
residual at the source parameter `N`. -/
def LiuMainPanSignedResidualBoundAt
    (distMain : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ)
    (A B C : ℝ) (u v : ℕ) : Prop :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanSignedResidualMaxY distMain N q N f u v ≤
    C * N / Real.log N ^ A

/-- The three explicit source-faithful finite inputs produce the fixed-`N`
main-parametric Pan inequality.  This does not take a `LiuMainPanMeanValueAt`
witness as an assumption. -/
theorem liuMainPanMeanValueAt_of_concreteSignedInputs
    (distMain : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ)
    (A B C1 C2 C3 : ℝ) (u v : ℕ) (hf0 : f 0 = 0)
    (hI : LiuMainPanTypeIPieceBoundAt N f A B C1 u)
    (hII : LiuMainPanTypeIIPieceBoundAt N f A B C2 u v)
    (hM : LiuMainPanSignedResidualBoundAt distMain N f A B C3 u v) :
    LiuMainPanMeanValueAt distMain N f A B (C1 + C2 + C3) := by
  unfold LiuMainPanMeanValueAt
  unfold LiuMainPanTypeIPieceBoundAt at hI
  unfold LiuMainPanTypeIIPieceBoundAt at hII
  unfold LiuMainPanSignedResidualBoundAt at hM
  let w : ℕ → ℝ := fun q =>
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card
  let pI : ℕ → ℝ := fun q =>
    panPieceMaxY N q N f
      (fun y q l => apV1 y q l u / Real.log (y : ℝ))
  let pII : ℕ → ℝ := fun q =>
    panPieceMaxY N q N f
      (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
  let pM : ℕ → ℝ := fun q =>
    liuPanSignedResidualMaxY distMain N q N f u v
  have hw : ∀ q, 0 ≤ w q := by
    intro q
    dsimp [w]
    exact panTypeI_weight_nonneg q
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1),
        w q * liuMainPanMaxY distMain N q N f) ≤
        ∑ q ∈ range (panModulusCutoff N B + 1),
          w q * (pI q + pII q + pM q) := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hq0 : q = 0
      · subst q
        have hμ : (ArithmeticFunction.moebius 0 : ℤ) = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree
            not_squarefree_zero
        simp [w, hμ]
      · exact mul_le_mul_of_nonneg_left
          (by simpa [pI, pII, pM] using
            (liuMainPanMaxY_le_sourceFaithfulSigned distMain N q N f u v hf0))
          (hw q)
    _ = (∑ q ∈ range (panModulusCutoff N B + 1), w q * pI q) +
          (∑ q ∈ range (panModulusCutoff N B + 1), w q * pII q) +
          (∑ q ∈ range (panModulusCutoff N B + 1), w q * pM q) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ C1 * N / Real.log N ^ A +
          C2 * N / Real.log N ^ A +
          C3 * N / Real.log N ^ A := by
      exact add_le_add (add_le_add (by simpa [w, pI] using hI)
        (by simpa [w, pII] using hII)) (by simpa [w, pM] using hM)
    _ = (C1 + C2 + C3) * N / Real.log N ^ A := by ring

/-- An eventual family of explicit Type I, Type II, and concrete signed residual
inputs for Liu's source-varying weight. -/
def LiuMainPanSourceFamilyInputs
    (distMain : ℝ → ℝ) (A B C1 C2 C3 : ℝ) (u v : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    LiuMainPanTypeIPieceBoundAt N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C1 u ∧
    LiuMainPanTypeIIPieceBoundAt N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C2 u v ∧
    LiuMainPanSignedResidualBoundAt distMain N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C3 u v

theorem eventually_liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_sourceFaithfulSignedInputs
    (κ ε A B C1 C2 C3 : ℝ) (u v : ℕ)
    (hε : 0 < ε) (hB : 0 ≤ B)
    (hsource : LiuMainPanSourceFamilyInputs
      (liuLogarithmicIntegral κ) A B C1 C2 C3 u v) :
    ∀ᶠ N : ℕ in atTop,
      liuPaperQSourceFullDistributionMajorant (liuLogarithmicIntegral κ) N ε ≤
        (C1 + C2 + C3) * N / Real.log N ^ A +
          15 * liuLogarithmicIntegralUpperConstant κ *
            liuSourceR1P₂ReciprocalBound *
            paperQStyleDivisorWeightLogConstant *
            (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hcut := eventually_liuSourceDEpsilon_le_panModulusCutoff ε B hε hB
  filter_upwards [hsource, hcut, eventually_ge_atTop 8] with N hsourceN hcutN hN
  rcases hsourceN with ⟨hI, hII, hM⟩
  have hf0 : liuWeight N (liuSourceZ10 N) (liuSourceY3 N) 0 = 0 := by
    simp only [liuWeight, ite_eq_right_iff, one_ne_zero, imp_false]
    rintro ⟨⟨p₁, p₂⟩, hp, hprod⟩
    have hpair := mem_liuWeightPairs.mp hp
    exact (Nat.mul_ne_zero hpair.1.ne_zero hpair.2.1.ne_zero) hprod
  have hpan : LiuMainPanMeanValueAt (liuLogarithmicIntegral κ) N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B (C1 + C2 + C3) :=
    liuMainPanMeanValueAt_of_concreteSignedInputs
      (liuLogarithmicIntegral κ) N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      A B C1 C2 C3 u v hf0 hI hII hM
  exact liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le
    κ N ε A (C1 + C2 + C3) hN (le_of_lt hε)
    (liuLogarithmicIntegral_liuPaperQCoprimeRBound_of_panMeanValueAt
      κ N ε A B (C1 + C2 + C3) hcutN hpan)

end MathlibNt.SieveTheory.LiuWeight
