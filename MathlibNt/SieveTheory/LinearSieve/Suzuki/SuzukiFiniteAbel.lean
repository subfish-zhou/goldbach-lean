import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Tactic

namespace MathlibNt.SieveTheory.LinearSieve

open scoped BigOperators

/-- Finite Abel summation on an initial segment. -/
theorem finiteAbelSum_range {𝕜 : Type*} [CommRing 𝕜]
    {R H : ℕ → 𝕜} (n : ℕ) :
    (∑ i ∈ Finset.range n, (R i - R (i + 1)) * H i) =
      R 0 * H 0 - R n * H n +
        ∑ i ∈ Finset.range n, R (i + 1) * (H (i + 1) - H i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ, ih]
      ring

/-- Exact finite Abel identity on the natural interval `[w,z)`.  The term
`R (x+1)` is the right-endpoint value in the discrete Stieltjes increment. -/
theorem finiteAbelSum_Ico {𝕜 : Type*} [CommRing 𝕜]
    {a R H : ℕ → 𝕜} {w z : ℕ} (hwz : w ≤ z)
    (hdiff : ∀ n ∈ Finset.Ico w z, a n = R n - R (n + 1)) :
    (∑ n ∈ Finset.Ico w z, a n * H n) =
      R w * H w - R z * H z +
        ∑ n ∈ Finset.Ico w z, R (n + 1) * (H (n + 1) - H n) := by
  simp only [Finset.sum_Ico_eq_sum_range]
  have hdiff' : ∀ i ∈ Finset.range (z - w),
      a (w + i) = R (w + i) - R (w + i + 1) := by
    intro i hi
    apply hdiff
    simp only [Finset.mem_Ico]
    constructor
    · omega
    · have hi' : i < z - w := Finset.mem_range.mp hi
      omega
  calc
    (∑ i ∈ Finset.range (z - w), a (w + i) * H (w + i)) =
        ∑ i ∈ Finset.range (z - w),
          (R (w + i) - R (w + i + 1)) * H (w + i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdiff' i hi]
    _ = R w * H w - R z * H z +
        ∑ i ∈ Finset.range (z - w),
          R (w + i + 1) * (H (w + i + 1) - H (w + i)) := by
      simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_sub_of_le hwz] using
        (finiteAbelSum_range (R := fun i => R (w + i))
          (H := fun i => H (w + i)) (z - w))


/-- Suzuki Lemma 8.5's exact finite Abel identity, before replacing `R` by its
main term plus error.  `R z = 1` corresponds to the empty tail at the upper
endpoint. -/
theorem suzukiLemma85_finiteAbel {𝕜 : Type*} [CommRing 𝕜]
    {a R H : ℕ → 𝕜} {w z : ℕ}
    (hwz : w ≤ z) (hRz : R z = 1)
    (hdiff : ∀ n ∈ Finset.Ico w z, a n = R n - R (n + 1)) :
    (∑ n ∈ Finset.Ico w z, a n * H n) =
      -H z + R w * H w +
        ∑ n ∈ Finset.Ico w z, R (n + 1) * (H (n + 1) - H n) := by
  rw [finiteAbelSum_Ico hwz hdiff, hRz]
  ring

/-- Fully explicit tail-sum form.  A prime sum is obtained by taking `a n = 0`
off primes.  No positivity, monotonicity, continuity, or primality hypothesis is
used by this exact finite identity. -/
theorem suzukiLemma85_finiteAbel_tail {𝕜 : Type*} [CommRing 𝕜]
    (a H : ℕ → 𝕜) {w z : ℕ} (hwz : w ≤ z) :
    (∑ n ∈ Finset.Ico w z, a n * H n) =
      -H z + (1 + ∑ p ∈ Finset.Ico w z, a p) * H w +
        ∑ n ∈ Finset.Ico w z,
          (1 + ∑ p ∈ Finset.Ico (n + 1) z, a p) *
            (H (n + 1) - H n) := by
  let R : ℕ → 𝕜 := fun x => 1 + ∑ p ∈ Finset.Ico x z, a p
  apply suzukiLemma85_finiteAbel (R := R) hwz
  · simp [R]
  · intro n hn
    have hnz : n ≤ z := (Finset.mem_Ico.mp hn).2.le
    have hsnz : n + 1 ≤ z := (Finset.mem_Ico.mp hn).2
    dsimp [R]
    rw [Finset.sum_Ico_eq_sub a hnz, Finset.sum_Ico_eq_sub a hsnz,
      Finset.sum_range_succ]
    ring

/-- Sum `(R x - R y) * g x` over consecutive nodes `x,y` of a finite list. -/
def finiteNodeAtomSum {α A : Type*} [CommRing A]
    (R g : α → A) : List α → A
  | x :: y :: xs => (R x - R y) * g x + finiteNodeAtomSum R g (y :: xs)
  | _ => 0

/-- Sum `R y * (g y - g x)` over consecutive nodes `x,y` of a finite list. -/
def finiteNodeVariationSum {α A : Type*} [CommRing A]
    (R g : α → A) : List α → A
  | x :: y :: xs => R y * (g y - g x) + finiteNodeVariationSum R g (y :: xs)
  | _ => 0

/-- Exact finite-node Abel identity.  It is intentionally stated for the list
`w :: interior ++ [z]`, so the two boundary values remain exactly `g w` and
`g z`, even when `w,z : ℝ` are not integers. -/
theorem finiteNodeAbel {α A : Type*} [CommRing A]
    (R g : α → A) (w z : α) (interior : List α) :
    finiteNodeAtomSum R g (w :: interior ++ [z]) =
      R w * g w - R z * g z +
        finiteNodeVariationSum R g (w :: interior ++ [z]) := by
  induction interior generalizing w with
  | nil =>
      simp [finiteNodeAtomSum, finiteNodeVariationSum]
      ring
  | cons x xs ih =>
      simp only [List.cons_append]
      rw [finiteNodeAtomSum, finiteNodeVariationSum]
      have htail := ih x
      simp only [List.cons_append] at htail
      rw [htail]
      ring

/-! ## Exact main-ratio/error decomposition

The next statements are purely finite algebra.  In particular they use no
monotonicity, continuity, differentiability, or ordering hypothesis on the
nodes.  The sign convention makes `finiteNodeStieltjesSum F g` the left-node
sum for `-∫ g dF`: its increment is `F x - F y` on an adjacent pair `x,y`.
-/

/-- Left-node finite Stieltjes sum with increments `F x - F y`. -/
def finiteNodeStieltjesSum {α A : Type*} [CommRing A]
    (F g : α → A) : List α → A
  | x :: y :: xs => g x * (F x - F y) + finiteNodeStieltjesSum F g (y :: xs)
  | _ => 0

/-- The atom sum is exactly the finite Stieltjes sum, up to the harmless
commutation of the two factors in each summand. -/
theorem finiteNodeStieltjesSum_eq_atomSum {α A : Type*} [CommRing A]
    (F g : α → A) (nodes : List α) :
    finiteNodeStieltjesSum F g nodes = finiteNodeAtomSum F g nodes := by
  induction nodes with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          rw [finiteNodeStieltjesSum, finiteNodeAtomSum, ih]
          ring

/-- Variation is additive in the coefficient function. -/
theorem finiteNodeVariationSum_add {α A : Type*} [CommRing A]
    (F E g : α → A) (nodes : List α) :
    finiteNodeVariationSum (fun x => F x + E x) g nodes =
      finiteNodeVariationSum F g nodes + finiteNodeVariationSum E g nodes := by
  induction nodes with
  | nil => simp [finiteNodeVariationSum]
  | cons x xs ih =>
      cases xs with
      | nil => simp [finiteNodeVariationSum]
      | cons y ys =>
          rw [finiteNodeVariationSum, finiteNodeVariationSum,
            finiteNodeVariationSum, ih]
          ring

/-- The exact main ratio `log z / log x`, with no domain convention imposed. -/
noncomputable def finiteNodeLogRatio (z x : ℝ) : ℝ :=
  Real.log z / Real.log x

/-- The main finite Stieltjes sum.  Explicitly, each adjacent pair `x,y`
contributes
`g x * (log z / log x - log z / log y)`.
This is the finite object to compare with the ordinary integral against
`log z / (x * (log x)^2) dx`. -/
noncomputable def finiteNodeMainRatioSum
    (z : ℝ) (g : ℝ → ℝ) (nodes : List ℝ) : ℝ :=
  finiteNodeStieltjesSum (finiteNodeLogRatio z) g nodes

/-- Boundary plus variation of the main ratio telescopes exactly to its finite
Stieltjes sum.  This is unconditional finite algebra. -/
theorem finiteNodeMainRatio_boundary_variation
    (w u z : ℝ) (interior : List ℝ) (g : ℝ → ℝ) :
    finiteNodeLogRatio z w * g w - finiteNodeLogRatio z u * g u +
        finiteNodeVariationSum (finiteNodeLogRatio z) g
          (w :: interior ++ [u]) =
      finiteNodeMainRatioSum z g (w :: interior ++ [u]) := by
  rw [finiteNodeMainRatioSum, finiteNodeStieltjesSum_eq_atomSum,
    finiteNodeAbel]

/-- Exact finite-node split for `R(x) = log z / log x + E(x)`.

The main boundary and variation terms have been telescoped into the finite
Stieltjes sum.  Every error contribution is retained explicitly as two endpoint
terms plus the finite variation of `g`; there are no analytic assumptions. -/
theorem finiteNodeAbel_mainRatio_errorVariation
    (R E g : ℝ → ℝ) (w u z : ℝ) (interior : List ℝ)
    (hR : ∀ x, R x = finiteNodeLogRatio z x + E x) :
    finiteNodeAtomSum R g (w :: interior ++ [u]) =
      finiteNodeMainRatioSum z g (w :: interior ++ [u]) +
        (E w * g w - E u * g u +
          finiteNodeVariationSum E g (w :: interior ++ [u])) := by
  let M : ℝ → ℝ := finiteNodeLogRatio z
  have hfun : R = fun x => M x + E x := by
    funext x
    exact hR x
  calc
    finiteNodeAtomSum R g (w :: interior ++ [u]) =
        R w * g w - R u * g u +
          finiteNodeVariationSum R g (w :: interior ++ [u]) :=
      finiteNodeAbel R g w u interior
    _ = (M w * g w - M u * g u +
          finiteNodeVariationSum M g (w :: interior ++ [u])) +
        (E w * g w - E u * g u +
          finiteNodeVariationSum E g (w :: interior ++ [u])) := by
      rw [hfun, finiteNodeVariationSum_add]
      ring
    _ = finiteNodeMainRatioSum z g (w :: interior ++ [u]) +
        (E w * g w - E u * g u +
          finiteNodeVariationSum E g (w :: interior ++ [u])) := by
      rw [finiteNodeMainRatio_boundary_variation]

/-- At a nondegenerate upper endpoint the main ratio has the expected value
one, so its upper boundary term is literally `-g z`. -/
@[simp] theorem finiteNodeLogRatio_self {z : ℝ} (hz : Real.log z ≠ 0) :
    finiteNodeLogRatio z z = 1 := by
  simp [finiteNodeLogRatio, hz]

/-- A finite adjacent-edge majorant telescopes.  Pairwise control is stronger than
needed, but matches the ordered Suzuki node list. -/
theorem finiteNodeVariationSum_le_telescope
    {α : Type*} (E g t : α → ℝ) (C : ℝ) (w z : α) (interior : List α)
    (hedge : (w :: interior ++ [z]).Pairwise
      (fun x y => E y * (g y - g x) ≤ C * (t x - t y))) :
    finiteNodeVariationSum E g (w :: interior ++ [z]) ≤ C * (t w - t z) := by
  induction interior generalizing w with
  | nil =>
      simpa [finiteNodeVariationSum] using hedge
  | cons x xs ih =>
      simp only [List.cons_append] at hedge ⊢
      have hfirst : E x * (g x - g w) ≤ C * (t w - t x) := by
        exact (List.pairwise_cons.mp hedge).1 x (by simp)
      have htail : finiteNodeVariationSum E g (x :: xs ++ [z]) ≤
          C * (t x - t z) :=
        ih x (List.pairwise_cons.mp hedge).2
      change E x * (g x - g w) + finiteNodeVariationSum E g (x :: xs ++ [z]) ≤
        C * (t w - t z)
      calc
        E x * (g x - g w) + finiteNodeVariationSum E g (x :: xs ++ [z]) ≤
            C * (t w - t x) + C * (t x - t z) := add_le_add hfirst htail
        _ = C * (t w - t z) := by ring

theorem finiteNodeVariationSum_mono_of_pairwise
    {α : Type*} (E B g : α → ℝ) (nodes : List α)
    (h : nodes.Pairwise (fun x y => E y * (g y - g x) ≤ B y * (g y - g x))) :
    finiteNodeVariationSum E g nodes ≤ finiteNodeVariationSum B g nodes := by
  induction nodes with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          rw [finiteNodeVariationSum, finiteNodeVariationSum]
          exact add_le_add ((List.pairwise_cons.mp h).1 y (by simp))
            (ih (List.pairwise_cons.mp h).2)

theorem finiteNodeVariationSum_smul_left
    {α : Type*} (C : ℝ) (B g : α → ℝ) (nodes : List α) :
    finiteNodeVariationSum (fun x => C * B x) g nodes =
      C * finiteNodeVariationSum B g nodes := by
  induction nodes with
  | nil => simp [finiteNodeVariationSum]
  | cons x xs ih =>
      cases xs with
      | nil => simp [finiteNodeVariationSum]
      | cons y ys =>
          rw [finiteNodeVariationSum, finiteNodeVariationSum, ih]
          ring

theorem finiteNodeAtomSum_le_telescope
    {α : Type*} (R g t : α → ℝ) (C : ℝ) (w z : α) (interior : List α)
    (h : (w :: interior ++ [z]).Pairwise
      (fun x y => (R x - R y) * g x ≤ C * (t x - t y))) :
    finiteNodeAtomSum R g (w :: interior ++ [z]) ≤ C * (t w - t z) := by
  induction interior generalizing w with
  | nil => simpa [finiteNodeAtomSum] using h
  | cons x xs ih =>
      simp only [List.cons_append] at h ⊢
      have hfirst := (List.pairwise_cons.mp h).1 x (by simp)
      have htail := ih x (List.pairwise_cons.mp h).2
      change (R w - R x) * g w + finiteNodeAtomSum R g (x :: xs ++ [z]) ≤
        C * (t w - t z)
      calc
        (R w - R x) * g w + finiteNodeAtomSum R g (x :: xs ++ [z]) ≤
            C * (t w - t x) + C * (t x - t z) := add_le_add hfirst htail
        _ = C * (t w - t z) := by ring

end MathlibNt.SieveTheory.LinearSieve
