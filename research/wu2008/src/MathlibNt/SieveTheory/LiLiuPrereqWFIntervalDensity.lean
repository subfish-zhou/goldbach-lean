import MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryLayers
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Normalized exponential bounds on intervals of small primes

The weights and cubic boundary kernels are the ones already constructed.
An exponential tilt bounds the kernels, and an Euler-product majorant
retains the normalization needed by the dimension-one hypothesis.
The resulting estimate is useful on `w ≤ p < u` when `log u / log w`
is bounded. It does not control the remaining small-minimum boundaries.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open Finset
open scoped Classical

private theorem exp_card_le_three_pow (n : ℕ) :
    Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
  calc
    Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      simp [← Real.exp_nat_mul]
    _ ≤ 3 ^ n := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le n

private theorem boundary_tilt (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hs : s ⊆ geometricSmallPrimes P D ε)
    (hfail : D ^ ε ≤ ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3) :
    1 ≤ Real.exp (3 - 1 / ε) * (3 : ℝ) ^ s.card := by
  have hc := small_cubic_failure_card P hD hε hq hs hfail
  have he : 1 / ε < (s.card : ℝ) + 3 := (div_lt_iff₀ hε).mpr (by nlinarith)
  calc
    1 ≤ Real.exp (3 - 1 / ε + (s.card : ℝ)) :=
      Real.one_le_exp_iff.mpr (by linarith)
    _ = Real.exp (3 - 1 / ε) * Real.exp (s.card : ℝ) := Real.exp_add _ _
    _ ≤ Real.exp (3 - 1 / ε) * 3 ^ s.card :=
      mul_le_mul_of_nonneg_left (exp_card_le_three_pow _) (Real.exp_pos _).le

theorem lowerBoundaryDensity_le_tilt (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {g : ℕ → ℝ} {q : ℕ} {B : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hB : B ⊆ geometricSmallPrimes P D ε)
    (hg : ∀ p ∈ B, 0 ≤ g p) :
    lowerBoundaryDensity (D ^ ε) g q B ≤
      Real.exp (3 - 1 / ε) * ∏ p ∈ B, (1 + 3 * g p) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  have hp : 0 ≤ ∏ p ∈ s, g p := Finset.prod_nonneg fun p hp => hg p (hsub hp)
  by_cases hb : LowerBoundary (D ^ ε) q s
  · simp only [if_pos hb, Finset.prod_mul_distrib, Finset.prod_const]
    have ht := boundary_tilt P hD hε hq (hsub.trans hB) hb.2.2.2
    nlinarith [mul_le_mul_of_nonneg_right ht hp]
  · simp only [if_neg hb]
    exact mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg fun p hp => mul_nonneg (by norm_num) (hg p (hsub hp)))

theorem upperBoundaryDensity_le_tilt (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {g : ℕ → ℝ} {q : ℕ} {B : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hB : B ⊆ geometricSmallPrimes P D ε)
    (hg : ∀ p ∈ B, 0 ≤ g p) :
    upperBoundaryDensity (D ^ ε) g q B ≤
      Real.exp (3 - 1 / ε) * ∏ p ∈ B, (1 + 3 * g p) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  have hp : 0 ≤ ∏ p ∈ s, g p := Finset.prod_nonneg fun p hp => hg p (hsub hp)
  by_cases hb : UpperBoundary (D ^ ε) q s
  · simp only [if_pos hb, Finset.prod_mul_distrib, Finset.prod_const]
    have ht := boundary_tilt P hD hε hq (hsub.trans hB) hb.2.2.2
    nlinarith [mul_le_mul_of_nonneg_right ht hp]
  · simp only [if_neg hb]
    exact mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg fun p hp => mul_nonneg (by norm_num) (hg p (hsub hp)))

/-- The factor `1/4` is the exact telescoping coefficient for the tilt `3`. -/
theorem lowerDensityDefect_le_tilt (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {g : ℕ → ℝ} (ps : List ℕ)
    (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p ∈ geometricSmallPrimes P D ε)
    (hg : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1) :
    lowerDensityDefect (D ^ ε) g ps ≤ Real.exp (3 - 1 / ε) / 4 *
      ((∏ p ∈ ps.toFinset, (1 + 3 * g p)) - ∏ p ∈ ps.toFinset, (1 - g p)) := by
  induction ps with
  | nil => simp [lowerDensityDefect]
  | cons q ps ih =>
      obtain ⟨hqnot, hnd⟩ := List.nodup_cons.mp hnd
      have hqB : q ∉ ps.toFinset := by simpa using hqnot
      have hq := hg q (by simp)
      have ht := ih hnd (fun p hp => hps p (by simp [hp]))
        (fun p hp => hg p (by simp [hp]))
      have hb := lowerBoundaryDensity_le_tilt P hD hε (hps q (by simp))
        (fun p hp => hps p (by simpa using Or.inr (List.mem_toFinset.mp hp)))
        (fun p hp => (hg p (by simpa using Or.inr (List.mem_toFinset.mp hp))).1)
      simp only [lowerDensityDefect, List.toFinset_cons, Finset.prod_insert hqB]
      nlinarith [mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hq.2),
        mul_le_mul_of_nonneg_left hb hq.1]

theorem upperDensityDefect_le_tilt (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {g : ℕ → ℝ} (ps : List ℕ)
    (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p ∈ geometricSmallPrimes P D ε)
    (hg : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1) :
    upperDensityDefect (D ^ ε) g ps ≤ Real.exp (3 - 1 / ε) / 4 *
      ((∏ p ∈ ps.toFinset, (1 + 3 * g p)) - ∏ p ∈ ps.toFinset, (1 - g p)) := by
  induction ps with
  | nil => simp [upperDensityDefect]
  | cons q ps ih =>
      obtain ⟨hqnot, hnd⟩ := List.nodup_cons.mp hnd
      have hqB : q ∉ ps.toFinset := by simpa using hqnot
      have hq := hg q (by simp)
      have ht := ih hnd (fun p hp => hps p (by simp [hp]))
        (fun p hp => hg p (by simp [hp]))
      have hb := upperBoundaryDensity_le_tilt P hD hε (hps q (by simp))
        (fun p hp => hps p (by simpa using Or.inr (List.mem_toFinset.mp hp)))
        (fun p hp => (hg p (by simpa using Or.inr (List.mem_toFinset.mp hp))).1)
      simp only [upperDensityDefect, List.toFinset_cons, Finset.prod_insert hqB]
      nlinarith [mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hq.2),
        mul_le_mul_of_nonneg_left hb hq.1]

private theorem tilted_factor_mul_cube_le_one {x : ℝ} (hx1 : x ≤ 1) :
    (1 + 3 * x) * (1 - x) ^ 3 ≤ 1 := by
  have hid : 1 - (1 + 3 * x) * (1 - x) ^ 3 =
      x ^ 2 * (3 * (1 - x) ^ 2 + 2 * (1 - x) + 1) := by ring
  have hn : 0 ≤ x ^ 2 * (3 * (1 - x) ^ 2 + 2 * (1 - x) + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- A product estimate rather than an unnormalized prime-mass bound. -/
theorem tiltedProduct_le_euler_mul_fourth {g : ℕ → ℝ} (B : Finset ℕ) {A : ℝ}
    (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p < 1)
    (hA : (∏ p ∈ B, (1 - g p))⁻¹ ≤ A) :
    (∏ p ∈ B, (1 + 3 * g p)) ≤ (∏ p ∈ B, (1 - g p)) * A ^ 4 := by
  let V := ∏ p ∈ B, (1 - g p)
  have hV : 0 < V := Finset.prod_pos fun p hp => sub_pos.mpr (hg p hp).2
  have hprod : (∏ p ∈ B, (1 + 3 * g p)) * V ^ 3 ≤ 1 := by
    rw [show V ^ 3 = ∏ p ∈ B, (1 - g p) ^ 3 by simp [V, Finset.prod_pow],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_one (fun p hp =>
      mul_nonneg (by linarith [(hg p hp).1])
        (pow_nonneg (sub_nonneg.mpr (hg p hp).2.le) _))
      (fun p hp => tilted_factor_mul_cube_le_one (hg p hp).2.le)
  have hAV : 1 ≤ A * V := (inv_le_iff_one_le_mul₀ hV).mp hA
  have hpow : 1 ≤ (A * V) ^ 4 := one_le_pow₀ hAV
  apply (mul_le_mul_iff_left₀ (pow_pos hV 3)).mp
  nlinarith [show (A * V) ^ 4 = (V * A ^ 4) * V ^ 3 by ring]

/-- Both actual errors, divided by their own Euler product. No density
estimate is an input; `hA` is an ordinary interval-product bound. -/
theorem smallDensityDefects_le_normalized_product (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {g : ℕ → ℝ} (ps : List ℕ) {A : ℝ}
    (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p ∈ geometricSmallPrimes P D ε)
    (hg : ∀ p ∈ ps, 0 ≤ g p ∧ g p < 1)
    (hA : (∏ p ∈ ps.toFinset, (1 - g p))⁻¹ ≤ A) :
    lowerDensityDefect (D ^ ε) g ps ≤
        (∏ p ∈ ps.toFinset, (1 - g p)) *
          (Real.exp (3 - 1 / ε) / 4 * (A ^ 4 - 1)) ∧
    upperDensityDefect (D ^ ε) g ps ≤
        (∏ p ∈ ps.toFinset, (1 - g p)) *
          (Real.exp (3 - 1 / ε) / 4 * (A ^ 4 - 1)) := by
  have ht := tiltedProduct_le_euler_mul_fourth ps.toFinset
    (fun p hp => hg p (List.mem_toFinset.mp hp)) hA
  have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right ht
    (∏ p ∈ ps.toFinset, (1 - g p)))
    (div_nonneg (Real.exp_pos (3 - 1 / ε)).le (by norm_num : (0 : ℝ) ≤ 4))
  have hl := lowerDensityDefect_le_tilt P hD hε ps hnd hps
    (fun p hp => ⟨(hg p hp).1, (hg p hp).2.le⟩)
  have hu := upperDensityDefect_le_tilt P hD hε ps hnd hps
    (fun p hp => ⟨(hg p hp).1, (hg p hp).2.le⟩)
  constructor <;> nlinarith

/-- The finite-carrier form of I80 (1), with the same constant `K`.
The left endpoint is closed and the right endpoint is strict. -/
def DimensionOneProductBound (P : Finset ℕ) (g : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ w z : ℝ, 2 ≤ w → w < z →
    (∏ p ∈ P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - g p)⁻¹) ≤ Real.log z / Real.log w * (1 + K / Real.log w)

theorem dimensionOne_smallInterval_inverseProduct (P : Finset ℕ)
    {D ε w K : ℝ} {g : ℕ → ℝ} (hdim : DimensionOneProductBound P g K)
    (hw : 2 ≤ w) (hwu : w < D ^ (ε ^ 2)) :
    (∏ p ∈ (geometricSmallPrimes P D ε).filter (fun p : ℕ => w ≤ (p : ℝ)),
      (1 - g p))⁻¹ ≤
        Real.log (D ^ (ε ^ 2)) / Real.log w * (1 + K / Real.log w) := by
  have heq : (geometricSmallPrimes P D ε).filter (fun p : ℕ => w ≤ (p : ℝ)) =
      P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < D ^ (ε ^ 2)) := by
    ext p
    simp only [geometricSmallPrimes, Finset.mem_filter]
    tauto
  rw [heq, ← Finset.prod_inv_distrib]
  exact hdim w (D ^ (ε ^ 2)) hw hwu

/-- An actual normalized analytic bound for both interval errors.
For `w = 2` its logarithmic factor grows with `D`; no full fundamental
lemma is inferred from that specialization. -/
theorem smallIntervalDensityDefects_le_dimensionOne (P : Finset ℕ)
    {D ε w K : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) {g : ℕ → ℝ}
    (hg : ∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) (hw : 2 ≤ w) (hwu : w < D ^ (ε ^ 2)) :
    let B := (geometricSmallPrimes P D ε).filter (fun p : ℕ => w ≤ (p : ℝ))
    let A := Real.log (D ^ (ε ^ 2)) / Real.log w * (1 + K / Real.log w)
    lowerDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) ≤
        (∏ p ∈ B, (1 - g p)) * (Real.exp (3 - 1 / ε) / 4 * (A ^ 4 - 1)) ∧
    upperDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) ≤
        (∏ p ∈ B, (1 - g p)) * (Real.exp (3 - 1 / ε) / 4 * (A ^ 4 - 1)) := by
  dsimp only
  let B := (geometricSmallPrimes P D ε).filter (fun p : ℕ => w ≤ (p : ℝ))
  have hB : ∀ p ∈ B.sort (· ≤ ·), p ∈ geometricSmallPrimes P D ε := by
    intro p hp
    exact (Finset.mem_filter.mp (show p ∈ B by simpa using hp)).1
  simpa only [Finset.sort_toFinset] using
    smallDensityDefects_le_normalized_product P hD hε (B.sort (· ≤ ·))
      (B.sort_nodup _) hB (fun p hp => hg p (hB p hp))
      (by simpa only [Finset.sort_toFinset] using
        dimensionOne_smallInterval_inverseProduct P hdim hw hwu)

/-- Uniform exponential suppression on a logarithmically short interval.
The explicit conditions retain the original `K`: they are satisfied by
`w = sqrt u` once `u ≥ 4` and `log u ≥ 2 K`. -/
theorem smallIntervalDensityDefects_le_exp (P : Finset ℕ)
    {D ε w K : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) {g : ℕ → ℝ}
    (hg : ∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) (hw : 2 ≤ w) (hwu : w < D ^ (ε ^ 2))
    (hK0 : 0 ≤ K) (hK : K ≤ Real.log w)
    (hratio : Real.log (D ^ (ε ^ 2)) ≤ 2 * Real.log w) :
    let B := (geometricSmallPrimes P D ε).filter (fun p : ℕ => w ≤ (p : ℝ))
    lowerDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) ≤
        (∏ p ∈ B, (1 - g p)) * (255 / 4 * Real.exp 3 * Real.exp (-(1 / ε))) ∧
    upperDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) ≤
        (∏ p ∈ B, (1 - g p)) * (255 / 4 * Real.exp 3 * Real.exp (-(1 / ε))) := by
  dsimp only
  let B := (geometricSmallPrimes P D ε).filter (fun p : ℕ => w ≤ (p : ℝ))
  have hlog : 0 < Real.log w := Real.log_pos (by linarith)
  have hratio' : Real.log (D ^ (ε ^ 2)) / Real.log w ≤ 2 :=
    (div_le_iff₀ hlog).mpr hratio
  have hK' : 1 + K / Real.log w ≤ 2 := by
    have := (div_le_one hlog).mpr hK
    linarith
  have hA : (∏ p ∈ B, (1 - g p))⁻¹ ≤ (4 : ℝ) :=
    (dimensionOne_smallInterval_inverseProduct P hdim hw hwu).trans (by
      calc
        Real.log (D ^ (ε ^ 2)) / Real.log w * (1 + K / Real.log w) ≤ 2 * 2 :=
          mul_le_mul hratio' hK' (by positivity) (by norm_num)
        _ = 4 := by norm_num)
  have hB : ∀ p ∈ B.sort (· ≤ ·), p ∈ geometricSmallPrimes P D ε := by
    intro p hp
    exact (Finset.mem_filter.mp (show p ∈ B by simpa using hp)).1
  have hm := smallDensityDefects_le_normalized_product P hD hε (B.sort (· ≤ ·))
    (B.sort_nodup _) hB (fun p hp => hg p (hB p hp))
    (by simpa only [Finset.sort_toFinset] using hA)
  have hexp : Real.exp (3 - 1 / ε) = Real.exp 3 * Real.exp (-(1 / ε)) := by
    rw [sub_eq_add_neg, Real.exp_add]
  simp only [Finset.sort_toFinset, hexp] at hm
  have heq : Real.exp 3 * Real.exp (-(1 / ε)) / 4 * ((4 : ℝ) ^ 4 - 1) =
      255 / 4 * Real.exp 3 * Real.exp (-(1 / ε)) := by ring
  rw [heq] at hm
  exact hm

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
