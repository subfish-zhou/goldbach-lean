import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# The global Buchstab delay function

Continuous integral approximants stabilize on successively larger half-lines.
Their locally stable value defines a function on all of `ℝ`; on `[1, ∞)` it
satisfies the initial condition and the Buchstab delay differential equation.
The extension below `1` is only used to keep the approximants globally continuous.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace LiLiuPrereqBuchstab

/-- The method-of-steps approximants, with harmless continuous cutoffs below
the interval on which the Buchstab equation is prescribed. -/
noncomputable def approx : ℕ → ℝ → ℝ
  | 0, u => 1 / max 1 u
  | n + 1, u =>
      (1 + ∫ t in (2 : ℝ)..max 2 u, approx n (t - 1)) / max 1 u

theorem continuous_approx (n : ℕ) : Continuous (approx n) := by
  have hd : Continuous (fun u : ℝ => max 1 u) := continuous_const.max continuous_id
  have hn : ∀ u : ℝ, max 1 u ≠ 0 := by
    intro u
    have h := le_max_left (1 : ℝ) u
    linarith
  induction n with
  | zero => exact continuous_const.div hd hn
  | succ n ih =>
      have hc : Continuous (fun t : ℝ => approx n (t - 1)) :=
        ih.comp (continuous_id.sub continuous_const)
      have hp : Continuous (fun u : ℝ => ∫ t in (2 : ℝ)..u, approx n (t - 1)) :=
        continuous_iff_continuousAt.mpr
          (fun u => (hc.integral_hasStrictDerivAt 2 u).hasDerivAt.continuousAt)
      exact (continuous_const.add
        (hp.comp (continuous_const.max continuous_id))).div hd hn

/-- One more integral step makes no change below its stabilization threshold. -/
theorem approx_succ_eq (n : ℕ) (u : ℝ) (hu : u ≤ (n : ℝ) + 2) :
    approx (n + 1) u = approx n u := by
  induction n generalizing u with
  | zero =>
      have hu' : u ≤ 2 := by simpa using hu
      simp [approx, max_eq_left hu']
  | succ n ih =>
      have hi :
          (∫ t in (2 : ℝ)..max 2 u, approx (n + 1) (t - 1)) =
            ∫ t in (2 : ℝ)..max 2 u, approx n (t - 1) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (le_max_left (2 : ℝ) u)] at ht
        apply ih
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hm : max 2 u ≤ (n : ℝ) + 3 := by
          apply max_le
          · linarith
          · push_cast at hu
            linarith
        linarith [ht.2]
      simpa only [approx] using congrArg (fun z : ℝ => (1 + z) / max 1 u) hi

/-- Any later approximant agrees on the earlier stabilization half-line. -/
theorem approx_eq_of_le {n m : ℕ} (hnm : n ≤ m) (u : ℝ)
    (hu : u ≤ (n : ℝ) + 2) : approx m u = approx n u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      rw [approx_succ_eq m u (by linarith), ih]

/-- The actual global Buchstab function, obtained by locally stabilized
method-of-steps approximants, rather than a fixed finite truncation. -/
noncomputable def buchstab (u : ℝ) : ℝ := approx ⌈u⌉₊ u

theorem buchstab_eq_approx (n : ℕ) (u : ℝ) (hu : u ≤ (n : ℝ) + 2) :
    buchstab u = approx n u := by
  unfold buchstab
  rcases le_total n ⌈u⌉₊ with h | h
  · exact approx_eq_of_le h u hu
  · symm
    apply approx_eq_of_le h
    have hceil : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    linarith

/-- Locally the glued function is a single continuous approximant. -/
theorem buchstab_eventuallyEq_approx (n : ℕ) (u : ℝ) (hu : u < (n : ℝ) + 2) :
    buchstab =ᶠ[𝓝 u] approx n := by
  filter_upwards [eventually_lt_nhds hu] with x hx
  exact buchstab_eq_approx n x hx.le

theorem continuous_buchstab : Continuous buchstab := by
  apply continuous_iff_continuousAt.mpr
  intro u
  obtain ⟨n, hn⟩ := exists_nat_gt u
  exact (continuous_approx n).continuousAt.congr_of_eventuallyEq
    (buchstab_eventuallyEq_approx n u (by linarith))

theorem continuousOn_buchstab : ContinuousOn buchstab (Ici 1) :=
  continuous_buchstab.continuousOn

/-- The prescribed initial condition, including both endpoints. -/
theorem buchstab_eq_one_div {u : ℝ} (hu₁ : 1 ≤ u) (hu₂ : u ≤ 2) :
    buchstab u = 1 / u := by
  rw [buchstab_eq_approx 0 u (by simpa using hu₂)]
  simp [approx, max_eq_right hu₁]

/-- The global integral equation; there is no upper bound on `u`. -/
theorem mul_buchstab_eq_integral {u : ℝ} (hu : 2 ≤ u) :
    u * buchstab u = 1 + ∫ t in (2 : ℝ)..u, buchstab (t - 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  have hi :
      (∫ t in (2 : ℝ)..u, approx n (t - 1)) =
        ∫ t in (2 : ℝ)..u, buchstab (t - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu] at ht
    exact (buchstab_eq_approx n (t - 1) (by linarith [ht.2])).symm
  have hstage : u ≤ ((n + 1 : ℕ) : ℝ) + 2 := by
    push_cast
    linarith
  have hu₁ : 1 ≤ u := by linarith
  have hu₀ : u ≠ 0 := by linarith
  rw [buchstab_eq_approx (n + 1) u hstage, approx,
    max_eq_right hu, max_eq_right hu₁, hi]
  field_simp

/-- The Buchstab delay differential equation at every real `u > 2`. -/
theorem hasDerivAt_mul_buchstab {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun v : ℝ => v * buchstab v) (buchstab (u - 1)) u := by
  have hc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
    continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hd := ((hc.integral_hasStrictDerivAt 2 u).hasDerivAt).const_add 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact mul_buchstab_eq_integral hv.le

end LiLiuPrereqBuchstab