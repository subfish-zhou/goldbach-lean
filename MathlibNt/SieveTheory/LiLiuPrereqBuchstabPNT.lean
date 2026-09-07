import PrimeNumberTheoremAnd.Consequences
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# A monotone error envelope for the actual prime counting function

The ordinary PNT is reused from the byte-frozen nine-module source closure.
The comparator is `t / log t`, so Abel summation against its derivative
has an additional explicit `1 / log t ^ 2` term.
-/

set_option autoImplicit false

open Filter Set Asymptotics
open scoped Topology

namespace LiLiuPrereqBuchstab

noncomputable def primePi (t : ℝ) : ℝ := Nat.primeCounting ⌊t⌋₊

noncomputable def primeRelativeError (t : ℝ) : ℝ :=
  |primePi t / (t / Real.log t) - 1|

theorem primePi_asymptotic :
    primePi ~[atTop] (fun t => t / Real.log t) := pi_alt'

theorem tendsto_primeRelativeError :
    Tendsto primeRelativeError atTop (𝓝 0) := by
  have hn : ∀ᶠ t : ℝ in atTop, t / Real.log t ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact (div_pos (by linarith) (Real.log_pos ht)).ne'
  have h := (isEquivalent_iff_tendsto_one hn).mp primePi_asymptotic
  change Tendsto (fun t => |primePi t / (t / Real.log t) - 1|) atTop (𝓝 0)
  simpa only [Pi.div_apply, sub_self, abs_zero] using
    (h.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs

private theorem exists_primeError_start :
    ∃ Y : ℝ, 3 ≤ Y ∧ Real.exp 1 ≤ Y ∧
      ∀ t ≥ Y, primeRelativeError t ≤ 1 := by
  obtain ⟨Y, hY⟩ := eventually_atTop.1
    (tendsto_primeRelativeError.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 3 (max (Real.exp 1) Y), le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro t ht
  exact (hY t ((le_max_right _ _).trans ((le_max_right _ _).trans ht))).le

noncomputable def primeErrorStart : ℝ := Classical.choose exists_primeError_start

theorem primeErrorStart_spec :
    3 ≤ primeErrorStart ∧ Real.exp 1 ≤ primeErrorStart ∧
      ∀ t ≥ primeErrorStart, primeRelativeError t ≤ 1 :=
  Classical.choose_spec exists_primeError_start

/-- A genuine tail supremum, clamped below a fixed PNT threshold. -/
noncomputable def primeErrorEnvelope (y : ℝ) : ℝ :=
  sSup (primeRelativeError '' Ici (max primeErrorStart y))

private theorem primeError_tail_nonempty (y : ℝ) :
    (primeRelativeError '' Ici (max primeErrorStart y)).Nonempty :=
  ⟨_, ⟨max primeErrorStart y, mem_Ici.mpr le_rfl, rfl⟩⟩

private theorem primeError_tail_bddAbove (y : ℝ) :
    BddAbove (primeRelativeError '' Ici (max primeErrorStart y)) := by
  refine ⟨1, ?_⟩
  rintro r ⟨t, ht, rfl⟩
  exact primeErrorStart_spec.2.2 t ((le_max_left _ _).trans ht)

theorem primeRelativeError_le_envelope {y t : ℝ}
    (ht : max primeErrorStart y ≤ t) :
    primeRelativeError t ≤ primeErrorEnvelope y :=
  le_csSup (primeError_tail_bddAbove y) ⟨t, ht, rfl⟩

theorem primeErrorEnvelope_nonneg (y : ℝ) : 0 ≤ primeErrorEnvelope y :=
  (abs_nonneg _).trans (primeRelativeError_le_envelope (y := y) le_rfl)

theorem primeErrorEnvelope_le_one (y : ℝ) : primeErrorEnvelope y ≤ 1 := by
  apply csSup_le (primeError_tail_nonempty y)
  rintro r ⟨t, ht, rfl⟩
  exact primeErrorStart_spec.2.2 t ((le_max_left _ _).trans ht)

theorem antitone_primeErrorEnvelope : Antitone primeErrorEnvelope := by
  intro y z hyz
  apply csSup_le (primeError_tail_nonempty z)
  rintro r ⟨t, ht, rfl⟩
  exact primeRelativeError_le_envelope ((max_le_max_left _ hyz).trans ht)

theorem tendsto_primeErrorEnvelope :
    Tendsto primeErrorEnvelope atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun y => ha.trans_le (primeErrorEnvelope_nonneg y)
  · intro b hb
    obtain ⟨Y, hY⟩ := eventually_atTop.1
      (tendsto_primeRelativeError.eventually (gt_mem_nhds (half_pos hb)))
    filter_upwards [eventually_ge_atTop Y] with y hy
    have hle : primeErrorEnvelope y ≤ b / 2 := by
      apply csSup_le (primeError_tail_nonempty y)
      rintro r ⟨t, ht, rfl⟩
      exact (hY t (hy.trans ((le_max_right _ _).trans ht))).le
    exact hle.trans_lt (half_lt_self hb)

/-- One threshold controls the actual PNT error at every larger real point. -/
theorem primePi_error_le {y t : ℝ}
    (hy : primeErrorStart ≤ y) (hyt : y ≤ t) :
    |primePi t - t / Real.log t| ≤ primeErrorEnvelope y * (t / Real.log t) := by
  have ht : 1 < t := lt_of_lt_of_le (by linarith [primeErrorStart_spec.1]) (hy.trans hyt)
  have hm : 0 < t / Real.log t := div_pos (by linarith) (Real.log_pos ht)
  have h := mul_le_mul_of_nonneg_right
    (primeRelativeError_le_envelope ((max_le hy le_rfl).trans hyt)) hm.le
  have he : primeRelativeError t * (t / Real.log t) =
      |primePi t - t / Real.log t| := by
    unfold primeRelativeError
    conv_lhs => rhs; rw [← abs_of_pos hm]
    rw [← abs_mul]
    congr 1
    rw [sub_mul, div_mul_cancel₀ _ hm.ne', one_mul]
  rwa [he] at h

theorem primePi_le_two_mul {t : ℝ} (ht : primeErrorStart ≤ t) :
    primePi t ≤ 2 * (t / Real.log t) := by
  have ht1 : 1 < t := by linarith [primeErrorStart_spec.1]
  have hm : 0 ≤ t / Real.log t := (div_pos (by linarith) (Real.log_pos ht1)).le
  have h := (le_abs_self (primePi t - t / Real.log t)).trans (primePi_error_le ht le_rfl)
  have hle := mul_le_mul_of_nonneg_right (primeErrorEnvelope_le_one t) hm
  linarith

/-- The elementary monotonicity needed for the prime-weighted boundary error. -/
theorem div_log_mono {s t : ℝ} (hs : primeErrorStart ≤ s) (hst : s ≤ t) :
    s / Real.log s ≤ t / Real.log t := by
  have hs1 : 1 < s := by linarith [primeErrorStart_spec.1]
  have ht1 : 1 < t := hs1.trans_le hst
  have h := Real.log_div_self_antitoneOn
    (primeErrorStart_spec.2.1.trans hs)
    (primeErrorStart_spec.2.1.trans (hs.trans hst)) hst
  have hlogs := Real.log_pos hs1
  have hlogt := Real.log_pos ht1
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  apply (div_le_div_iff₀ hlogs hlogt).2
  have hh := (div_le_div_iff₀ ht0 hs0).1 h
  nlinarith

end LiLiuPrereqBuchstab