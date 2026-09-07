import MathlibNt.SieveTheory.LiLiuPrereqWFRounding
import MathlibNt.SieveTheory.LiLiuPrereqWFZeroDensity

/-!
# Parameters for the rounded, moving-range density estimate

The coordinate depends on `D, ε` only, never on a prime carrier, density,
or truncation depth. Increasing the product constant to `max K 2` incurs
the displayed absolute factor in `exp (sqrt K)`.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open Finset
open scoped Classical

theorem dimensionOneProductBound_mono {P : Finset ℕ} {g : ℕ → ℝ} {K K' : ℝ}
    (h : DimensionOneProductBound P g K) (hKK : K ≤ K') :
    DimensionOneProductBound P g K' := by
  intro w z hw hwz
  have hwlog : 0 < Real.log w := Real.log_pos (by linarith)
  have hzlog : 0 ≤ Real.log z := (Real.log_pos (by linarith)).le
  exact (h w z hw hwz).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right hKK hwlog.le))
      (div_nonneg hzlog hwlog.le))

theorem exp_sqrt_max_two_le (K : ℝ) :
    Real.exp (Real.sqrt (max K 2)) ≤
      Real.exp (Real.sqrt 2) * Real.exp (Real.sqrt K) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rcases le_total K 2 with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg K)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg 2)

theorem log_ceil_rpow_bounds {D ε : ℝ} (hD : 2 ≤ D)
    (hlarge : Real.log 2 ≤ ε * Real.log D) :
    ε * Real.log D ≤ Real.log (⌈D ^ ε⌉₊ : ℝ) ∧
      Real.log (⌈D ^ ε⌉₊ : ℝ) ≤ 2 * (ε * Real.log D) := by
  have hD0 : 0 < D := by linarith
  have hL0 : 0 < D ^ ε := Real.rpow_pos_of_pos hD0 ε
  have hlogL : Real.log (D ^ ε) = ε * Real.log D := Real.log_rpow hD0 ε
  have hL2 : 2 ≤ D ^ ε := by
    apply (Real.log_le_log_iff (by norm_num) hL0).mp
    simpa only [hlogL] using hlarge
  have hR0 : 0 < (⌈D ^ ε⌉₊ : ℝ) := hL0.trans_le (Nat.le_ceil _)
  have hR2 : (⌈D ^ ε⌉₊ : ℝ) ≤ (D ^ ε) ^ 2 := by
    have hc := Nat.ceil_lt_add_one hL0.le
    nlinarith
  constructor
  · rw [← hlogL]
    exact Real.log_le_log hL0 (Nat.le_ceil _)
  · calc
      Real.log (⌈D ^ ε⌉₊ : ℝ) ≤ Real.log ((D ^ ε) ^ 2) :=
        Real.log_le_log hR0 hR2
      _ = 2 * (ε * Real.log D) := by rw [Real.log_pow, hlogL]; norm_num

theorem small_roundedSieveCoordinate_bounds {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hlarge : Real.log 2 ≤ ε * Real.log D) :
    1 / ε ≤ roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2)) ∧
      roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2)) ≤ 2 / ε := by
  have hdlog : 0 < Real.log D := Real.log_pos (by linarith)
  have hden : 0 < ε ^ 2 * Real.log D := mul_pos (sq_pos_of_pos hε) hdlog
  obtain ⟨hlo, hup⟩ := log_ceil_rpow_bounds hD hlarge
  unfold roundedSieveCoordinate
  rw [Real.log_rpow (by linarith : 0 < D)]
  constructor
  · apply (le_div_iff₀ hden).mpr
    calc
      1 / ε * (ε ^ 2 * Real.log D) = ε * Real.log D := by field_simp
      _ ≤ Real.log (⌈D ^ ε⌉₊ : ℝ) := hlo
  · apply (div_le_iff₀ hden).mpr
    calc
      Real.log (⌈D ^ ε⌉₊ : ℝ) ≤ 2 * (ε * Real.log D) := hup
      _ = 2 / ε * (ε ^ 2 * Real.log D) := by field_simp

/-- A fixed numerical threshold gives the power budget uniformly in all
subsequently chosen sieve data and depths. -/
theorem small_rounded_power_budget {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε)
    (hlarge : max (Real.log 2) ((2 / ε) ^ 13) ≤ ε * Real.log D) :
    (roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))) ^ 13 ≤
      Real.log (⌈D ^ ε⌉₊ : ℝ) := by
  have hlog := (le_max_left _ _).trans hlarge
  obtain ⟨hlo, hup⟩ := small_roundedSieveCoordinate_bounds hD hε hlog
  calc
    (roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))) ^ 13 ≤ (2 / ε) ^ 13 :=
      pow_le_pow_left₀ ((by positivity : (0 : ℝ) ≤ 1 / ε).trans hlo) hup 13
    _ ≤ ε * Real.log D := (le_max_right _ _).trans hlarge
    _ ≤ Real.log (⌈D ^ ε⌉₊ : ℝ) := (log_ceil_rpow_bounds hD hlog).1

/-- The precise `s` in the moving-range envelope is retained. -/
theorem moving_envelope_le_exp_one {t s : ℝ} (hs : 0 < s) (ht : s ^ 13 ≤ t) :
    (1 + s ^ 12 / t) ^ s ≤ Real.exp 1 := by
  have ht0 : 0 < t := lt_of_lt_of_le (pow_pos hs 13) ht
  have hdiv : s ^ 12 / t ≤ 1 / s := by
    apply (div_le_div_iff₀ ht0 hs).mpr
    simpa only [one_mul, ← pow_succ] using ht
  have hbase : 1 + s ^ 12 / t ≤ Real.exp (1 / s) :=
    (add_le_add le_rfl hdiv).trans (by
      simpa only [add_comm] using Real.add_one_le_exp (1 / s))
  calc
    (1 + s ^ 12 / t) ^ s ≤ (Real.exp (1 / s)) ^ s :=
      Real.rpow_le_rpow (by positivity) hbase hs.le
    _ = Real.exp 1 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      field_simp

/-- The actual shape of the source's moving endpoint, with `d = 12`. -/
theorem moving_range_of_power_budget {R s : ℝ} (hR : 0 < R) (hs : 1 ≤ s)
    (hbudget : s ^ 13 ≤ Real.log R) (hlog : Real.exp 1 ≤ Real.log R) :
    s ≤ (Real.log R) ^ (1 / 12 : ℝ) * Real.log (Real.log (27 * R)) := by
  have hs0 : 0 ≤ s := by linarith
  have hpow : s ^ 12 ≤ s ^ 13 := by
    simpa only [mul_one, ← pow_succ] using
      mul_le_mul_of_nonneg_left hs (pow_nonneg hs0 12)
  have hroot := Real.rpow_le_rpow (pow_nonneg hs0 12) (hpow.trans hbudget)
    (by norm_num : (0 : ℝ) ≤ 1 / 12)
  rw [← Real.rpow_natCast_mul hs0 12 (1 / 12)] at hroot
  norm_num at hroot
  have hlog27 : Real.log R ≤ Real.log (27 * R) :=
    Real.log_le_log hR (by linarith)
  have hloglog : 1 ≤ Real.log (Real.log (27 * R)) := by
    have hh := Real.log_le_log (Real.exp_pos 1) (hlog.trans hlog27)
    simpa only [Real.log_exp] using hh
  exact hroot.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hloglog
      (Real.rpow_nonneg (lt_of_lt_of_le (Real.exp_pos 1) hlog).le _))

/-- Explicit threshold, before all carriers, densities, and depths.
Both the source domain and its envelope use the rounded coordinate. -/
theorem small_rounded_moving_range {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : max (max (Real.log 2) ((2 / ε) ^ 13)) (Real.exp 1) ≤
      ε * Real.log D) :
    let R : ℝ := (⌈D ^ ε⌉₊ : ℝ)
    let s := roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))
    8 < s ∧
      s ≤ (Real.log R) ^ (1 / 12 : ℝ) * Real.log (Real.log (27 * R)) ∧
      (1 + s ^ 12 / Real.log R) ^ s ≤ Real.exp 1 := by
  dsimp only
  have hb := (le_max_left _ _).trans hlarge
  have hl := (le_max_left _ _).trans hb
  obtain ⟨hslo, _⟩ := small_roundedSieveCoordinate_bounds hD hε hl
  have h8 : (8 : ℝ) < 1 / ε := (lt_div_iff₀ hε).mpr (by linarith)
  have hs8 := h8.trans_le hslo
  have hp := small_rounded_power_budget hD hε hb
  have hlog := ((le_max_right _ _).trans hlarge).trans
    (log_ceil_rpow_bounds hD hl).1
  refine ⟨hs8, ?_, moving_envelope_le_exp_one (by linarith) hp⟩
  exact moving_range_of_power_budget
    ((Real.rpow_pos_of_pos (by linarith : 0 < D) ε).trans_le (Nat.le_ceil _))
    (by linarith) hp hlog

theorem exists_small_rounded_moving_threshold {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      let R : ℝ := (⌈D ^ ε⌉₊ : ℝ)
      let s := roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))
      8 < s ∧
        s ≤ (Real.log R) ^ (1 / 12 : ℝ) * Real.log (Real.log (27 * R)) ∧
        (1 + s ^ 12 / Real.log R) ^ s ≤ Real.exp 1 := by
  let T := max (max (Real.log 2) ((2 / ε) ^ 13)) (Real.exp 1)
  refine ⟨max 2 (Real.exp (T / ε)), le_max_left _ _, ?_⟩
  intro D hD
  have hD2 : 2 ≤ D := (le_max_left _ _).trans hD
  have hlog := Real.log_le_log (Real.exp_pos (T / ε))
    ((le_max_right _ _).trans hD)
  rw [Real.log_exp] at hlog
  apply small_rounded_moving_range hD2 hε hεsmall
  exact (div_le_iff₀ hε).mp hlog |>.trans_eq (mul_comm _ _)

theorem small_rounded_decay_bounds {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hlarge : Real.log 2 ≤ ε * Real.log D) :
    Real.exp (-roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))) ≤
        Real.exp (-(1 / ε)) ∧
      (Real.log (⌈D ^ ε⌉₊ : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
        (ε * Real.log D) ^ (-(1 / 3 : ℝ)) := by
  constructor
  · exact Real.exp_le_exp.mpr
      (neg_le_neg (small_roundedSieveCoordinate_bounds hD hε hlarge).1)
  · exact Real.rpow_le_rpow_of_nonpos
      (mul_pos hε (Real.log_pos (by linarith)))
      (log_ceil_rpow_bounds hD hlarge).1 (by norm_num)

/-- Transport the two terms of the rounded producer error to the original
parameters. The constant is independent of `K`, `D`, and `ε`. -/
theorem small_rounded_error_bound (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε)
    (hlarge : Real.log 2 ≤ ε * Real.log D) :
    let s := roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))
    A * Real.exp (-s) +
        B * Real.exp (Real.sqrt (max K 2)) * Real.exp (-s) *
          (Real.log (⌈D ^ ε⌉₊ : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
      max A (B * Real.exp (Real.sqrt 2)) *
        (Real.exp (-(1 / ε)) +
          Real.exp (Real.sqrt K - 1 / ε) *
            (ε * Real.log D) ^ (-(1 / 3 : ℝ))) := by
  dsimp only
  obtain ⟨hdec, hlog⟩ := small_rounded_decay_bounds hD hε hlarge
  have hK := exp_sqrt_max_two_le K
  have hAC : A ≤ max A (B * Real.exp (Real.sqrt 2)) := le_max_left _ _
  have hBC : B * Real.exp (Real.sqrt 2) ≤
      max A (B * Real.exp (Real.sqrt 2)) := le_max_right _ _
  have hC : 0 ≤ max A (B * Real.exp (Real.sqrt 2)) := hA.trans hAC
  have hlog0 : 0 ≤ (Real.log (⌈D ^ ε⌉₊ : ℝ)) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_nonneg
      ((mul_pos hε (Real.log_pos (by linarith))).le.trans
        (log_ceil_rpow_bounds hD hlarge).1) _
  rw [mul_add, Real.exp_sub]
  apply add_le_add
  · exact mul_le_mul hAC hdec (Real.exp_pos _).le hC
  · calc
      B * Real.exp (Real.sqrt (max K 2)) *
          Real.exp (-roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))) *
          (Real.log (⌈D ^ ε⌉₊ : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
        B * (Real.exp (Real.sqrt 2) * Real.exp (Real.sqrt K)) *
          Real.exp (-(1 / ε)) * (ε * Real.log D) ^ (-(1 / 3 : ℝ)) := by
            apply mul_le_mul _ hlog hlog0
              (mul_nonneg (mul_nonneg hB (by positivity)) (Real.exp_pos _).le)
            exact mul_le_mul (mul_le_mul_of_nonneg_left hK hB) hdec
              (Real.exp_pos _).le (mul_nonneg hB (by positivity))
      _ = (B * Real.exp (Real.sqrt 2)) *
          (Real.exp (Real.sqrt K) / Real.exp (1 / ε)) *
          (ε * Real.log D) ^ (-(1 / 3 : ℝ)) := by
            rw [Real.exp_neg]
            ring
      _ ≤ _ := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBC (by positivity))
        exact Real.rpow_nonneg (mul_pos hε (Real.log_pos (by linarith))).le _

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
