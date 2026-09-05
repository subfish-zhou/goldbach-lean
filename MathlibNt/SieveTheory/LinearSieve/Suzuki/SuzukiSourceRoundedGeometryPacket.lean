import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaGeometryEventually
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiNatCeilPowerCarrier

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Every size and cutoff-geometry premise used by the double-rounded Case-II
endpoint, after substituting Suzuki's moving source cutoff.  The extra fields
`hyceil`, `hyrzr`, and `hzr2` make explicit the three immediate geometric facts
that consumers otherwise have to reconstruct from the displayed premises. -/
structure SourceRoundedGeometryPacket
    (S : BoundingSieve) (D y z : ℕ) (d s : ℝ) : Prop where
  h3σ : 3 ≤ sourceSigma (D : ℝ) d
  hD : Real.exp 1 ≤ (D : ℝ)
  hDlarge : 2 * Real.log 2 ≤ Real.log (D : ℝ)
  hwy : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤
    (D : ℝ) ^ (1 / (3 : ℝ))
  hy2 : 2 ≤ (y : ℝ)
  hyr2 : 2 ≤ (D : ℝ) ^ (1 / (3 : ℝ))
  hw2 : 2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)
  hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D
  hyceil : y = ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
  hyrzr : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (D : ℝ) ^ (1 / s)
  hyz : y ≤ z
  hyLower : (y - 1) ^ 3 < D
  hyUpper : D ≤ y ^ 3
  hyDhalf : (y : ℝ) ≤ (D : ℝ) / 2
  hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊
  hzr2 : 2 ≤ (D : ℝ) ^ (1 / s)
  h3dlog : (3 : ℝ) ^ d ≤ Real.log (D : ℝ)

/-- The natural ceiling of the real cube root satisfies the strict lower and
weak upper cubic bracket.  This is the direction needed to manufacture the
rounded natural cutoff, rather than consume a pre-existing bracket. -/
theorem natCeil_cuberoot_cubeBracket (D : ℕ) (hD : 0 < D) :
    let y := ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
    (y - 1) ^ 3 < D ∧ D ≤ y ^ 3 := by
  let r : ℝ := (D : ℝ) ^ (1 / (3 : ℝ))
  let y : ℕ := ⌈r⌉₊
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hr : 0 < r := Real.rpow_pos_of_pos hDR _
  have hypos : 0 < y := by
    dsimp [y]
    exact Nat.ceil_pos.mpr hr
  have hpred : (((y - 1 : ℕ) : ℝ)) < r := by
    have hceil : (y : ℝ) < r + 1 := by
      simpa [y] using Nat.ceil_lt_add_one hr.le
    rw [Nat.cast_sub (by omega : 1 ≤ y)]
    norm_num
    linarith
  have hrootle : r ≤ (y : ℝ) := by
    dsimp [y]
    exact Nat.le_ceil r
  have hlowerR : (((y - 1 : ℕ) : ℝ) ^ (3 : ℕ)) < (D : ℝ) := by
    have hiff := Real.lt_rpow_inv_iff_of_pos
      (x := ((y - 1 : ℕ) : ℝ)) (y := (D : ℝ)) (z := (3 : ℝ))
      (by positivity) hDR.le (by norm_num)
    norm_num [one_div, r] at hiff hpred ⊢
    exact hiff.mp hpred
  have hupperR : (D : ℝ) ≤ (y : ℝ) ^ (3 : ℕ) := by
    have hiff := Real.rpow_inv_le_iff_of_pos
      (x := (D : ℝ)) (y := (y : ℝ)) (z := (3 : ℝ))
      hDR.le (by positivity) (by norm_num)
    norm_num [one_div, r] at hiff hrootle ⊢
    exact hiff.mp hrootle
  exact ⟨by exact_mod_cast hlowerR, by exact_mod_cast hupperR⟩

/-- A single threshold, depending only on `d`, supplies all moving
source-`sigma`, logarithmic-size, and double-rounded cutoff geometry uniformly
in the sieve, in the natural parameter `D`, and in every `1 < s ≤ 3`.

The cutoffs are fixed in the conclusion as
`y = ceil(D^(1/3))` and `z = ceil(D^(1/s))`; thus no perfect-power equality is
assumed and no size premise remains for downstream induction/source consumers. -/
theorem exists_sourceSigma_doubleRounded_geometry_threshold
    (d : ℝ) (hd : 1 < d) :
    ∃ D0 : ℝ, 1 < D0 ∧
      ∀ (S : BoundingSieve) (D : ℕ), D0 ≤ (D : ℝ) →
      ∀ s : ℝ, 1 < s → s ≤ 3 →
        SourceRoundedGeometryPacket S D
          ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
          ⌈(D : ℝ) ^ (1 / s)⌉₊ d s := by
  obtain ⟨Dσ, hDσ, hσ⟩ := exists_sourceSigma_geometry_threshold d hd
  let Elog : ℝ := Real.exp (2 * Real.log 2)
  let Ed : ℝ := Real.exp ((3 : ℝ) ^ d)
  let Dsize : ℝ := max 8 (max (Real.exp 1) (max Elog Ed))
  let D0 : ℝ := max Dσ Dsize
  have hD0 : 1 < D0 := hDσ.trans_le (le_max_left Dσ Dsize)
  refine ⟨D0, hD0, ?_⟩
  intro S D hDD0 s hs1 hs3
  have hDσD : Dσ ≤ (D : ℝ) :=
    (le_max_left Dσ Dsize).trans hDD0
  have hDsizeD : Dsize ≤ (D : ℝ) :=
    (le_max_right Dσ Dsize).trans hDD0
  have hD8R : (8 : ℝ) ≤ (D : ℝ) :=
    (le_max_left (8 : ℝ) (max (Real.exp 1) (max Elog Ed))).trans hDsizeD
  have hD8 : 8 ≤ D := by exact_mod_cast hD8R
  have hDpos : 0 < D := by omega
  have hExpOne : Real.exp 1 ≤ (D : ℝ) :=
    ((le_max_left (Real.exp 1) (max Elog Ed)).trans
      (le_max_right (8 : ℝ) _)).trans hDsizeD
  have hElog : Elog ≤ (D : ℝ) :=
    (le_max_left Elog Ed).trans <|
      (le_max_right (Real.exp 1) (max Elog Ed)).trans <|
        (le_max_right (8 : ℝ) (max (Real.exp 1) (max Elog Ed))).trans hDsizeD
  have hEd : Ed ≤ (D : ℝ) :=
    (le_max_right Elog Ed).trans <|
      (le_max_right (Real.exp 1) (max Elog Ed)).trans <|
        (le_max_right (8 : ℝ) (max (Real.exp 1) (max Elog Ed))).trans hDsizeD
  have hDrealpos : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hDlarge : 2 * Real.log 2 ≤ Real.log (D : ℝ) := by
    apply (Real.le_log_iff_exp_le hDrealpos).2
    simpa [Elog] using hElog
  have h3dlog : (3 : ℝ) ^ d ≤ Real.log (D : ℝ) := by
    apply (Real.le_log_iff_exp_le hDrealpos).2
    simpa [Ed] using hEd
  obtain ⟨h3σ, hwy, hw2⟩ := hσ (D : ℝ) hDσD
  let y : ℕ := ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hs : 0 < s := zero_lt_one.trans hs1
  have hyceil : y = ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊ := rfl
  have hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊ := rfl
  obtain ⟨hyLower, hyUpper⟩ := natCeil_cuberoot_cubeBracket D hDpos
  have hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D :=
    supported_cube_lt_of_eq_natCeil_cuberoot S hDpos hyceil
  have hyrzr : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (D : ℝ) ^ (1 / s) :=
    rpow_one_div_mono_of_le (by exact_mod_cast (show 1 ≤ D by omega)) hs hs3
  have hyz : y ≤ z :=
    caseII_hyz_of_natCeil_powerCutoffs (show 1 ≤ D by omega) hs hs3 hyceil hzceil
  obtain ⟨_, _, hy2, hyDhalf⟩ :=
    SwitchingPrinciple.SuzukiLemma144KappaOne.nat_cubic_cutoff_real_geometry
      hD8 hyLower hyUpper
  have hyr2 : 2 ≤ (D : ℝ) ^ (1 / (3 : ℝ)) := by
    have h8root : (8 : ℝ) ^ (1 / (3 : ℝ)) = 2 := by
      calc
        (8 : ℝ) ^ (1 / (3 : ℝ)) = (((2 : ℝ) ^ (3 : ℕ)) ^ (1 / (3 : ℝ))) := by
          norm_num
        _ = 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    rw [← h8root]
    exact Real.rpow_le_rpow (by norm_num) hD8R (by norm_num)
  have hzr2 : 2 ≤ (D : ℝ) ^ (1 / s) := hyr2.trans hyrzr
  exact {
    h3σ := h3σ
    hD := hExpOne
    hDlarge := hDlarge
    hwy := hwy
    hy2 := hy2
    hyr2 := hyr2
    hw2 := hw2
    hycube := hycube
    hyceil := hyceil
    hyrzr := hyrzr
    hyz := hyz
    hyLower := hyLower
    hyUpper := hyUpper
    hyDhalf := hyDhalf
    hzceil := hzceil
    hzr2 := hzr2
    h3dlog := h3dlog }


end MathlibNt.SieveTheory
