import AnalyticNumberTheory.Sieve.PanMeanValueBody
import MathlibNt.SieveTheory.LiuTrueLiPan
import MathlibNt.SieveTheory.LiuPanPrincipalPNT

/-!
# Wu's real product endpoints

Wu (2004), printed p. 220, defines the prime count with `m * p ≤ y`
and `li(t) = ∫₂ᵗ du / log u`. The frozen Pan count has a natural endpoint.
These bridges retain the real argument of li and the coupled inverse residue.

The integral below is a total Lean expression. Analytic uses in this module
require its argument to be at least 2; no convention across the singularity
at 1 is inferred from totalization.
-/

namespace Wu2004MeanValue

open Finset
open scoped BigOperators
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

noncomputable section

def wuLi (t : ℝ) : ℝ := liuLogarithmicIntegral 0 t

def scaledPrimeSet (y : ℝ) (d b m : ℕ) : Finset ℕ :=
  (range (⌊y / m⌋₊ + 1)).filter
    (fun p => p.Prime ∧ m * p ≡ b [MOD d])

def scaledPrimeCount (y : ℝ) (d b m : ℕ) : ℕ :=
  (scaledPrimeSet y d b m).card

def ebar (y : ℝ) (d b m : ℕ) : ℝ :=
  (scaledPrimeCount y d b m : ℝ) - wuLi (y / m) / Nat.totient d

theorem mem_scaledPrimeSet {y : ℝ} {d b m p : ℕ}
    (hy : 0 ≤ y) (hm : 0 < m) :
    p ∈ scaledPrimeSet y d b m ↔
      p.Prime ∧ (m : ℝ) * p ≤ y ∧ m * p ≡ b [MOD d] := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [scaledPrimeSet, mem_filter, mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff (div_nonneg hy hmR.le)]
  rw [le_div_iff₀ hmR]
  simp only [mul_comm (p : ℝ) (m : ℝ)]
  tauto

theorem scaledPrimeCount_eq_frozen (y : ℝ) (d b m : ℕ)
    (hy : 0 ≤ y) (hm : 0 < m) :
    scaledPrimeCount y d b m = primesInAPBelow ⌊y⌋₊ m d b := by
  unfold scaledPrimeCount primesInAPBelow
  congr 1
  ext p
  rw [mem_scaledPrimeSet hy hm]
  simp only [mem_filter, mem_range, Nat.lt_succ_iff]
  have hprod : m * p ≤ ⌊y⌋₊ ↔ (m : ℝ) * p ≤ y := by
    rw [Nat.le_floor_iff hy, Nat.cast_mul]
  constructor
  · rintro ⟨hp, hpy, hcong⟩
    have hmp := hprod.mpr hpy
    exact ⟨(Nat.le_mul_of_pos_left p hm).trans hmp, hp, hmp, hcong⟩
  · rintro ⟨_, hp, hmp, hcong⟩
    exact ⟨hp, hprod.mp hmp, hcong⟩

theorem scaledPrimeCount_eq_inverse (y : ℝ) (d b m : ℕ)
    (hy : 0 ≤ y) (hm : 0 < m) (hmd : m.Coprime d) :
    scaledPrimeCount y d b m =
      primesInAP ⌊y / m⌋₊ d (natInvMod d m * b % d) := by
  rw [scaledPrimeCount_eq_frozen y d b m hy hm,
    primesInAPBelow_eq_primesInAP_inv _ _ _ _ hm hmd,
    Nat.floor_div_natCast]

theorem scaledPrimeCount_residue_mod (y : ℝ) (d b m : ℕ) :
    scaledPrimeCount y d (b % d) m = scaledPrimeCount y d b m := by
  unfold scaledPrimeCount scaledPrimeSet
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p _
  simp only [Nat.ModEq, Nat.mod_mod]

theorem ebar_residue_mod (y : ℝ) (d b m : ℕ) :
    ebar y d (b % d) m = ebar y d b m := by
  simp only [ebar, scaledPrimeCount_residue_mod]

theorem wuLi_sub_frozen (t : ℝ) :
    wuLi t = liuLogarithmicIntegral (2 / Real.log 2) t - 2 / Real.log 2 := by
  simp [wuLi, liuLogarithmicIntegral]

theorem wuLi_sub_wuLi (u v : ℝ) :
    wuLi u - wuLi v =
      liuLogarithmicIntegral (2 / Real.log 2) u -
        liuLogarithmicIntegral (2 / Real.log 2) v := by
  rw [wuLi_sub_frozen, wuLi_sub_frozen]
  ring

theorem ebar_eq_frozen_add_correction (y : ℝ) (d b m : ℕ)
    (hy : 0 ≤ y) (hm : 0 < m) :
    ebar y d b m =
      liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) ⌊y⌋₊ m d b +
        (liuLogarithmicIntegral (2 / Real.log 2) ((⌊y⌋₊ : ℝ) / m) -
          liuLogarithmicIntegral (2 / Real.log 2) (y / m) +
          2 / Real.log 2) / Nat.totient d := by
  rw [ebar, scaledPrimeCount_eq_frozen y d b m hy hm, wuLi_sub_frozen]
  unfold liuScaledAPError
  ring

theorem ebar_nat_eq_frozen (Y d b m : ℕ) (hm : 0 < m) :
    ebar Y d b m =
      liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) Y m d b +
        (2 / Real.log 2) / Nat.totient d := by
  simpa using ebar_eq_frozen_add_correction (Y : ℝ) d b m (by positivity) hm

theorem ebar_moving_inverse (r : ℝ) (d b m : ℕ)
    (hr : 0 ≤ r) (hm : 0 < m) (hmd : m.Coprime d) :
    ebar ((m : ℝ) * r) d b m =
      (primesInAP ⌊r⌋₊ d (natInvMod d m * b % d) : ℝ) -
        wuLi r / Nat.totient d := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [ebar, scaledPrimeCount_eq_inverse _ _ _ _ (by positivity) hm hmd]
  simp [hmR]

/-- The real-to-natural correction is bounded, but is not zero. -/
theorem abs_ebar_sub_frozen_le (y : ℝ) (d b m : ℕ)
    (hy : 0 ≤ y) (hm : 0 < m) (hd : 0 < d)
    (hlo : 2 ≤ (⌊y⌋₊ : ℝ) / m) :
    |ebar y d b m -
        liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) ⌊y⌋₊ m d b| ≤
      (3 / Real.log 2) / Nat.totient d := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlohi : (⌊y⌋₊ : ℝ) / m ≤ y / m :=
    div_le_div_of_nonneg_right (Nat.floor_le hy) hmR.le
  have hshort : y / (m : ℝ) ≤ (⌊y⌋₊ : ℝ) / m + 1 := by
    apply (div_le_iff₀ hmR).mpr
    have hfloor := Nat.lt_floor_add_one y
    have heq : ((⌊y⌋₊ : ℝ) / m + 1) * m = (⌊y⌋₊ : ℝ) + m := by
      field_simp
    rw [heq]
    linarith
  have hli := AnalyticNumberTheory.LargeSieve.PanPrincipal.abs_li_sub_le_short
    (2 / Real.log 2) hlo hlohi hshort
  rw [ebar_eq_frozen_add_correction _ _ _ _ hy hm, add_sub_cancel_left,
    abs_div, abs_of_pos (show (0 : ℝ) < Nat.totient d by
      exact_mod_cast Nat.totient_pos.mpr hd)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ |liuLogarithmicIntegral (2 / Real.log 2) ((⌊y⌋₊ : ℝ) / m) -
        liuLogarithmicIntegral (2 / Real.log 2) (y / m)| +
        |2 / Real.log 2| := abs_add_le _ _
    _ ≤ 1 / Real.log 2 + 2 / Real.log 2 := by
      rw [abs_sub_comm, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.log 2)]
      linarith
    _ = _ := by ring

end
end Wu2004MeanValue