import MathlibNt.Wu2004MeanValue.SmallSource
import MathlibNt.Wu2004MeanValue.OpenIntervals
import MathlibNt.SieveTheory.LiuPanLiMainTermEnvelope

/-!
# Weight payment for the actual Wu AP discrepancy

The elementary envelope below is for arbitrary bounded coefficients, not
the special Liu semiprime coefficient. The source sum precedes its absolute
value, and one residue is retained across all its coordinates.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.Richert1969

noncomputable section

def actualAPError (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ) : ℝ :=
  |∑ m ∈ S.filter (fun m => m.Coprime d),
    f m * ebar ((m : ℝ) * r m) d b m|

theorem actualAPError_nonneg (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ) :
    0 ≤ actualAPError S f r d b := abs_nonneg _

theorem ap_source_reciprocal_bound (x : ℝ) (S : Finset ℕ) (hx : 2 ≤ x)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ x) :
    (∑ m ∈ S, (1 : ℝ) / m) ≤ 1 + Real.log x := by
  have hsub : S ⊆ Icc 1 ⌊x⌋₊ :=
    fun m hm => mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor (hS m hm).2⟩
  calc
    _ ≤ ∑ m ∈ Icc 1 ⌊x⌋₊, (1 : ℝ) / m := by
      exact sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = liuHarmonic ⌊x⌋₊ := by simp [liuHarmonic, one_div]
    _ ≤ 1 + Real.log (⌊x⌋₊ : ℝ) := liuHarmonic_le_one_add_log _
    _ ≤ _ := by
      gcongr
      · exact_mod_cast (show 0 < ⌊x⌋₊ from
          lt_of_lt_of_le (by norm_num : 0 < 2) (Nat.le_floor hx))
      · exact Nat.floor_le (by linarith)

theorem wuLi_abs_le_linear {r : ℝ} (hr : 2 ≤ r) :
    |wuLi r| ≤ liuPanLiEnvelopeConstant 0 * r := by
  have hlog : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hr
  calc
    _ ≤ liuLogarithmicIntegralUpperConstant 0 * r / Real.log r :=
      liuLogarithmicIntegral_abs_le 0 hr
    _ ≤ liuLogarithmicIntegralUpperConstant 0 * r / Real.log 2 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (liuLogarithmicIntegralUpperConstant_nonneg 0) (by linarith))
        (Real.log_pos (by norm_num)) hlog
    _ = _ := by unfold liuPanLiEnvelopeConstant; ring

theorem totient_mul_abs_ebar_le (d b m : ℕ) (r : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hmd : m.Coprime d) (hr : 2 ≤ r) :
    (Nat.totient d : ℝ) * |ebar ((m : ℝ) * r) d b m| ≤
      (1 + liuPanLiEnvelopeConstant 0) * r + d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hphi : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have hcount : (d : ℝ) *
      (primesInAP ⌊r⌋₊ d (natInvMod d m * b % d) : ℝ) ≤ r + d := by
    have hn := modulus_mul_primesInAP_le ⌊r⌋₊ d (natInvMod d m * b % d) hd
    have hcast : (d : ℝ) *
        (primesInAP ⌊r⌋₊ d (natInvMod d m * b % d) : ℝ) ≤ ⌊r⌋₊ + d := by
      exact_mod_cast hn
    have hfloor : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le (by linarith)
    linarith
  rw [ebar_moving_inverse r d b m (by linarith) hm hmd]
  calc
    _ ≤ (Nat.totient d : ℝ) *
        (|(primesInAP ⌊r⌋₊ d (natInvMod d m * b % d) : ℝ)| +
          |wuLi r / Nat.totient d|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hphi.le
    _ = (Nat.totient d : ℝ) *
        (primesInAP ⌊r⌋₊ d (natInvMod d m * b % d) : ℝ) + |wuLi r| := by
      rw [abs_of_nonneg (by positivity), abs_div, abs_of_pos hphi, mul_add]
      field_simp
    _ ≤ (d : ℝ) * (primesInAP ⌊r⌋₊ d (natInvMod d m * b % d) : ℝ) +
        liuPanLiEnvelopeConstant 0 * r := by
      apply add_le_add _ (wuLi_abs_le_linear hr)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le d)
        (by positivity)
    _ ≤ _ := by linarith

def apEnvelopeConstant (F K : ℝ) : ℝ :=
  F * ((1 + liuPanLiEnvelopeConstant 0) * K + 1)

theorem apEnvelopeConstant_nonneg {F K : ℝ} (hF : 0 ≤ F) (hK : 0 ≤ K) :
    0 ≤ apEnvelopeConstant F K := by
  unfold apEnvelopeConstant
  positivity [liuPanLiEnvelopeConstant_nonneg 0]

/-- The actual complete AP sum has a reciprocal-totient envelope. No
distribution theorem, restriction on the residue, or special coefficient
identity is assumed. The `+1` in a residue-class count is paid by `d|S|≤x`. -/
theorem totient_mul_actualAPError_le (x F K : ℝ) (S : Finset ℕ)
    (f r : ℕ → ℝ) (d b : ℕ)
    (hx : 2 ≤ x) (hF : 0 ≤ F) (hK : 0 ≤ K)
    (hd : 0 < d) (hdx : (d : ℝ) ≤ Real.sqrt x)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x)
    (hf : ∀ m ∈ S, |f m| ≤ F)
    (hr : ∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) :
    (Nat.totient d : ℝ) * actualAPError S f r d b ≤
      apEnvelopeConstant F K * x * (1 + Real.log x) := by
  let T := S.filter (fun m => m.Coprime d)
  have hT : ∀ m ∈ T, m ∈ S := fun m hm => (mem_filter.mp hm).1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hroot : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hcard : (T.card : ℝ) ≤ Real.sqrt x :=
    small_support_card_le T _ (Real.sqrt_nonneg x) (fun m hm => hS m (hT m hm))
  have hmass : (∑ m ∈ T, r m) ≤ K * x * (1 + Real.log x) := by
    calc
      _ ≤ ∑ m ∈ T, K * x * (1 / (m : ℝ)) := by
        apply sum_le_sum
        intro m hm
        have hmR : (0 : ℝ) < m := by exact_mod_cast (hS m (hT m hm)).1
        have h := (le_div_iff₀ hmR).mpr (by
          simpa [mul_comm] using (hr m (hT m hm)).2)
        simpa only [mul_one_div, mul_comm x K] using h
      _ = K * x * (∑ m ∈ T, 1 / (m : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (ap_source_reciprocal_bound x T hx
          (fun m hm => ⟨(hS m (hT m hm)).1, (hS m (hT m hm)).2.trans hroot⟩))
        (mul_nonneg hK (by linarith))
  have hatom : (d : ℝ) * T.card ≤ x := by
    calc
      _ ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul hdx hcard (by positivity) (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt (by linarith)
  have hC : 0 ≤ 1 + liuPanLiEnvelopeConstant 0 := by
    positivity [liuPanLiEnvelopeConstant_nonneg 0]
  calc
    _ ≤ (Nat.totient d : ℝ) *
        (∑ m ∈ T, |f m * ebar ((m : ℝ) * r m) d b m|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ∑ m ∈ T, F * ((1 + liuPanLiEnvelopeConstant 0) * r m + d) := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      rw [abs_mul, mul_left_comm]
      exact mul_le_mul (hf m (hT m hm))
        (totient_mul_abs_ebar_le d b m (r m) hd (hS m (hT m hm)).1
          (mem_filter.mp hm).2 (hr m (hT m hm)).1)
        (mul_nonneg (by positivity) (abs_nonneg _)) hF
    _ = F * ((1 + liuPanLiEnvelopeConstant 0) * (∑ m ∈ T, r m) +
        d * T.card) := by
      simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      ring
    _ ≤ F * ((1 + liuPanLiEnvelopeConstant 0) *
        (K * x * (1 + Real.log x)) + x) := by gcongr
    _ ≤ apEnvelopeConstant F K * x * (1 + Real.log x) := by
      unfold apEnvelopeConstant
      have h := mul_nonneg (mul_nonneg hF (by linarith : 0 ≤ x)) hlog
      nlinarith

theorem ap_totient_ratio_le_log (x : ℝ) (d : ℕ) (hx : 2 ≤ x)
    (hd : 0 < d) (hdx : (d : ℝ) ≤ x) :
    (d : ℝ) / Nat.totient d ≤ richertReciprocalTotientConstant * Real.log x := by
  have h := reciprocal_totient_le_richertConstant_log_div
    (Nat.le_floor hx) hd (Nat.le_floor hdx)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h' := mul_le_mul_of_nonneg_left h hdR.le
  have hratio : (d : ℝ) / Nat.totient d ≤
      richertReciprocalTotientConstant * Real.log (⌊x⌋₊ : ℝ) := by
    calc
      _ = (d : ℝ) * (1 / (Nat.totient d : ℝ)) := by ring
      _ ≤ d * (richertReciprocalTotientConstant * Real.log (⌊x⌋₊ : ℝ) / d) := h'
      _ = _ := by field_simp
  apply hratio.trans
  apply mul_le_mul_of_nonneg_left _ richertReciprocalTotientConstant_pos.le
  exact Real.log_le_log
    (by exact_mod_cast (show 0 < ⌊x⌋₊ from lt_of_lt_of_le (by norm_num : 0 < 2)
      (Nat.le_floor hx))) (Nat.floor_le (by linarith))

/-- A modulus, rather than totient, envelope makes the frozen reciprocal
ninth divisor moment directly applicable. -/
theorem modulus_mul_actualAPError_le (x F K : ℝ) (S : Finset ℕ)
    (f r : ℕ → ℝ) (d b : ℕ)
    (hx : 2 ≤ x) (hF : 0 ≤ F) (hK : 0 ≤ K)
    (hd : 0 < d) (hdx : (d : ℝ) ≤ Real.sqrt x)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x)
    (hf : ∀ m ∈ S, |f m| ≤ F)
    (hr : ∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) :
    (d : ℝ) * actualAPError S f r d b ≤
      (apEnvelopeConstant F K * richertReciprocalTotientConstant) *
        x * (1 + Real.log x) ^ 2 := by
  have hphi : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hC := apEnvelopeConstant_nonneg hF hK
  calc
    _ = ((d : ℝ) / Nat.totient d) *
        ((Nat.totient d : ℝ) * actualAPError S f r d b) := by field_simp
    _ ≤ (richertReciprocalTotientConstant * Real.log x) *
        (apEnvelopeConstant F K * x * (1 + Real.log x)) :=
      mul_le_mul
        (ap_totient_ratio_le_log x d hx hd
          (hdx.trans (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith)))))
        (totient_mul_actualAPError_le x F K S f r d b hx hF hK hd hdx hS hf hr)
        (mul_nonneg (by positivity) (actualAPError_nonneg ..))
        (mul_nonneg richertReciprocalTotientConstant_pos.le hlog)
    _ ≤ _ := by
      have h := mul_nonneg
        (mul_nonneg (mul_nonneg hC richertReciprocalTotientConstant_pos.le)
          (by linarith : 0 ≤ x)) (by linarith : 0 ≤ 1 + Real.log x)
      nlinarith

end
end Wu2004MeanValue