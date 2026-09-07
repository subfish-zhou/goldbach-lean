import MathlibNt.SieveTheory.LiLiuPrereqWFCollisionAnalytic

/-!
# Analytic boundary windows

Closed lower and strict upper logarithmic windows are estimated directly
from the original dimension-one product hypothesis.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset SmallRosser
open scoped Classical

namespace BoundaryAnalytic

/-- A narrow interval in logarithmic coordinates, with its lower endpoint
closed, pays its width rather than a whole dimension-one product. -/
theorem log_interval_sum_le (P S : Finset ℕ) {g : ℕ → ℝ}
    {K t l r δ : ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) (hK : 0 ≤ K)
    (ht : 1 ≤ t) (hl : t ≤ l) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hwidth : r - l ≤ δ * t)
    (hS : ∀ p ∈ S, p ∈ P ∧ p.Prime ∧ l ≤ Real.log p ∧ Real.log p < r) :
    (∑ p ∈ S, g p) ≤ δ + 2 * K / t := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < l := lt_of_lt_of_le ht0 hl
  by_cases hlr : l < r
  · have htwo : (2 : ℝ) ≤ Real.exp l := by
      calc
        2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        _ ≤ Real.exp l := Real.exp_le_exp.mpr (ht.trans hl)
    have hs := CollisionAnalytic.interval_sum_le P S hg hdim htwo
      (Real.exp_lt_exp.mpr hlr) (by
        intro p hp
        obtain ⟨hpP, hprime, hpL, hpR⟩ := hS p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
        refine mem_filter.mpr ⟨hpP, hprime, ?_, ?_⟩
        · simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hpL
        · simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hpR)
    simp only [Real.log_exp] at hs
    have hratio : r / l ≤ 1 + δ := by
      apply (div_le_iff₀ hl0).mpr
      have hm := mul_le_mul_of_nonneg_left hl hδ
      nlinarith
    have hquot : K / l ≤ K / t := div_le_div_of_nonneg_left hK ht0 hl
    have hprod := mul_le_mul hratio (show 1 + K / l ≤ 1 + K / t by linarith)
      (by positivity : 0 ≤ 1 + K / l) (by positivity : 0 ≤ 1 + δ)
    have htwo' := mul_le_mul_of_nonneg_right (show 1 + δ ≤ 2 by linarith)
      (div_nonneg hK ht0.le)
    rw [mul_div_assoc]
    nlinarith
  · have hzero : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hs := hS p hp
      exact (not_lt_of_ge (le_of_not_gt hlr)) (hs.2.2.1.trans_lt hs.2.2.2)
    rw [hzero, sum_empty]
    positivity

/-- The exponent is `1` for a full product and `3` for a cubic prefix.
The remaining prefix is recorded by its logarithmic product `x`. -/
def Window (D a x k : ℝ) (b : ℕ → ℝ) (p : ℕ) : Prop :=
  Real.log D / a ≤ x + k * Real.log (b p) ∧
    x + k * Real.log (b p) < Real.log D

theorem window_sum_le (P R : Finset ℕ) {D ε K x k : ℝ} {b : ℕ → ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    (hR : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (hx : 0 ≤ x) (hk : 1 ≤ k)
    (hb : ∀ p ∈ R, 1 ≤ b p ∧ b p ≤ (p : ℝ) ∧
      (p : ℝ) < b p ^ (1 + ε ^ 9))
    (hrough : ∀ p ∈ R, D ^ (ε ^ 2) ≤ (p : ℝ))
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    (∑ p ∈ R.filter (Window D (1 + ε ^ 9) x k b), g p) ≤
      3 * ε ^ 7 + 2 * K / (ε ^ 2 * Real.log D) := by
  let a := 1 + ε ^ 9
  let t := ε ^ 2 * Real.log D
  let l := max t ((Real.log D / a - x) / k)
  let r := a * (Real.log D - x) / k
  have hpar := CollisionAnalytic.rough_parameters hD hε hεsmall hlarge
  have he9 : 0 < ε ^ 9 := pow_pos hε _
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have hk0 : 0 < k := by linarith
  have he7 : ε ^ 7 ≤ 1 / 8 := by
    calc
      ε ^ 7 ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le (by linarith) (by omega)
      _ ≤ 1 / 8 := by simpa using hεsmall.le
  have hdelta : 0 ≤ 3 * ε ^ 7 := by positivity
  have hadiff : a - 1 / a ≤ 3 * ε ^ 9 := by
    have hh : 1 - 2 * ε ^ 9 ≤ 1 / a := by
      apply (le_div_iff₀ ha0).mpr
      dsimp [a]
      nlinarith [sq_nonneg (ε ^ 9)]
    dsimp [a] at *
    linarith
  have hwidth : r - l ≤ (3 * ε ^ 7) * t := by
    have hlow : Real.log D / a - x ≤ k * l := by
      have hh := le_max_right t ((Real.log D / a - x) / k)
      exact (div_le_iff₀ hk0).mp hh |>.trans_eq (mul_comm _ _)
    have hreq : k * r = a * (Real.log D - x) := by
      dsimp [r]
      field_simp
    have hd : k * (r - l) ≤ (a - 1 / a) * Real.log D := by
      have hdiv : Real.log D / a = (1 / a) * Real.log D := by ring
      rw [hdiv] at hlow
      nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hx]
    have hm := mul_le_mul_of_nonneg_right hadiff hpar.2.2.1.le
    have hid : (3 * ε ^ 7) * t = 3 * ε ^ 9 * Real.log D := by dsimp [t]; ring
    rw [hid]
    by_cases hrl : 0 ≤ r - l
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) hrl]
    · exact (le_of_not_ge hrl).trans
        (mul_nonneg (by positivity) hpar.2.2.1.le)
  apply log_interval_sum_le P _ hg hdim hK hlarge (le_max_left _ _)
    hdelta (by linarith) hwidth
  intro p hp
  obtain ⟨hpR, hpw⟩ := mem_filter.mp hp
  obtain ⟨hb1, hbp, hpb⟩ := hb p hpR
  have hb0 : 0 < b p := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p (hR hpR)).pos
  have hlogbp := Real.log_le_log hb0 hbp
  have hlogpb := Real.log_lt_log hp0 hpb
  rw [Real.log_rpow hb0] at hlogpb
  refine ⟨hR hpR, hP p (hR hpR), max_le ?_ ?_, ?_⟩
  · rw [← hpar.2.2.2]
    exact Real.log_le_log (by positivity) (hrough p hpR)
  · apply (div_le_iff₀ hk0).mpr
    have hmul := mul_le_mul_of_nonneg_left hlogbp hk0.le
    dsimp [Window] at hpw
    dsimp [a]
    nlinarith [hpw.1]
  · apply (lt_div_iff₀ hk0).mpr
    dsimp [Window] at hpw
    have hmul := mul_lt_mul_of_pos_left hpw.2 ha0
    have hmul' := mul_lt_mul_of_pos_left hlogpb hk0
    dsimp [a] at *
    nlinarith

#print axioms log_interval_sum_le
#print axioms window_sum_le

end BoundaryAnalytic
end MathlibNt.SieveTheory.LiLiuPrereqWF
