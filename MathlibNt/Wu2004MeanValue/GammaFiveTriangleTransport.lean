import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Measurability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Parameterized affine transport of the Gamma₅ triangle

The source is the literal triangular density with an optional legal insertion
cutoff. The change of variables v = S(1-t-u) includes its Jacobian exactly.
Unlike the earlier fourth-row calculation, these identities leave S and B
as parameters, so that all four original rows can use the same transport.
-/

namespace Wu2004MeanValue.GammaFiveLossBudget
open MeasureTheory Set
open scoped Classical

def triangleRegion (S B : ℝ) (legal : Bool) (t u : ℝ) : Prop :=
  1/S ≤ t ∧ t ≤ u ∧ u ≤ B ∧ (legal = true → u+2*t ≤ 1)

def triangleSection (S B : ℝ) (legal : Bool) (v t : ℝ) : Prop :=
  1/S ≤ t ∧ t ≤ (1-v/S)/2 ∧ 1-v/S-B ≤ t ∧ (legal = true → t ≤ v/S)

noncomputable def triangleSource (S B : ℝ) (legal : Bool) (H : ℝ → ℝ)
    (t u : ℝ) : ℝ :=
  if triangleRegion S B legal t u then H (S*(1-t-u))/(t*u*(1-t-u)) else 0

noncomputable def triangleMasked (S B : ℝ) (legal : Bool) (H : ℝ → ℝ)
    (v t : ℝ) : ℝ :=
  if triangleSection S B legal v t then H v/(v*t*(1-v/S-t)) else 0

/-- The original triangle and insertion gate become an exact closed section. -/
theorem triangle_region_section {S : ℝ} (hS : S ≠ 0) (B : ℝ)
    (legal : Bool) (t u : ℝ) :
    triangleRegion S B legal t u ↔ triangleSection S B legal (S*(1-t-u)) t := by
  have hr : S*(1-t-u)/S = 1-t-u := mul_div_cancel_left₀ _ hS
  simp only [triangleRegion, triangleSection, hr]
  constructor
  · rintro ⟨ha,htu,hu,hl⟩
    exact ⟨ha,by linarith,by linarith,fun he => by have := hl he; linarith⟩
  · rintro ⟨ha,ht,hu,hl⟩
    exact ⟨ha,by linarith,by linarith,fun he => by have := hl he; linarith⟩

/-- The source density is S times the transformed density. -/
theorem triangle_source_eq {S : ℝ} (hS : S ≠ 0) (B : ℝ)
    (legal : Bool) (H : ℝ → ℝ) (t u : ℝ) :
    triangleSource S B legal H t u = S * triangleMasked S B legal H (S*(1-t-u)) t := by
  unfold triangleSource triangleMasked
  rw [← triangle_region_section hS]
  split_ifs
  · rw [mul_div_cancel_left₀ _ hS]
    have hu : 1-(1-t-u)-t = u := by ring
    rw [hu]
    field_simp
  · exact (mul_zero S).symm

/-- Fixed-outer affine substitution, valid for arbitrary input H.
Integrability is needed later for swapping the two integrals, not here. -/
theorem triangle_inner_substitution {S : ℝ} (hS : 0 < S) (B : ℝ)
    (legal : Bool) (H : ℝ → ℝ) (t : ℝ) :
    (∫ u : ℝ, triangleSource S B legal H t u) =
      ∫ v : ℝ, triangleMasked S B legal H v t := by
  simp_rw [triangle_source_eq hS.ne']
  rw [integral_const_mul]
  change S * (∫ u : ℝ,
    (fun y => triangleMasked S B legal H (S*y) t) ((1-t)-u)) = _
  rw [integral_sub_left_eq_self (fun y => triangleMasked S B legal H (S*y) t)
    volume (1-t)]
  rw [Measure.integral_comp_mul_left (fun v => triangleMasked S B legal H v t)]
  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hS), ← mul_assoc,
    mul_inv_cancel₀ hS.ne', one_mul]

theorem triangle_source_support (S B : ℝ) (legal : Bool) (H : ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => triangleSource S B legal H p.1 p.2) ⊆
      Icc (1/S) B ×ˢ Icc (1/S) B := by
  intro p hp
  have hr : triangleRegion S B legal p.1 p.2 := by
    by_contra hn
    exact hp (if_neg hn)
  exact ⟨⟨hr.1,hr.2.1.trans hr.2.2.1⟩,⟨hr.1.trans hr.2.1,hr.2.2.1⟩⟩

theorem triangle_source_measurable (S B : ℝ) (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) :
    Measurable (fun p : ℝ × ℝ => triangleSource S B legal H p.1 p.2) := by
  unfold triangleSource triangleRegion
  apply Measurable.ite (by measurability) _ measurable_const
  fun_prop

/-- A uniform bound on the literal source density, with no continuity of H. -/
theorem triangle_source_bound {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (legal : Bool) {H : ℝ → ℝ} (hb : ∀ v, |H v| ≤ 1) (t u : ℝ) :
    ‖triangleSource S B legal H t u‖ ≤ 1/((1/S)*(1/S)*(1-2*B)) := by
  have ha : 0 < 1/S := one_div_pos.mpr hS
  have hc : 0 < 1-2*B := by linarith
  have hd : 0 < (1/S)*(1/S)*(1-2*B) := mul_pos (mul_pos ha ha) hc
  by_cases hr : triangleRegion S B legal t u
  · have ht : 0 < t := ha.trans_le hr.1
    have hu : 0 < u := ht.trans_le hr.2.1
    have hgap : 1-2*B ≤ 1-t-u := by linarith [hr.2.1,hr.2.2.1]
    have hden : (1/S)*(1/S)*(1-2*B) ≤ t*u*(1-t-u) :=
      mul_le_mul (mul_le_mul hr.1 (hr.1.trans hr.2.1) ha.le ht.le) hgap hc.le
        (mul_nonneg ht.le hu.le)
    rw [triangleSource, if_pos hr, Real.norm_eq_abs, abs_div,
      abs_of_pos (hd.trans_le hden)]
    exact div_le_div₀ (by norm_num) (hb _) hd hden
  · rw [triangleSource, if_neg hr, norm_zero]
    exact (one_div_pos.mpr hd).le

/-- Compact support and the preceding bound justify Fubini on the source. -/
theorem triangle_source_integrable {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (legal : Bool) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => triangleSource S B legal H p.1 p.2) := by
  apply (integrableOn_iff_integrable_of_support_subset (triangle_source_support S B legal H)).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (triangle_source_measurable S B legal hm).aestronglyMeasurable
      (M := 1/((1/S)*(1/S)*(1-2*B)))
  exact Filter.Eventually.of_forall (fun p => triangle_source_bound hS hB legal hb p.1 p.2)

theorem triangle_masked_source {S : ℝ} (hS : S ≠ 0) (B : ℝ)
    (legal : Bool) (H : ℝ → ℝ) (v t : ℝ) :
    triangleMasked S B legal H v t =
      (1/S)*triangleSource S B legal H t (1-v/S-t) := by
  rw [triangle_source_eq hS]
  have he : S*(1-t-(1-v/S-t)) = v := by field_simp; ring
  rw [he]
  field_simp

theorem triangle_masked_support {S : ℝ} (hS : 0 < S) (B : ℝ)
    (legal : Bool) (H : ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => triangleMasked S B legal H p.1 p.2) ⊆
      Icc (S*(1-2*B)) (S-2) ×ˢ Icc (1/S) B := by
  intro p hp
  have hr : triangleSection S B legal p.1 p.2 := by
    by_contra hn
    exact hp (if_neg hn)
  have hv : p.1/S*S = p.1 := div_mul_cancel₀ _ hS.ne'
  have ha : 1/S*S = 1 := one_div_mul_cancel hS.ne'
  have htB : p.2 ≤ B := by linarith [hr.2.1,hr.2.2.1]
  have hlow : S*(1-2*B) ≤ p.1 := by
    have h := mul_nonneg (by linarith [hr.2.1,hr.2.2.1] : 0 ≤ p.1/S-(1-2*B)) hS.le
    nlinarith
  have hhigh : p.1 ≤ S-2 := by
    have h := mul_nonneg (by linarith [hr.1,hr.2.1] : 0 ≤ 1-p.1/S-2*(1/S)) hS.le
    nlinarith
  exact ⟨⟨hlow,hhigh⟩,⟨hr.1,htB⟩⟩

theorem triangle_masked_measurable (S B : ℝ) (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) :
    Measurable (fun p : ℝ × ℝ => triangleMasked S B legal H p.1 p.2) := by
  unfold triangleMasked triangleSection
  apply Measurable.ite (by measurability) _ measurable_const
  fun_prop

theorem triangle_masked_integrable {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (legal : Bool) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => triangleMasked S B legal H p.1 p.2) := by
  apply (integrableOn_iff_integrable_of_support_subset (triangle_masked_support hS B legal H)).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (triangle_masked_measurable S B legal hm).aestronglyMeasurable
      (M := (1/S)*(1/((1/S)*(1/S)*(1-2*B))))
  apply Filter.Eventually.of_forall
  intro p
  rw [triangle_masked_source hS.ne', norm_mul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hS)]
  exact mul_le_mul_of_nonneg_left (triangle_source_bound hS hB legal hb _ _)
    (one_div_pos.mpr hS).le

/-- Affine substitution and Fubini, for both the full and legal triangle. -/
theorem triangle_product_transport {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (legal : Bool) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ p : ℝ × ℝ, triangleSource S B legal H p.1 p.2) =
      ∫ v : ℝ, ∫ t : ℝ, triangleMasked S B legal H v t := by
  rw [show (∫ p : ℝ × ℝ, triangleSource S B legal H p.1 p.2) =
    ∫ t, ∫ u, triangleSource S B legal H t u from
      integral_prod _ (triangle_source_integrable hS hB legal hm hb)]
  simp_rw [triangle_inner_substitution hS]
  exact integral_integral_swap (triangle_masked_integrable hS hB legal hm hb).swap

/-- The transported triangle has precisely the endpoint expressions used
by the full and legal logarithmic kernels. -/
theorem triangle_section_endpoints {S B : ℝ} (hB : B ≤ 1/2)
    (legal : Bool) (v t : ℝ) :
    triangleSection S B legal v t ↔
      max (1/S) (max (1-v/S-B) (1-v/S-1/2)) ≤ t ∧
      t ≤ min B (min (1-v/S-1/S) ((1-v/S)/2)) ∧
      (legal = true → t ≤ v/S) := by
  simp only [triangleSection, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨ha,ht,hu,hl⟩
    refine ⟨⟨ha,hu,?_⟩,⟨?_,?_,ht⟩,hl⟩ <;> linarith
  · rintro ⟨⟨ha,hu,_⟩,⟨_,_,ht⟩,hl⟩
    exact ⟨ha,ht,hu,hl⟩

end Wu2004MeanValue.GammaFiveLossBudget
