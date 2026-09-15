import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairData
import MathlibNt.Wu2008DoubleSieve.Gamma5GainCell

namespace Wu2008DoubleSieve.MotherPair
open Real Set Finset
open scoped Classical

 theorem parameter_order {p : SecondFunctionalParameters} (h : AnalyticParameters p) :
    (1/5:ℝ) ≤ 1/p.S ∧ 1/p.S ≤ 1/p.kappa1 ∧
    1/p.kappa1 < 1/p.kappa2 ∧ 1/p.kappa2 < 1/p.kappa3 ∧
    1/p.kappa3 ≤ 1/p.s ∧ 1/p.s < 1/2 := by
  have hs : 0 < p.s := by linarith [h.two_lt_s]
  have he := hs.trans_le h.mother.s_le_kappa3
  have hc := he.trans h.mother.kappa3_lt_kappa2
  have hb := hc.trans h.mother.kappa2_lt_kappa1
  have ha := hb.trans_le h.mother.kappa1_le_S
  exact ⟨by simpa using one_div_le_one_div_of_le ha h.S_le_five,
    one_div_le_one_div_of_le hb h.mother.kappa1_le_S,
    (one_div_lt_one_div hb hc).mpr h.mother.kappa2_lt_kappa1,
    (one_div_lt_one_div hc he).mpr h.mother.kappa3_lt_kappa2,
    one_div_le_one_div_of_le hs h.mother.s_le_kappa3,
    (one_div_lt_one_div hs (by norm_num : (0:ℝ) < 2)).mpr h.two_lt_s⟩

/-- The genuine common region for Gamma6--8. The extra gap is scalar only. -/
theorem fullH_domain {p : SecondFunctionalParameters} (h : FullHParameters p)
    {t u : ℝ} (ht : 1/p.S ≤ t) (htb : t ≤ 1/p.kappa1)
    (htu : t ≤ u) (hue : u ≤ 1/p.kappa3) :
    0 < t ∧ 0 < u ∧ 2*u < 1 ∧ u+2*t < 1 ∧ 0 < 1-t-u ∧
    (1 ≤ p.S*(1-t-u) ∧ p.S*(1-t-u) ≤ 3) ∧
    (1 ≤ (1-t-u)/t ∧ (1-t-u)/t ≤ 3) := by
  obtain ⟨ha, _, _, _, hef, hf⟩ := parameter_order h.toAnalyticParameters
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := ht0.trans_le htu
  have hu2 : 2*u < 1 := by linarith
  have hgap := h.insertion_gap
  rw [div_eq_mul_one_div 2] at hgap
  have hut : u+2*t < 1 := by linarith
  have hden : 0 < 1-t-u := by linarith
  have hS : 0 < p.S := by linarith [h.three_le_S]
  have hSt : 1 ≤ p.S*t := by
    have := (div_le_iff₀ hS).mp ht
    nlinarith
  have hSu : 1 ≤ p.S*u := hSt.trans (mul_le_mul_of_nonneg_left htu hS.le)
  refine ⟨ht0,hu0,hu2,hut,hden,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · nlinarith [mul_pos hS (show 0 < 1-u-2*t by linarith)]
  · nlinarith [h.S_le_five]
  · apply (le_div_iff₀ ht0).mpr
    linarith
  · apply (div_le_iff₀ ht0).mpr
    linarith

/-- Gamma5 uses only the original legal insertion inequalities. -/
theorem legal_domain {S t u : ℝ} (hS3 : 3 ≤ S) (hS5 : S ≤ 5)
    (ht : 1/S ≤ t) (htu : t ≤ u) (_hu : 2*u ≤ 1) (hut : u+2*t ≤ 1) :
    0 < t ∧ 0 < u ∧ 0 < 1-t-u ∧
    (1 ≤ S*(1-t-u) ∧ S*(1-t-u) ≤ 3) ∧
    (1 ≤ (1-t-u)/t ∧ (1-t-u)/t ≤ 3) := by
  have hS : 0 < S := by linarith
  have ha : (1/5:ℝ) ≤ 1/S := by
    simpa using one_div_le_one_div_of_le hS hS5
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := ht0.trans_le htu
  have hSt : 1 ≤ S*t := by nlinarith [(div_le_iff₀ hS).mp ht]
  have hSu : 1 ≤ S*u := hSt.trans (mul_le_mul_of_nonneg_left htu hS.le)
  refine ⟨ht0,hu0,by linarith,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · nlinarith [mul_nonneg hS.le (show 0 ≤ 1-u-2*t by linarith)]
  · nlinarith
  · apply (le_div_iff₀ ht0).mpr
    linarith
  · apply (div_le_iff₀ ht0).mpr
    linarith

 theorem strict_interior {S t u : ℝ} (hS3 : 3 ≤ S) (hS5 : S ≤ 5)
    (ht : 1/S < t) (htu : t ≤ u) :
    S*(1-t-u) < 3 ∧ (1-t-u)/t < 3 := by
  have hS : 0 < S := by linarith
  have ha : (1/5:ℝ) ≤ 1/S := by
    simpa using one_div_le_one_div_of_le hS hS5
  have ht0 : 0 < t := by linarith
  have hSt : 1 < S*t := by nlinarith [(div_lt_iff₀ hS).mp ht]
  have hSu := mul_le_mul_of_nonneg_left htu hS.le
  constructor
  · nlinarith
  · apply (div_lt_iff₀ ht0).mpr
    linarith

 theorem closed_five_endpoint :
    (5:ℝ)*(1-1/5-1/5) = 3 ∧ (1-1/5-1/5)/(1/5:ℝ) = 3 := by norm_num

/-- These are exactly the four physical rpow premises of sorted two-insertion. -/
theorem sorted_rpow_admission {R S t u : ℝ} (hR : 1 < R)
    (hS : 0 < S) (hS5 : S ≤ 5) (ht : 1/S ≤ t) (htu : t ≤ u)
    (hu : 2*u ≤ 1) (hut : u+2*t ≤ 1) :
    R^(1/10:ℝ) ≤ R^u ∧ R^u ≤ R^(1/2:ℝ) ∧
    (R/R^u)^(1/10:ℝ) ≤ R^t ∧ R^t ≤ (R/R^u)^(1/2:ℝ) := by
  have ha : (1/5:ℝ) ≤ 1/S := by
    simpa using one_div_le_one_div_of_le hS hS5
  have hR0 : 0 < R := by linarith
  have he : R/R^u = R^(1-u) := by rw [rpow_sub hR0, rpow_one]
  rw [he, ← rpow_mul hR0.le, ← rpow_mul hR0.le]
  refine ⟨rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_⟩ <;> linarith

 theorem fullH_sorted_rpow {p : SecondFunctionalParameters} (h : FullHParameters p)
    {R t u : ℝ} (hR : 1 < R) (ht : 1/p.S ≤ t) (htb : t ≤ 1/p.kappa1)
    (htu : t ≤ u) (hue : u ≤ 1/p.kappa3) :
    R^(1/10:ℝ) ≤ R^u ∧ R^u ≤ R^(1/2:ℝ) ∧
    (R/R^u)^(1/10:ℝ) ≤ R^t ∧ R^t ≤ (R/R^u)^(1/2:ℝ) := by
  have hg := fullH_domain h ht htb htu hue
  exact sorted_rpow_admission hR (by linarith [h.three_le_S]) h.S_le_five ht htu
    hg.2.2.1.le hg.2.2.2.1.le

/-- Closed real region corresponding to each original half-open prime rectangle.
Gamma5 still needs the two legal insertion inequalities separately. -/
def PairRegion (p : SecondFunctionalParameters) : Term → ℝ → ℝ → Prop
  | .gammaFive, t, u => 1/p.S ≤ t ∧ t ≤ 1/p.kappa2 ∧ t ≤ u ∧ u ≤ 1/p.kappa2
  | .gammaSix, t, u => 1/p.S ≤ t ∧ t ≤ 1/p.kappa1 ∧ 1/p.kappa2 ≤ u ∧ u ≤ 1/p.kappa3
  | .gammaSeven, t, u => 1/p.S ≤ t ∧ t ≤ 1/p.kappa1 ∧ t ≤ u ∧ u ≤ 1/p.kappa1
  | .gammaEight, t, u => 1/p.S ≤ t ∧ t ≤ 1/p.kappa1 ∧ 1/p.kappa1 ≤ u ∧ u ≤ 1/p.kappa2

noncomputable def Hratio (p : SecondFunctionalParameters) : Term → ℝ → ℝ → ℝ
  | .gammaFive, t, u => p.S*(1-t-u)
  | .gammaSix, t, u => p.S*(1-t-u)
  | .gammaSeven, t, u => (1-t-u)/t
  | .gammaEight, t, u => (1-t-u)/t

theorem fullH_region_bounds {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) {t u : ℝ} (hv : PairRegion p j t u) :
    1/p.S ≤ t ∧ t ≤ 1/p.kappa1 ∧ t ≤ u ∧ u ≤ 1/p.kappa3 := by
  obtain ⟨_,_,hbc,hce,_,_⟩ := parameter_order h.toAnalyticParameters
  cases j with
  | gammaFive => exact False.elim (hj rfl)
  | gammaSix => exact ⟨hv.1,hv.2.1,(hv.2.1.trans hbc.le).trans hv.2.2.1,hv.2.2.2⟩
  | gammaSeven => exact ⟨hv.1,hv.2.1,hv.2.2.1,(hv.2.2.2.trans hbc.le).trans hce.le⟩
  | gammaEight => exact ⟨hv.1,hv.2.1,hv.2.1.trans hv.2.2.1,hv.2.2.2.trans hce.le⟩

/-- The actual fixed Gamma6 ratio and selected Gamma7/8 ratio, together with
all four sorted insertion premises, including the closed endpoint 3. -/
theorem fullH_term_admission {p : SecondFunctionalParameters} (h : FullHParameters p)
    (j : Term) (hj : j ≠ .gammaFive) {R t u : ℝ} (hR : 1 < R)
    (hv : PairRegion p j t u) :
    2*u < 1 ∧ u+2*t < 1 ∧ 0 < 1-t-u ∧ Hratio p j t u ∈ Set.Icc 1 3 ∧
    R^(1/10:ℝ) ≤ R^u ∧ R^u ≤ R^(1/2:ℝ) ∧
    (R/R^u)^(1/10:ℝ) ≤ R^t ∧ R^t ≤ (R/R^u)^(1/2:ℝ) := by
  obtain ⟨ht,htb,htu,hue⟩ := fullH_region_bounds h j hj hv
  have hg := fullH_domain h ht htb htu hue
  refine ⟨hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,?_,fullH_sorted_rpow h hR ht htb htu hue⟩
  cases j with
  | gammaFive => exact False.elim (hj rfl)
  | gammaSix => exact hg.2.2.2.2.2.1
  | gammaSeven => exact hg.2.2.2.2.2.2
  | gammaEight => exact hg.2.2.2.2.2.2

theorem gammaFive_term_admission {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    {R t u : ℝ} (hR : 1 < R) (hv : PairRegion p .gammaFive t u)
    (hu : 2*u ≤ 1) (hut : u+2*t ≤ 1) :
    0 < 1-t-u ∧ Hratio p .gammaFive t u ∈ Set.Icc 1 3 ∧
    R^(1/10:ℝ) ≤ R^u ∧ R^u ≤ R^(1/2:ℝ) ∧
    (R/R^u)^(1/10:ℝ) ≤ R^t ∧ R^t ≤ (R/R^u)^(1/2:ℝ) := by
  have hg := legal_domain h.three_le_S h.S_le_five hv.1 hv.2.2.1 hu hut
  exact ⟨hg.2.2.1,hg.2.2.2.1,sorted_rpow_admission hR
    (by linarith [h.three_le_S]) h.S_le_five hv.1 hv.2.2.1 hu hut⟩

/-- Analytic admissibility alone does not supply the genuine insertion gap. -/
theorem analytic_not_fullH : ∃ p : SecondFunctionalParameters,
    AnalyticParameters p ∧ ¬ FullHParameters p := by
  let p : SecondFunctionalParameters := ⟨5/2,5,3,14/5,13/5⟩
  refine ⟨p,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · constructor <;> norm_num [p]
    all_goals norm_num [p]
  · intro h
    have hh := h.insertion_gap
    norm_num [p] at hh

open SecondFunctionalParameters
 theorem row1_fullH : FullHParameters row1 := by
  refine ⟨⟨row1_motherAdmissible, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> norm_num [row1]
 theorem row2_fullH : FullHParameters row2 := by
  refine ⟨⟨row2_motherAdmissible, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> norm_num [row2]
 theorem row3_fullH : FullHParameters row3 := by
  refine ⟨⟨row3_motherAdmissible, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> norm_num [row3]
 theorem row4_fullH : FullHParameters row4 := by
  refine ⟨⟨row4_motherAdmissible, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> norm_num [row4]
end Wu2008DoubleSieve.MotherPair
