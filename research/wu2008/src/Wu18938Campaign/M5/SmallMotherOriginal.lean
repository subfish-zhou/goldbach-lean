import Wu18938Campaign.M5.SmallMotherPacking
import Wu18938Campaign.M5.OriginalConsumer

noncomputable section

namespace Wu18938Campaign.M5.SmallMotherOriginal

open Real Finset Wu2008DoubleSieve WuPaper.R2SixthCount
open SmallMotherDifference SmallMotherPacking
open scoped Classical

def bMid : ℝ := (alpha + bCut) / 2

def smallLower (j : Fin 3) : ℝ := ![alpha, alpha, bMid] j
def smallUpper (j : Fin 3) : ℝ := ![beta, bMid, bCut] j
def largeLower (j : Fin 3) : ℝ := ![beta, aCeiling, aCeiling] j
def largeUpper (j : Fin 3) : ℝ := ![aCeiling, sigma, sigma] j

def bandCoefficient (δ η : ℝ) (j : Fin 3) : ℝ :=
  endpointCoefficient δ
    (((1 / 2 - δ) - smallLower j) / (largeUpper j - η))
    (((1 / 2 - δ) - smallUpper j) / largeLower j)

theorem band_geometry {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hη : 0 < η) (hηhi : η ≤ 1 / 1000) (j : Fin 3) :
    alpha ≤ smallLower j ∧ smallLower j ≤ smallUpper j ∧
      alpha ≤ largeLower j ∧ smallUpper j ≤ (1 / 2 - δ) / 2 ∧
      0 < largeLower j ∧ 0 < largeUpper j - η ∧
      1 ≤ ((1 / 2 - δ) - smallLower j) / (largeUpper j - η) ∧
      ((1 / 2 - δ) - smallLower j) / (largeUpper j - η) ≤
        ((1 / 2 - δ) - smallUpper j) / largeLower j ∧
      ((1 / 2 - δ) - smallUpper j) / largeLower j ≤ 10 := by
  have hsmall : smallUpper j < 1 / 2 - δ := by
    fin_cases j <;>
      norm_num [smallUpper, bMid, bCut, alpha, beta, QuarterTrim.alpha, QuarterTrim.beta] <;>
      linarith
  have hprod := mul_nonneg (sub_pos.mpr hsmall).le (sub_nonneg.mpr hηhi)
  have hv : 0 < largeLower j := by
    fin_cases j <;>
      norm_num [largeLower, aCeiling, beta, QuarterTrim.beta]
  have hw : 0 < largeUpper j - η := by
    fin_cases j <;>
      norm_num [largeUpper, aCeiling, sigma, alpha, beta, QuarterTrim.alpha, QuarterTrim.beta] <;>
      linarith
  refine ⟨?_, ?_, ?_, ?_, hv, hw, ?_, ?_, ?_⟩
  · fin_cases j <;>
      norm_num [smallLower, bMid, bCut, alpha, QuarterTrim.alpha]
  · fin_cases j <;>
      norm_num [smallLower, smallUpper, bMid, bCut, alpha, beta, QuarterTrim.alpha, QuarterTrim.beta]
  · fin_cases j <;>
      norm_num [largeLower, aCeiling, alpha, beta, QuarterTrim.alpha, QuarterTrim.beta]
  · fin_cases j <;>
      norm_num [smallUpper, bMid, bCut, alpha, beta, QuarterTrim.alpha, QuarterTrim.beta] <;>
      linarith
  · apply (le_div_iff₀ hw).mpr
    fin_cases j <;>
      norm_num [smallLower, largeUpper, aCeiling, sigma, bMid, bCut,
        alpha, beta, QuarterTrim.alpha, QuarterTrim.beta] <;> linarith
  · apply (div_le_div_iff₀ hw hv).mpr
    fin_cases j <;>
      norm_num [smallLower, smallUpper, largeLower, largeUpper, aCeiling, sigma, bMid, bCut,
        alpha, beta, QuarterTrim.alpha, QuarterTrim.beta] at hprod ⊢ <;> nlinarith
  · apply (div_le_iff₀ hv).mpr
    fin_cases j <;>
      norm_num [smallUpper, largeLower, aCeiling, bMid, bCut,
        alpha, beta, QuarterTrim.alpha, QuarterTrim.beta] <;> linarith

theorem band_count_sum {N : ℕ} (hN : 1 ≤ N) (η : ℝ) :
    (∑ j : Fin 3,
      (rectangleCount N (smallLower j) (smallUpper j) (largeLower j) (largeUpper j - η) : ℝ)) =
      ((rectangleCount N alpha beta beta (aCeiling - η) +
        rectangleCount N alpha bCut aCeiling (sigma - η) : ℤ) : ℝ) := by
  have hleft : alpha ≤ bMid := by
    norm_num [bMid, bCut, alpha, QuarterTrim.alpha]
  have hright : bMid ≤ bCut := by
    norm_num [bMid, bCut, alpha, QuarterTrim.alpha]
  have hsplit :
      rectangleCount N alpha bCut aCeiling (sigma - η) =
        rectangleCount N alpha bMid aCeiling (sigma - η) +
          rectangleCount N bMid bCut aCeiling (sigma - η) := by
    unfold rectangleCount
    simp_rw [window_sum_split hN hleft hright]
    rw [sum_add_distrib]
  rw [hsplit]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, smallLower, smallUpper, largeLower,
    largeUpper, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Int.cast_add, add_zero]

/-- All geometric inputs are produced here, including both halves of the original high b window. -/
theorem original_ab_endpoint_lower {η δ ε : ℝ}
    (hη : 0 < η) (hηhi : η ≤ 1 / 1000)
    (hδ : 0 < δ) (hδcap : δ ≤ min η (1 / 100)) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        (∑ j : Fin 3, (bandCoefficient δ η j - ε) *
            motherMass N δ Δ (smallLower j) (smallUpper j)) ≤
          ((rectangleCount N alpha beta beta (aCeiling - η) +
            rectangleCount N alpha bCut aCeiling (sigma - η) : ℤ) : ℝ) := by
  have hδhi := hδcap.trans (min_le_right _ _)
  have hb (j : Fin 3) :
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ∀ Δ : ℝ, 1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
          Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
          (bandCoefficient δ η j - ε) * motherMass N δ Δ (smallLower j) (smallUpper j) ≤
            (rectangleCount N (smallLower j) (smallUpper j)
              (largeLower j) (largeUpper j - η) : ℝ) := by
    obtain ⟨hl, hlu, hv, hu, hv0, hw0, hs, hst, ht⟩ := band_geometry hδ hδhi hη hηhi j
    exact rectangle_lower hδ hδhi hl hlu hv hu hs hst ht
      (by rw [mul_div_cancel₀ _ hv0.ne'])
      (by rw [mul_div_cancel₀ _ hw0.ne']) hε
  choose T hT4 hT using hb
  refine ⟨∑ j : Fin 3, T j, ?_, ?_⟩
  · exact (hT4 0).trans (single_le_sum (fun j _ => Nat.zero_le (T j)) (mem_univ 0))
  · intro N hN he Δ hΔlo hΔhi
    rw [← band_count_sum (by
      have h4 := (hT4 0).trans ((single_le_sum
        (fun j _ => Nat.zero_le (T j)) (mem_univ 0)).trans hN)
      omega) η]
    exact sum_le_sum (fun j _ => hT j N
      ((single_le_sum (fun i _ => Nat.zero_le (T i)) (mem_univ j)).trans hN)
      he Δ hΔlo hΔhi)

theorem original_upsilon6_endpoint_lower {η δ ε : ℝ}
    (hη : 0 < η) (hηhi : η ≤ 1 / 1000)
    (hδ : 0 < δ) (hδcap : δ ≤ min η (1 / 100)) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        (∑ j : Fin 3, (bandCoefficient δ η j - ε) *
          motherMass N δ Δ (smallLower j) (smallUpper j)) ≤ (upsilon6 N : ℝ) := by
  obtain ⟨T, hT4, hT⟩ := original_ab_endpoint_lower hη hηhi hδ hδcap hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he Δ hΔlo hΔhi
  exact (hT N hN he Δ hΔlo hΔhi).trans (by
    exact_mod_cast OriginalConsumer.original_trimmed_count (by omega : 1 ≤ N) hη.le)

set_option pp.universes true
set_option pp.fullNames true

#check @bMid
#print axioms bMid
#check @smallLower
#print axioms smallLower
#check @smallUpper
#print axioms smallUpper
#check @largeLower
#print axioms largeLower
#check @largeUpper
#print axioms largeUpper
#check @bandCoefficient
#print axioms bandCoefficient
#check @band_geometry
#print axioms band_geometry
#check @band_count_sum
#print axioms band_count_sum
#check @original_ab_endpoint_lower
#print axioms original_ab_endpoint_lower
#check @original_upsilon6_endpoint_lower
#print axioms original_upsilon6_endpoint_lower

end Wu18938Campaign.M5.SmallMotherOriginal
