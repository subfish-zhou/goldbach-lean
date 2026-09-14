import MathlibNt.Analysis.IntegralExcessCover
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Shared estimates for half-open logarithmic grids. The density, cell selection,
and boundary cover remain parameters of the consumers, not replacement measures. -/

open MeasureTheory Set
open scoped BigOperators

namespace MathlibNt.Analysis.LogGridEstimates

/-- Reciprocal oscillation paid for by a positive lower gap. -/
theorem reciprocal_variation {c d l e : ℝ} (hl : 0 < l) (hc : l ≤ c)
    (hcd : c ≤ d) (he : 0 ≤ e) (hdelta : d - c ≤ e * (l * l)) :
    0 ≤ 1 / c - 1 / d ∧ 1 / c - 1 / d ≤ e := by
  have hc0 := hl.trans_le hc
  have hd0 := hc0.trans_le hcd
  have hprod : l * l ≤ c * d := mul_le_mul hc (hc.trans hcd) hl.le hc0.le
  rw [show 1 / c - 1 / d = (d - c) / (c * d) by
    simpa only [one_div] using inv_sub_inv hc0.ne' hd0.ne']
  exact ⟨div_nonneg (sub_nonneg.mpr hcd) (mul_pos hc0 hd0).le,
    (div_le_iff₀ (mul_pos hc0 hd0)).mpr
      (hdelta.trans (mul_le_mul_of_nonneg_left hprod he))⟩

/-- The two coordinate widths control the reciprocal gap throughout an Ioc cell. -/
theorem cell_reciprocal_variation {a b da db l e : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ Ioc a (a + da) ×ˢ Ioc b (b + db))
    (hl : 0 < l) (hgap : l ≤ 1 - (a + da) - (b + db))
    (he : 0 ≤ e) (hwidth : da + db ≤ e * (l * l)) :
    0 ≤ 1 / (1 - (a + da) - (b + db)) - 1 / (1 - x.1 - x.2) ∧
      1 / (1 - (a + da) - (b + db)) - 1 / (1 - x.1 - x.2) ≤ e := by
  apply reciprocal_variation hl hgap (by linarith [hx.1.2, hx.2.2]) he
  linarith [hx.1.1, hx.2.1]

/-- Distinct natural indices select disjoint half-open intervals. -/
private theorem Ioc_index_unique {a : ℕ → ℝ} (ha : Monotone a)
    {i j : ℕ} {x : ℝ} (hi : x ∈ Ioc (a i) (a (i + 1)))
    (hj : x ∈ Ioc (a j) (a (j + 1))) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact not_lt_of_ge (ha (by omega : i + 1 ≤ j)) (hj.1.trans_le hi.2)
  · exact not_lt_of_ge (ha (by omega : j + 1 ≤ i)) (hi.1.trans_le hj.2)

/-- Product cells inherit exact disjointness, including grid lines. -/
theorem cells_pairwiseDisjoint (n : ℕ) (a b : ℕ → ℝ)
    (ha : Monotone a) (hb : Monotone b) :
    (Set.univ : Set (Fin n × Fin n)).Pairwise
      (Function.onFun Disjoint (fun q =>
        Ioc (a q.1) (a (q.1 + 1)) ×ˢ Ioc (b q.2) (b (q.2 + 1)))) := by
  intro q _ r _ hqr
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hqr
  exact Prod.ext (Fin.ext (Ioc_index_unique ha hx.1 hy.1))
    (Fin.ext (Ioc_index_unique hb hx.2 hy.2))

/-- Exact volume of an open vertical strip of constant width over a closed base.
No slope or sign restriction on the moving lower boundary is needed. -/
theorem volume_strip (a b w : ℝ) (f : ℝ → ℝ)
    (hs : MeasurableSet {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ f x.1 < x.2 ∧ x.2 < f x.1 + w})
    (hw : 0 ≤ w) :
    volume {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ f x.1 < x.2 ∧ x.2 < f x.1 + w} =
      ENNReal.ofReal (w * (b - a)) := by
  classical
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply hs]
  have hfun : (fun u : ℝ => volume (Prod.mk u ⁻¹'
      {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ f x.1 < x.2 ∧ x.2 < f x.1 + w})) =
      (Icc a b).indicator (fun _ => ENNReal.ofReal w) := by
    funext u
    by_cases hu : u ∈ Icc a b
    · simp only [Set.preimage_ofPred_eq, hu, true_and, Set.indicator_of_mem hu]
      change volume (Ioo (f u) (f u + w)) = _
      rw [Real.volume_Ioo, add_sub_cancel_left]
    · simp only [Set.preimage_ofPred_eq, hu, false_and, Set.ofPred_false,
        measure_empty, Set.indicator_of_notMem hu]
  rw [hfun, lintegral_indicator measurableSet_Icc, setLIntegral_const,
    Real.volume_Icc, ← ENNReal.ofReal_mul hw]

/-- Evaluation of a weighted cell sum uses the actual density at the point. -/
theorem weighted_sum_eq_of_mem {α ι : Type*} (s : Finset ι) (C : ι → Set α)
    (k : ι → ℝ) (d : α → ℝ)
    (hd : (Set.univ : Set ι).Pairwise (Function.onFun Disjoint C))
    {q : ι} (hq : q ∈ s) {x : α} (hx : x ∈ C q) :
    (∑ r ∈ s, k r * (C r).indicator d x) = k q * d x := by
  classical
  rw [Finset.sum_eq_single q]
  · rw [indicator_of_mem hx]
  · intro r _ hrq
    rw [indicator_of_notMem (fun hr =>
      Set.disjoint_left.mp (hd (mem_univ q) (mem_univ r) hrq.symm) hx hr), mul_zero]
  · exact fun h => (h hq).elim

/-- The weighted sum has no contribution outside the selected union. -/
theorem weighted_sum_zero {α ι : Type*} (s : Finset ι) (C : ι → Set α)
    (k : ι → ℝ) (d : α → ℝ) {x : α} (hx : x ∉ ⋃ q ∈ s, C q) :
    (∑ q ∈ s, k q * (C q).indicator d x) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  rw [indicator_of_notMem (fun h => hx (Set.mem_iUnion₂.mpr ⟨q, hq, h⟩)), mul_zero]

/-- A bounded density transports kernel oscillation without dropping the weight. -/
theorem weighted_error {k k' d D e : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ D)
    (he : 0 ≤ e) (hk : k' - k ≤ e) : k' * d ≤ k * d + e * D := by
  have h := mul_le_mul hk hd hd0 he
  nlinarith

/-- Three measurable strips may overlap. This specializes the accepted excess-cover
integral theorem, keeping their individual volumes and the actual weighted functions. -/
theorem integral_sub_le_three_strips
    (G S A E₀ E₁ E₂ : Set (ℝ × ℝ)) (g f : ℝ × ℝ → ℝ)
    (e M v₀ v₁ v₂ : ℝ) (hg : Integrable g) (hf : IntegrableOn f S)
    (hS : MeasurableSet S) (hA : MeasurableSet A) (hAv : volume A = 1)
    (hE₀ : MeasurableSet E₀) (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂)
    (hV₀ : volume E₀ = ENNReal.ofReal v₀)
    (hV₁ : volume E₁ = ENNReal.ofReal v₁)
    (hV₂ : volume E₂ = ENNReal.ofReal v₂)
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (he : 0 ≤ e) (hM : 0 ≤ M) (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hzero : ∀ x, x ∉ G → g x = 0) (hinside : G ∩ S ⊆ A)
    (hlocal : ∀ x ∈ G ∩ S, g x ≤ f x + e)
    (hcover : G \ S ⊆ E₀ ∪ E₁ ∪ E₂) (hcap : ∀ x ∈ G \ S, g x ≤ M) :
    (∫ x, g x) - (∫ x in S, f x) ≤ e + (v₀ + v₁ + v₂) * M := by
  classical
  let E : Fin 3 → Set (ℝ × ℝ) := ![E₀, E₁, E₂]
  have h := IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover
    volume G S A E g f e M hg hf hS hA (by rw [hAv]; norm_num)
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> simp [E, hV₀, hV₁, hV₂])
    he hM hf0 hzero hinside hlocal
    (by
      intro x hx
      rcases hcover hx with (h | h) | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩) hcap
  simpa [Fin.sum_univ_three, E, Measure.real_def, hAv, hV₀, hV₁, hV₂,
    ENNReal.toReal_ofReal hv₀, ENNReal.toReal_ofReal hv₁,
    ENNReal.toReal_ofReal hv₂, add_mul] using h

end MathlibNt.Analysis.LogGridEstimates
