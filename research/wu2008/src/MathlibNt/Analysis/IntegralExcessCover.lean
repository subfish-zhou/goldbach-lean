import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Tactic.Linarith

open MeasureTheory Set Finset
open scoped BigOperators ENNReal

namespace MathlibNt.Analysis.IntegralExcessCover

/-- Pointwise payment for a finite, possibly overlapping cover of the excess. -/
theorem majorized_of_excess_cover
    {α ι : Type*} [Fintype ι]
    (G S A : Set α) (E : ι → Set α) (g f : α → ℝ) (e M : ℝ)
    (he : 0 ≤ e) (hM : 0 ≤ M)
    (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hzero : ∀ x, x ∉ G → g x = 0)
    (hinside : G ∩ S ⊆ A)
    (hlocal : ∀ x ∈ G ∩ S, g x ≤ f x + e)
    (hcover : ∀ x ∈ G \ S, ∃ i, x ∈ E i)
    (hcap : ∀ x ∈ G \ S, g x ≤ M) :
    ∀ x, g x ≤ S.indicator f x + A.indicator (fun _ => e) x +
      ∑ i, (E i).indicator (fun _ => M) x := by
  classical
  have hs0 (x : α) : 0 ≤ S.indicator f x := indicator_nonneg hf0 x
  have ha0 (x : α) : 0 ≤ A.indicator (fun _ => e) x :=
    indicator_nonneg (fun _ _ => he) x
  have hi0 (i : ι) (x : α) : 0 ≤ (E i).indicator (fun _ => M) x :=
    indicator_nonneg (fun _ _ => hM) x
  have hsum0 (x : α) : 0 ≤ ∑ i, (E i).indicator (fun _ => M) x :=
    Finset.sum_nonneg (fun i _ => hi0 i x)
  intro x
  by_cases hxG : x ∈ G
  · by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, indicator_of_mem (hinside ⟨hxG, hxS⟩)]
      exact (hlocal x ⟨hxG, hxS⟩).trans (le_add_of_nonneg_right (hsum0 x))
    · obtain ⟨i, hxi⟩ := hcover x ⟨hxG, hxS⟩
      have hpay : M ≤ ∑ j, (E j).indicator (fun _ => M) x := by
        calc
          M = (E i).indicator (fun _ => M) x := (indicator_of_mem hxi (fun _ => M)).symm
          _ ≤ ∑ j, (E j).indicator (fun _ => M) x :=
            Finset.single_le_sum (fun j _ => hi0 j x) (Finset.mem_univ i)
      rw [indicator_of_notMem hxS]
      linarith [hcap x ⟨hxG, hxS⟩, ha0 x]
  · rw [hzero x hxG]
    exact add_nonneg (add_nonneg (hs0 x) (ha0 x)) (hsum0 x)

/-- Local error on the common region plus a finite cover of the excess.
The cover sets may overlap; neither S ⊆ G nor measurability of G is required.
All integrability hypotheses refer to the actual functions being integrated. -/
theorem integral_sub_setIntegral_le_of_excess_cover
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (G S A : Set α) (E : ι → Set α)
    (g f : α → ℝ) (e M : ℝ)
    (hg : Integrable g μ) (hf : IntegrableOn f S μ)
    (hS : MeasurableSet S) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞)
    (hE : ∀ i, MeasurableSet (E i)) (hEfin : ∀ i, μ (E i) ≠ ∞)
    (he : 0 ≤ e) (hM : 0 ≤ M)
    (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hzero : ∀ x, x ∉ G → g x = 0)
    (hinside : G ∩ S ⊆ A)
    (hlocal : ∀ x ∈ G ∩ S, g x ≤ f x + e)
    (hcover : ∀ x ∈ G \ S, ∃ i, x ∈ E i)
    (hcap : ∀ x ∈ G \ S, g x ≤ M) :
    (∫ x, g x ∂μ) - (∫ x in S, f x ∂μ) ≤
      μ.real A * e + ∑ i, μ.real (E i) * M := by
  classical
  have hmajor := majorized_of_excess_cover G S A E g f e M
    he hM hf0 hzero hinside hlocal hcover hcap
  have hsi : Integrable (S.indicator f) μ := hf.integrable_indicator hS
  have hai : Integrable (A.indicator (fun _ => e)) μ :=
    (integrableOn_const hAfin).integrable_indicator hA
  have hei (i : ι) : Integrable ((E i).indicator (fun _ => M)) μ :=
    (integrableOn_const (hEfin i)).integrable_indicator (hE i)
  have hsum : Integrable (fun x => ∑ i, (E i).indicator (fun _ => M) x) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hei i)
  have hmono := integral_mono hg ((hsi.add hai).add hsum) hmajor
  have hOuter := integral_add (hsi.add hai) hsum
  have hInner := integral_add hsi hai
  simp only [Pi.add_apply] at hmono hOuter hInner
  rw [hOuter, hInner,
    integral_indicator hS, integral_indicator_const e hA,
    integral_finsetSum Finset.univ (fun i _ => hei i)] at hmono
  have hEq : (∑ i, ∫ x, (E i).indicator (fun _ => M) x ∂μ) =
      ∑ i, μ.real (E i) * M := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [smul_eq_mul] using integral_indicator_const (μ := μ) M (hE i)
  rw [hEq] at hmono
  simp only [smul_eq_mul] at hmono
  linarith

end MathlibNt.Analysis.IntegralExcessCover
