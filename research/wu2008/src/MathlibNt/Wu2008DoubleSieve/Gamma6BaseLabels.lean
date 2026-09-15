import MathlibNt.Wu2008DoubleSieve.Gamma6BaseTransport
import MathlibNt.Wu2008DoubleSieve.Gamma6BaseUpper

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

theorem gamma6Base_rect_mem_iff {i k N : ℕ} {δ Δ A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hA : gamma5MassA ≤ A) (hB : B ≤ gamma6BaseB)
    (hC : gamma6BaseC ≤ C) (hD : D ≤ gamma6BaseF)
    (x : Gamma5ClassicalLabel) :
    x ∈ gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D ↔
      x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
      x.2 ∈ gamma6BasePairs N ((N : ℝ) ^ (1 / 2 - δ) / x.1) A B C D := by
  constructor
  · intro hx
    obtain ⟨hx, hcoord⟩ := mem_filter.mp hx
    obtain ⟨hd, hp, hq, hpN, hqN, _hz, hpu, _hql, hqu⟩ :=
      (gamma6Base_mem_labels_iff hN hδ hδhi hb x).mp hx
    have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
    refine ⟨hd, mem_product.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨?_, hpu⟩, hpN⟩,
      mem_filter.mpr ⟨mem_filter.mpr ⟨?_, hqu⟩, hqN⟩⟩⟩
    · exact (gamma5Mass_coordinate_mem_iff hR _).mpr ⟨hp, hcoord.1, hcoord.2.1⟩
    · exact (gamma5Mass_coordinate_mem_iff hR _).mpr ⟨hq, hcoord.2.2.1, hcoord.2.2.2⟩
  · rintro ⟨hd, hpairs⟩
    have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
    obtain ⟨hpm, hqm⟩ := mem_product.mp hpairs
    obtain ⟨⟨hpm, hpu⟩, hpN⟩ := mem_filter.mp hpm |>.imp_left mem_filter.mp
    obtain ⟨⟨hqm, hqu⟩, hqN⟩ := mem_filter.mp hqm |>.imp_left mem_filter.mp
    obtain ⟨hp, hpa, hpb⟩ := (gamma5Mass_coordinate_mem_iff hR _).mp hpm
    obtain ⟨hq, hqc, hqd⟩ := (gamma5Mass_coordinate_mem_iff hR _).mp hqm
    have hplow : ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma5MassA ≤ (x.2.1 : ℝ) := by
      have hm := (gamma5Mass_coordinate_mem_iff hR _).mpr ⟨hp, hA.trans hpa, hpb.trans hB⟩
      exact ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1) _)).mp hm).2.1
    have hqlow : ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma6BaseC ≤ (x.2.2 : ℝ) := by
      have hm := (gamma5Mass_coordinate_mem_iff hR _).mpr ⟨hq, hC.trans hqc, hqd.trans hD⟩
      exact ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1) _)).mp hm).2.1
    have hx := (gamma6Base_mem_labels_iff hN hδ hδhi hb x).mpr
      ⟨hd, hp, hq, hpN, hqN, hplow, hpu, hqlow, hqu⟩
    exact mem_filter.mpr ⟨hx, hpa, hpb, hqc, hqd⟩

theorem gamma6Base_sum_rect {i k N : ℕ} {δ Δ A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hA : gamma5MassA ≤ A) (hB : B ≤ gamma6BaseB)
    (hC : gamma6BaseC ≤ C) (hD : D ≤ gamma6BaseF)
    (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D, f x) =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ∑ pq ∈ gamma6BasePairs N ((N : ℝ) ^ (1 / 2 - δ) / d) A B C D, f (d, pq) := by
  let P := fun d => gamma6BasePairs N ((N : ℝ) ^ (1 / 2 - δ) / d) A B C D
  have he : gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D =
      (boxConvolutionSupport (convolutionWuWindows N Δ V)).biUnion
        (fun d => (P d).image (fun pq => (d, pq))) := by
    ext x
    rw [gamma6Base_rect_mem_iff hN hδ hδhi hb hA hB hC hD, Finset.mem_biUnion]
    constructor
    · rintro ⟨hd, hx⟩
      exact ⟨x.1, hd, mem_image.mpr ⟨x.2, hx, Prod.eta x⟩⟩
    · rintro ⟨d, hd, hx⟩
      obtain ⟨pq, hpq, heq⟩ := mem_image.mp hx
      cases heq
      exact ⟨hd, hpq⟩
  have hdis : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ e ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), d ≠ e →
        Disjoint ((P d).image (fun pq => (d, pq))) ((P e).image (fun pq => (e, pq))) := by
    intro d _ e _ hde
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨pq, _, heq⟩ := mem_image.mp hx
    obtain ⟨rs, _, heq'⟩ := mem_image.mp hy
    exact hde (congrArg Prod.fst (heq.trans heq'.symm))
  rw [he, sum_biUnion hdis]
  apply sum_congr rfl
  intro d _
  exact sum_image (fun pq _ rs _ heq => congrArg Prod.snd heq)

theorem gamma6Base_full_labels_eq {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V)
      gamma5MassA gamma6BaseB gamma6BaseC gamma6BaseF =
      gamma6BaseLabels N δ (convolutionWuWindows N Δ V) := by
  apply filter_eq_self.mpr
  intro x hx
  obtain ⟨hd, hp, hq, _hpN, _hqN, hpa, hpb, hqc, hqf⟩ :=
    (gamma6Base_mem_labels_iff hN hδ hδhi hb x).mp hx
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
  exact gamma6Base_pair_coordinates hR (by exact_mod_cast hp.pos) (by exact_mod_cast hq.pos)
    hpa hpb.le hqc hqf.le

theorem gamma6Base_label_eventually (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ∀ x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V),
        2 < x.2.1 ∧ 2 < x.2.2 := by
  have hα := (gamma5Classical_exponents_pos k hδ hδhi).1
  filter_upwards [((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (2 : ℝ)), eventually_ge_atTop (2 : ℕ)] with N hlarge hN
  intro i Δ V hb x hx
  have hg := gamma6Base_label_geometry hN hδ hδhi hb hx
  have hp : 2 < x.2.1 := by exact_mod_cast hlarge.trans_le hg.prime_lower
  exact ⟨hp, hp.trans hg.prime_order⟩

end Wu2008DoubleSieve
