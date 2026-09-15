import MathlibNt.Wu2008DoubleSieve.Gamma5MassTransport

/-!
# Exact rectangular masks and their product fibres

The full source triangle keeps its original closed lower cutoff, strict
prime ordering, and strict upper cutoff. Rectangle sides are closed.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def gamma5MassRectLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (A B C D : ℝ) : Finset Gamma5ClassicalLabel :=
  (gamma5ClassicalLabels N δ W).filter (fun x =>
    A ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 ∧
    gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 ≤ B ∧
    C ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ∧
    gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ≤ D)

theorem gamma5Mass_support_geometry {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {d : ℕ}
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    0 < d ∧ (N : ℝ) ^ wuLocalExponent k δ ≤ (N : ℝ) ^ (1 / 2 - δ) / d ∧
      1 < (N : ℝ) ^ (1 / 2 - δ) / d ∧
      0 < gamma5MassOldWeight N d ((N : ℝ) ^ (1 / 2 - δ)) := by
  have h := wuLocal_support_bounds (by omega) hδ hδhi hb.2.2.2.2.1
    ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
  have hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega))
      (wuLocalExponent_pos k hδ hδhi)).trans_le h.2.2
  refine ⟨h.1, h.2.2, hR, ?_⟩
  exact div_pos (wuSingularSeries_pos _ (Nat.mul_pos h.1 (by omega)))
    (mul_pos (by exact_mod_cast Nat.totient_pos.mpr h.1) (log_pos hR))

theorem gamma5Mass_rect_mem_iff {i k N : ℕ} {δ Δ A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hA : gamma5MassA ≤ A) (hB : B ≤ gamma5ClassicalB)
    (_hC : gamma5MassA ≤ C) (_hD : D ≤ gamma5ClassicalB)
    (x : Gamma5ClassicalLabel) :
    x ∈ gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D ↔
      x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
      x.2 ∈ gamma5MassPrimePairs N ((N : ℝ) ^ (1 / 2 - δ) / x.1) A B C D := by
  constructor
  · intro hx
    obtain ⟨hx, hcoord⟩ := mem_filter.mp hx
    obtain ⟨hd, hp, hq, hpN, hqN, _hz, hpq, hqu⟩ :=
      (gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mp hx
    have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
    refine ⟨hd, mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, hpq, hqu, hpN, hqN⟩⟩
    · exact (gamma5Mass_coordinate_mem_iff hR _).mpr ⟨hp, hcoord.1, hcoord.2.1⟩
    · exact (gamma5Mass_coordinate_mem_iff hR _).mpr ⟨hq, hcoord.2.2.1, hcoord.2.2.2⟩
  · rintro ⟨hd, hpairs⟩
    have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
    obtain ⟨hpairs, hpq, hqu, hpN, hqN⟩ := mem_filter.mp hpairs
    obtain ⟨hpm, hqm⟩ := mem_product.mp hpairs
    obtain ⟨hp, hpa, hpb⟩ := (gamma5Mass_coordinate_mem_iff hR _).mp hpm
    obtain ⟨hq, hqc, hqd⟩ := (gamma5Mass_coordinate_mem_iff hR _).mp hqm
    have hplow : ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma5MassA ≤ (x.2.1 : ℝ) := by
      have hm := (gamma5Mass_coordinate_mem_iff hR _).mpr
        ⟨hp, hA.trans hpa, hpb.trans hB⟩
      exact ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1) _)).mp hm).2.1
    have hx := (gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mpr
      ⟨hd, hp, hq, hpN, hqN, hplow, hpq, hqu⟩
    exact mem_filter.mpr ⟨hx, hpa, hpb, hqc, hqd⟩

theorem gamma5Mass_sum_rect {i k N : ℕ} {δ Δ A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hA : gamma5MassA ≤ A) (hB : B ≤ gamma5ClassicalB)
    (hC : gamma5MassA ≤ C) (hD : D ≤ gamma5ClassicalB)
    (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D, f x) =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ∑ pq ∈ gamma5MassPrimePairs N ((N : ℝ) ^ (1 / 2 - δ) / d) A B C D, f (d, pq) := by
  let P := fun d => gamma5MassPrimePairs N ((N : ℝ) ^ (1 / 2 - δ) / d) A B C D
  have he : gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D =
      (boxConvolutionSupport (convolutionWuWindows N Δ V)).biUnion
        (fun d => (P d).image (fun pq => (d, pq))) := by
    ext x
    rw [gamma5Mass_rect_mem_iff hN hδ hδhi hb hA hB hC hD, Finset.mem_biUnion]
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

theorem gamma5Mass_full_labels_eq {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    gamma5MassRectLabels N δ (convolutionWuWindows N Δ V)
      gamma5MassA gamma5ClassicalB gamma5MassA gamma5ClassicalB =
      gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) := by
  apply filter_eq_self.mpr
  intro x hx
  obtain ⟨hd, hp, hq, _hpN, _hqN, hz, hpq, hu⟩ :=
    (gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mp hx
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
  have hpq' : (x.2.1 : ℝ) ≤ x.2.2 := by exact_mod_cast hpq.le
  have hpm : x.2.1 ∈ gamma5MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / x.1)
      gamma5MassA gamma5ClassicalB :=
    (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1) _)).mpr
      ⟨hp, hz, hpq'.trans hu.le⟩
  have hqm : x.2.2 ∈ gamma5MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / x.1)
      gamma5MassA gamma5ClassicalB :=
    (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1) _)).mpr
      ⟨hq, hz.trans hpq', hu.le⟩
  exact ⟨((gamma5Mass_coordinate_mem_iff hR _).mp hpm).2.1,
    ((gamma5Mass_coordinate_mem_iff hR _).mp hpm).2.2,
    ((gamma5Mass_coordinate_mem_iff hR _).mp hqm).2.1,
    ((gamma5Mass_coordinate_mem_iff hR _).mp hqm).2.2⟩

end Wu2008DoubleSieve
