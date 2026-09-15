import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureGrid

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def truncatedSixthClosureInf (g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf (g '' Icc a b)

theorem truncatedSixthClosure_inf_bounds {g : ℝ → ℝ} {M a b : ℝ}
    (hg : ∀ t, 0 ≤ g t ∧ g t ≤ M) (hab : a ≤ b) :
    0 ≤ truncatedSixthClosureInf g a b ∧ truncatedSixthClosureInf g a b ≤ M := by
  have hne : (g '' Icc a b).Nonempty := ⟨g a, mem_image_of_mem g ⟨le_rfl, hab⟩⟩
  have hbd : BddBelow (g '' Icc a b) := ⟨0, by
    rintro _ ⟨t, _, rfl⟩
    exact (hg t).1⟩
  exact ⟨le_csInf hne (by rintro _ ⟨t, _, rfl⟩; exact (hg t).1),
    (csInf_le hbd (mem_image_of_mem g ⟨le_rfl, hab⟩)).trans (hg a).2⟩

theorem truncatedSixthClosure_inf_le {g : ℝ → ℝ} {a b t : ℝ}
    (hg : ∀ t, 0 ≤ g t) (ht : t ∈ Icc a b) :
    truncatedSixthClosureInf g a b ≤ g t :=
  csInf_le ⟨0, by rintro _ ⟨s, _, rfl⟩; exact hg s⟩ (mem_image_of_mem g ht)

theorem truncatedSixthClosure_inf_tendsto {g : ℝ → ℝ} {a b : ℕ → ℝ} {s : ℝ}
    (hg : ∀ t, 0 ≤ g t) (hc : ContinuousAt g s)
    (hab : ∀ n, a n ≤ b n) (ha : Tendsto a atTop (𝓝 s)) (hb : Tendsto b atTop (𝓝 s)) :
    Tendsto (fun n => truncatedSixthClosureInf g (a n) (b n)) atTop (𝓝 (g s)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (half_pos hε)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((ha.eventually (Metric.ball_mem_nhds s hr)).and (hb.eventually (Metric.ball_mem_nhds s hr)))
  refine ⟨T, fun n hn => ?_⟩
  have ha' := abs_lt.mp (show |a n - s| < r by simpa [Real.dist_eq] using (hT n hn).1)
  have hb' := abs_lt.mp (show |b n - s| < r by simpa [Real.dist_eq] using (hT n hn).2)
  have hgclose (t : ℝ) (ht : t ∈ Icc (a n) (b n)) : |g t - g s| < ε / 2 := by
    apply hclose
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hne : (g '' Icc (a n) (b n)).Nonempty :=
    ⟨g (a n), mem_image_of_mem g ⟨le_rfl, hab n⟩⟩
  have hlo : g s - ε / 2 ≤ truncatedSixthClosureInf g (a n) (b n) := by
    apply le_csInf hne
    rintro _ ⟨t, ht, rfl⟩
    linarith [(abs_lt.mp (hgclose t ht)).1]
  have hhi := (truncatedSixthClosure_inf_le hg ⟨le_rfl, hab n⟩).trans
    (show g (a n) ≤ g s + ε / 2 by linarith [(abs_lt.mp (hgclose (a n) ⟨le_rfl, hab n⟩)).2])
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

noncomputable def truncatedSixthClosureRegion (gain : Bool) (δ : ℝ) : Set (ℝ × ℝ) :=
  if gain then {v | truncatedSixthLowerAdmissibleRegion δ v.1 v.2}
  else {v | truncatedSixthLowerWedge δ v.1 v.2}

noncomputable def truncatedSixthClosureCoefficient (gain : Bool) (δ : ℝ) (s : ℝ) : ℝ :=
  if gain then truncatedSixthMassEffective δ s
  else wuLowerCoefficient (truncatedSixthMassClip s)

noncomputable def truncatedSixthClosureInner (gain : Bool) (δ : ℝ) (n : ℕ) :
    Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun j =>
    truncatedSixthClosureLower n j ∈ truncatedSixthClosureRegion gain δ ∧
    truncatedSixthClosureUpper n j ∈ truncatedSixthClosureRegion gain δ)

noncomputable def truncatedSixthClosureWeight (gain : Bool) (δ : ℝ) (n : ℕ) (j : ℕ × ℕ) : ℝ :=
  truncatedSixthClosureInf (truncatedSixthClosureCoefficient gain δ)
    (truncatedSixthLowerS δ (truncatedSixthClosureUpper n j).1 (truncatedSixthClosureUpper n j).2)
    (truncatedSixthLowerS δ (truncatedSixthClosureLower n j).1 (truncatedSixthClosureLower n j).2)

theorem truncatedSixthClosure_s_order {δ : ℝ} {l u : ℝ × ℝ} (h : l ≤ u) :
    truncatedSixthLowerS δ u.1 u.2 ≤ truncatedSixthLowerS δ l.1 l.2 := by
  unfold truncatedSixthLowerS
  apply div_le_div_of_nonneg_right _ truncatedSixthLower_parameters.1.le
  linarith [h.1, h.2]

theorem truncatedSixthClosure_corners_order (n : ℕ) (j : ℕ × ℕ) :
    truncatedSixthClosureLower n j ≤ truncatedSixthClosureUpper n j :=
  ⟨(truncatedSixthClosure_lo_lt_hi _ _).le, (truncatedSixthClosure_lo_lt_hi _ _).le⟩

theorem truncatedSixthClosure_region_between {gain : Bool} {δ : ℝ} {l u v : ℝ × ℝ}
    (hl : l ∈ truncatedSixthClosureRegion gain δ) (hu : u ∈ truncatedSixthClosureRegion gain δ)
    (hv : l ≤ v ∧ v ≤ u) : v ∈ truncatedSixthClosureRegion gain δ := by
  have hR {l u : ℝ × ℝ}
      (hl : truncatedSixthLowerRegion δ l.1 l.2) (hu : truncatedSixthLowerRegion δ u.1 u.2)
      (hvl : l ≤ v) (hvu : v ≤ u) : truncatedSixthLowerRegion δ v.1 v.2 :=
    ⟨hl.1.trans hvl.1, hvu.1.trans hu.2.1, hl.2.2.1.trans hvl.2,
      hvu.2.trans hu.2.2.2.1, (add_le_add hvu.1 hvu.2).trans hu.2.2.2.2⟩
  cases gain
  · exact ⟨hR hl.1 hu.1 hv.1 hv.2, hl.2.trans_le hv.1.2⟩
  · exact ⟨hR hl.1 hu.1 hv.1 hv.2, hv.2.2.trans hu.2⟩

theorem truncatedSixthClosure_region_bounds {gain : Bool} {δ : ℝ} {v : ℝ × ℝ}
    (hv : v ∈ truncatedSixthClosureRegion gain δ) :
    truncatedSixthLowerRegion δ v.1 v.2 := by
  cases gain <;> exact hv.1

theorem truncatedSixthClosure_region_frontier (gain : Bool) (δ : ℝ) :
    volume (frontier (truncatedSixthClosureRegion gain δ)) = 0 := by
  cases gain
  · apply Convex.addHaar_frontier
    intro v hv w hw A B hA hB hsum
    refine ⟨(truncatedSixthMass_regions_convex δ).1 hv.1 hw.1 hA hB hsum, ?_⟩
    change truncatedSixthLowerC δ / 2 < A * v.2 + B * w.2
    have hEq : A * (truncatedSixthLowerC δ / 2) + B * (truncatedSixthLowerC δ / 2) =
        truncatedSixthLowerC δ / 2 := by rw [← add_mul, hsum, one_mul]
    by_cases ha : A = 0
    · have hb : B = 1 := by linarith
      simpa [ha, hb] using hw.2
    · have hlt := mul_lt_mul_of_pos_left hv.2 (lt_of_le_of_ne hA (Ne.symm ha))
      have hle := mul_le_mul_of_nonneg_left hw.2.le hB
      linarith
  · exact (truncatedSixthMass_regions_convex δ).2.addHaar_frontier volume

theorem truncatedSixthClosure_coefficient_bounds {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (gain : Bool) (s : ℝ) :
    0 ≤ truncatedSixthClosureCoefficient gain δ s ∧
      truncatedSixthClosureCoefficient gain δ s ≤ 10 := by
  have hs := truncatedSixthMass_clip_bounds s
  have he := truncatedSixthLower_effective_bounds hδ hδhi hs
  cases gain
  · have ha : 0 ≤ wuLowerCoefficient (truncatedSixthMassClip s) := by
      unfold wuLowerCoefficient
      have hf := MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965f_nonneg
        (show 0 < truncatedSixthMassClip s by linarith [hs.1])
      have hs0 : 0 ≤ truncatedSixthMassClip s := by linarith [hs.1]
      positivity
    have hh := wuImprovementLimit_nonneg false hδ (by linarith)
      (s := truncatedSixthMassClip s) (by linarith [hs.1]) (by linarith [hs.2])
    exact ⟨ha, by dsimp [truncatedSixthClosureCoefficient]; linarith [he.2]⟩
  · exact he

theorem truncatedSixthClosure_weight_bounds {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (gain : Bool) (n : ℕ) (j : ℕ × ℕ) :
    0 ≤ truncatedSixthClosureWeight gain δ n j ∧ truncatedSixthClosureWeight gain δ n j ≤ 10 :=
  truncatedSixthClosure_inf_bounds (truncatedSixthClosure_coefficient_bounds hδ hδhi gain)
    (truncatedSixthClosure_s_order (truncatedSixthClosure_corners_order n j))

end Wu2008DoubleSieve
