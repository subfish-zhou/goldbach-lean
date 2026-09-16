import Wu18938Campaign.M1.Confirmed.FullFiveRectangle
import Wu18938Campaign.M1.Confirmed.ProfileGrid

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullFive

open Wu2008DoubleSieve MotherPair Finset Set Real Filter MeasureTheory
open scoped Classical Topology

def domain (p : SecondFunctionalParameters) : Set (ℝ × ℝ) :=
  {v | PairRegion p .gammaFive v.1 v.2}

def kernel (p : SecondFunctionalParameters) (H : ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ domain p then H (p.S * (1 - v.1 - v.2)) * gainSmooth p v else 0

def gridInner (p : SecondFunctionalParameters) (n : ℕ) : Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun i =>
    1 / p.S < truncatedSixthClosureLo n i.1 ∧
    truncatedSixthClosureHi n i.1 < truncatedSixthClosureLo n i.2 ∧
    truncatedSixthClosureHi n i.2 < 1 / p.kappa2 ∧
    2 * truncatedSixthClosureHi n i.2 < 1 ∧
    1 < gridSample p .gammaFive n i ∧ gridSample p .gammaFive n i < 3)

def gridRectangle (p : SecondFunctionalParameters) (n : ℕ)
    (i : {i // i ∈ gridInner p n}) : Rectangle p where
  A := truncatedSixthClosureLo n i.val.1
  B := truncatedSixthClosureHi n i.val.1
  C := truncatedSixthClosureLo n i.val.2
  D := truncatedSixthClosureHi n i.val.2
  sample := gridSample p .gammaFive n i.val
  lowerP_lt_A := (mem_filter.mp i.property).2.1
  A_lt_B := truncatedSixthClosure_lo_lt_hi _ _
  B_lt_C := (mem_filter.mp i.property).2.2.1
  C_lt_D := truncatedSixthClosure_lo_lt_hi _ _
  D_lt_cap := (mem_filter.mp i.property).2.2.2.1
  twiceD_lt_one := (mem_filter.mp i.property).2.2.2.2.1
  sample_lower := (mem_filter.mp i.property).2.2.2.2.2.1
  sample_upper := (mem_filter.mp i.property).2.2.2.2.2.2
  ratio_lt_sample := lt_add_of_pos_right _ (by positivity)

def gridFamily (p : SecondFunctionalParameters) (n : ℕ) : Finset (Rectangle p) :=
  univ.image (gridRectangle p n)

theorem grid_inner_subset {p : SecondFunctionalParameters} {n : ℕ} {i : ℕ × ℕ}
    (hi : i ∈ gridInner p n) : truncatedSixthClosureCell n i ⊆ domain p := by
  let r := gridRectangle p n ⟨i,hi⟩
  intro v hv
  change v.1 ∈ Ico r.A r.B ∧ v.2 ∈ Ico r.C r.D at hv
  exact ⟨r.lowerP_lt_A.le.trans hv.1.1,
    hv.1.2.le.trans (r.B_lt_C.le.trans (r.C_lt_D.le.trans r.D_lt_cap.le)),
    hv.1.2.le.trans (r.B_lt_C.le.trans hv.2.1),hv.2.2.le.trans r.D_lt_cap.le⟩

theorem grid_family_pairwise (p : SecondFunctionalParameters) (n : ℕ) :
    (↑(gridFamily p n) : Set (Rectangle p)).Pairwise (fun r s =>
      Disjoint (Ico r.A r.B ×ˢ Ico r.C r.D) (Ico s.A s.B ×ˢ Ico s.C s.D)) := by
  intro r hr s hs hrs
  obtain ⟨i,_,rfl⟩ := mem_image.mp hr
  obtain ⟨k,_,rfl⟩ := mem_image.mp hs
  apply Set.disjoint_left.mpr
  intro v hv hw
  have he : i.val = k.val := truncatedSixthClosure_cell_unique hv hw
  exact hrs (congrArg (gridRectangle p n) (Subtype.ext he))

theorem grid_rectangle_injective (p : SecondFunctionalParameters) (n : ℕ) :
    Function.Injective (gridRectangle p n) := by
  intro i k he
  apply Subtype.ext
  have hA := congrArg Rectangle.A he
  have hC := congrArg Rectangle.C he
  change truncatedSixthClosureLo n i.val.1 = truncatedSixthClosureLo n k.val.1 at hA
  change truncatedSixthClosureLo n i.val.2 = truncatedSixthClosureLo n k.val.2 at hC
  apply Prod.ext
  · exact_mod_cast (div_left_inj' (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)).mp hA
  · exact_mod_cast (div_left_inj' (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)).mp hC

theorem full_ratio_mem {p : SecondFunctionalParameters} (hp : WuPaper.R2Gamma5.FullParameters p)
    {v : ℝ × ℝ} (hv : v ∈ domain p) :
    p.S * (1 - v.1 - v.2) ∈ Set.Icc (1 : ℝ) 3 :=
  WuPaper.R2Gamma5.full_ratio_mem hp ⟨hv.1,hv.2.1⟩ ⟨hv.1.trans hv.2.2.1,hv.2.2.2⟩

theorem strict_ae {p : SecondFunctionalParameters} (hp : WuPaper.R2Gamma5.FullParameters p) :
    ∀ᵐ v : ℝ × ℝ, v ∈ domain p →
      1 / p.S < v.1 ∧ v.1 < v.2 ∧ v.2 < 1 / p.kappa2 ∧
      2 * v.2 < 1 ∧ 1 < p.S * (1 - v.1 - v.2) ∧ p.S * (1 - v.1 - v.2) < 3 := by
  filter_upwards [gamma5Gain_vertical_ne_ae (1 / p.S),
    gamma5Gain_affine_ne_ae 0 1 (1 / p.kappa2) (by norm_num),
    gamma5Gain_affine_ne_ae 1 (-1) 0 (by norm_num),
    gain_ratio_ne_ae hp.toAnalyticParameters .gammaFive 1,
    gain_ratio_ne_ae hp.toAnalyticParameters .gammaFive 3] with v ha hb hc hd he
  intro hv
  have hr := full_ratio_mem hp hv
  have ho := parameter_order hp.toAnalyticParameters
  have hcap : 1 / p.kappa2 < 1 / 2 :=
    ho.2.2.2.1.trans_le ho.2.2.2.2.1 |>.trans ho.2.2.2.2.2
  simp only [zero_mul,one_mul,zero_add] at hb
  refine ⟨lt_of_le_of_ne hv.1 ha.symm,?_,
    lt_of_le_of_ne hv.2.2.2 hb,?_,lt_of_le_of_ne hr.1 hd.symm,lt_of_le_of_ne hr.2 he⟩
  · apply lt_of_le_of_ne hv.2.2.1
    intro heq
    apply hc
    rw [heq]
    ring
  · linarith [hv.2.2.2]

def approximation (p : SecondFunctionalParameters) (H : ℝ → ℝ) (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ i ∈ gridInner p n, (truncatedSixthClosureCell n i).indicator
    (fun v => H (gridSample p .gammaFive n i) * gainSmooth p v) v

theorem at_cell {p : SecondFunctionalParameters} {H : ℝ → ℝ}
    {n : ℕ} {i : ℕ × ℕ} {v : ℝ × ℝ}
    (hi : i ∈ gridInner p n) (hv : v ∈ truncatedSixthClosureCell n i) :
    approximation p H n v = H (gridSample p .gammaFive n i) * gainSmooth p v := by
  unfold approximation
  rw [sum_eq_single i]
  · exact Set.indicator_of_mem hv _
  · intro k _ hki
    exact Set.indicator_of_notMem (fun hk => hki (truncatedSixthClosure_cell_unique hk hv)) _
  · exact fun hn => False.elim (hn hi)

theorem outside {p : SecondFunctionalParameters} {H : ℝ → ℝ}
    {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ i ∈ gridInner p n, v ∉ truncatedSixthClosureCell n i) :
    approximation p H n v = 0 :=
  sum_eq_zero (fun i hi => Set.indicator_of_notMem (h i hi) _)

theorem approximation_bound {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} (hH : ∀ s ∈ Icc (1 : ℝ) 3, 0 ≤ H s ∧ H s ≤ 1)
    (n : ℕ) (v : ℝ × ℝ) :
    ‖approximation p H n v‖ ≤ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
      (fun _ => 25 / (1 - 2 * (1 / p.kappa3))) v := by
  by_cases hex : ∃ i ∈ gridInner p n, v ∈ truncatedSixthClosureCell n i
  · obtain ⟨i,hi,hv⟩ := hex
    have hu := truncatedSixthClosure_cell_mem (mem_filter.mp hi).1 hv
    rw [at_cell hi hv,Set.indicator_of_mem
      (show v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨⟨hu.1.1,hu.1.2.le⟩,⟨hu.2.1,hu.2.2.le⟩⟩)]
    let r := gridRectangle p n ⟨i,hi⟩
    have hh := hH r.sample ⟨r.sample_lower.le,r.sample_upper.le⟩
    change 0 ≤ H (gridSample p .gammaFive n i) ∧ H (gridSample p .gammaFive n i) ≤ 1 at hh
    have hk := gain_smooth_bounds hp v
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hh.1 hk.1)]
    exact (mul_le_of_le_one_left hk.1 hh.2).trans hk.2
  · rw [outside (by simpa only [not_exists,not_and] using hex),norm_zero]
    exact Set.indicator_nonneg (fun _ _ => (gain_smooth_bounds hp v).1.trans
      (gain_smooth_bounds hp v).2) _

end Wu18938Campaign.M1.Confirmed.FullFive
