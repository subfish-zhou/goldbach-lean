import MathlibNt.Wu2008DoubleSieve.SingleUpperHCoarseEnvelope

namespace Wu2008DoubleSieve.SingleUpperHCoarseLimit
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperHSource SingleUpperHIntegral SingleUpperHDarboux
open SingleUpperHPrimeQuadrature SingleUpperHCoarseEnvelope
open scoped Classical Topology

noncomputable def coarseMesh (δ : ℝ) (n : ℕ) : ℝ :=
  (((1/2-δ)/2)-truncatedSixthLowerAlpha/2)/(n+1)

noncomputable def coarseNode (δ : ℝ) (n i : ℕ) : ℝ :=
  point (truncatedSixthLowerAlpha/2) (coarseMesh δ n) i

noncomputable def clippedNode (δ : ℝ) (n i : ℕ) : ℝ :=
  max (truncatedSixthLowerAlpha-coarseMesh δ n) (coarseNode δ n i)

noncomputable def coarsePrimeMass (δ η : ℝ) (n N : ℕ) : ℝ :=
  ∑ i ∈ range (n+1), (effective δ (argument δ (coarseNode δ n (i-1)))+η) *
    ∑ p ∈ primesIcc ((N : ℝ)^(clippedNode δ n i)) ((N : ℝ)^(clippedNode δ n (i+1))),
      1/((p : ℝ)*((1/2-δ)-log p/log N))

noncomputable def coarseIntegral (δ η : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n+1), (effective δ (argument δ (coarseNode δ n (i-1)))+η) *
    ∫ t in clippedNode δ n i..clippedNode δ n (i+1), (t*((1/2-δ)-t))⁻¹

theorem mesh_pos {δ : ℝ} (hδhi : δ ≤ 1/100) (n : ℕ) : 0 < coarseMesh δ n := by
  apply div_pos _ (by positivity)
  norm_num [truncatedSixthLowerAlpha] at *
  linarith

@[simp] theorem node_zero (δ : ℝ) (n : ℕ) : coarseNode δ n 0 = truncatedSixthLowerAlpha/2 := by
  simp [coarseNode]

@[simp] theorem node_end (δ : ℝ) (n : ℕ) : coarseNode δ n (n+1) = (1/2-δ)/2 := by
  unfold coarseNode point coarseMesh
  push_cast
  rw [mul_div_cancel₀ _ (by positivity : (n : ℝ)+1 ≠ 0)]
  ring

theorem node_mono {δ : ℝ} (hδhi : δ ≤ 1/100) (n : ℕ) : Monotone (coarseNode δ n) :=
  point_mono (mesh_pos hδhi n).le

theorem node_mem {δ : ℝ} (hδhi : δ ≤ 1/100) {n i : ℕ} (hi : i ≤ n+1) :
    coarseNode δ n i ∈ Icc (truncatedSixthLowerAlpha/2) ((1/2-δ)/2) := by
  have hm := node_mono hδhi n
  constructor
  · simpa using hm (Nat.zero_le i)
  · simpa using hm hi

theorem effective_slab_nonneg {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (truncatedSixthLowerAlpha/2) ((1/2-δ)/2)) :
    0 ≤ effective δ (argument δ t) := by
  have hs := argument_bounds hδ hδhi ht.1 ht.2
  exact effective_nonneg hδ (by linarith) hs.1 hs.2

theorem effective_slab_bound {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (truncatedSixthLowerAlpha/2) ((1/2-δ)/2)) :
    effective δ (argument δ t) ≤ effective δ (argument δ (truncatedSixthLowerAlpha/2)) :=
  effective_argument_antitone hδ hδhi ⟨le_rfl,ht.1.trans ht.2⟩ ht ht.1

/-- The fixed lower overhang is paid by its actual width, not discarded. -/
theorem effective_overhang {δ d : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hd : truncatedSixthLowerAlpha/2 ≤ d) (hda : d ≤ truncatedSixthLowerAlpha) :
    (∫ t in d..((1/2-δ)/2), effectiveKernel δ t) ≤
      (∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t) +
      200*(truncatedSixthLowerAlpha-d)*
        effective δ (argument δ (truncatedSixthLowerAlpha/2)) := by
  have hab : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hid := effective_integrable hδ hδhi hd hda hab
  have hia := effective_integrable hδ hδhi
    (by norm_num [truncatedSixthLowerAlpha]) hab le_rfl
  have hsum := intervalIntegral.integral_add_adjacent_intervals hid hia
  have hm := intervalIntegral.integral_mono_on hda hid
    (intervalIntegrable_const (c := 200*effective δ (argument δ (truncatedSixthLowerAlpha/2))))
    (fun t ht => by
      have hs : t ∈ Icc (truncatedSixthLowerAlpha/2) ((1/2-δ)/2) := ⟨hd.trans ht.1,ht.2.trans hab⟩
      have hf := effective_slab_bound hδ hδhi hs
      have hb := reciprocal_bounds hδhi hs.1 hs.2
      have hM := effective_slab_nonneg hδ hδhi ⟨le_rfl,hs.1.trans hs.2⟩
      have hp := mul_le_mul hf hb.2 hb.1 hM
      simpa only [effectiveKernel,div_eq_mul_inv,mul_comm] using hp)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hm
  linarith only [hsum,hm]

/-- Full coarse integral payment, including the one-cell predecessor lag,
the fixed lower overhang, and source slack on the complete kernel mass. -/
theorem coarse_integral_upper {δ η : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 ≤ η)
    (hsmall : coarseMesh δ n ≤ truncatedSixthLowerAlpha/2) :
    coarseIntegral δ η n ≤
      (∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t) +
      600*coarseMesh δ n*effective δ (argument δ (truncatedSixthLowerAlpha/2)) + 200*η := by
  let d := truncatedSixthLowerAlpha-coarseMesh δ n
  let f := fun t => effective δ (argument δ t)
  let w := fun t => (t*((1/2-δ)-t))⁻¹
  have hh := mesh_pos hδhi n
  have hd : truncatedSixthLowerAlpha/2 ≤ d := by dsimp [d]; linarith
  have hda : d ≤ truncatedSixthLowerAlpha := by dsimp [d]; linarith
  have hab : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hm := node_mono hδhi n
  have hf := effective_argument_antitone hδ hδhi
  have hc := reciprocal_continuous hδhi (a := truncatedSixthLowerAlpha/2) le_rfl
    (hd.trans (hda.trans hab)) (b := (1/2-δ)/2) le_rfl
  rw [uIcc_of_le (hd.trans (hda.trans hab))] at hc
  have hlag := clipped_lag_darboux (f := f) (w := w) (x := coarseNode δ n) (n := n+1)
    hm (by simpa using hd) (by simpa using hda.trans hab)
    (by simpa only [node_zero,node_end] using hf) (by simpa only [node_zero,node_end] using hc)
    (fun t ht => (reciprocal_bounds hδhi (by simpa using ht.1) (by simpa using ht.2)).1)
    (fun t ht => (reciprocal_bounds hδhi (by simpa using ht.1) (by simpa using ht.2)).2)
    (by norm_num : (0 : ℝ) ≤ 200) hh.le (fun i _ => by
      change point _ _ (i+1)-point _ _ i ≤ coarseMesh δ n
      rw [point_succ]
      linarith)
  simp only [node_zero,node_end] at hlag
  have hwi (i : ℕ) (hi : i < n+1) :
      IntervalIntegrable w volume (clippedNode δ n i) (clippedNode δ n (i+1)) := by
    have hlo : truncatedSixthLowerAlpha/2 ≤ clippedNode δ n i := hd.trans (le_max_left _ _)
    have hhi : clippedNode δ n (i+1) ≤ (1/2-δ)/2 :=
      max_le (hda.trans hab) (node_mem hδhi (by omega)).2
    have hord : clippedNode δ n i ≤ clippedNode δ n (i+1) := max_le_max le_rfl (hm (by omega))
    exact ((hc.mono (by rw [uIcc_of_le hord]; exact Icc_subset_Icc hlo hhi))).intervalIntegrable
  have hs := intervalIntegral.sum_integral_adjacent_intervals hwi
  have hz0 : clippedNode δ n 0 = d := by simp only [clippedNode,node_zero]; exact max_eq_left hd
  have hzn : clippedNode δ n (n+1) = (1/2-δ)/2 := by
    simp only [clippedNode,node_end]
    exact max_eq_right (hda.trans hab)
  rw [hz0,hzn] at hs
  have hmass : (∫ t in d..((1/2-δ)/2), w t) ≤ 200 := by
    have hwi' := (hc.mono (by rw [uIcc_of_le (hda.trans hab)]; exact Icc_subset_Icc hd le_rfl)).intervalIntegrable (μ := volume)
    have h := intervalIntegral.integral_mono_on (hda.trans hab) hwi'
      (intervalIntegrable_const (c := (200 : ℝ))) (fun t ht =>
        (reciprocal_bounds hδhi (hd.trans ht.1) ht.2).2)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at h
    have hd0 : 0 < d := lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha]) hd
    linarith
  have heq : coarseIntegral δ η n =
      (∑ i ∈ range (n+1), f (coarseNode δ n (i-1)) * ∫ t in clippedNode δ n i..clippedNode δ n (i+1), w t) +
      η*(∫ t in d..((1/2-δ)/2), w t) := by
    unfold coarseIntegral
    simp_rw [add_mul]
    rw [sum_add_distrib,← mul_sum,hs]
  have hover := effective_overhang hδ hδhi hd hda
  have hlast := effective_slab_nonneg hδ hδhi
    (node_mem hδhi (n := n) (i := n+1) le_rfl)
  simp only [node_end] at hlast
  have hp := mul_nonneg hh.le hlast
  have hpay := mul_le_mul_of_nonneg_left hmass hη
  change coarseIntegral δ η n ≤ _
  rw [heq]
  change (∑ i ∈ range (n+1), f (coarseNode δ n (i-1)) *
    ∫ t in max d (coarseNode δ n i)..max d (coarseNode δ n (i+1)), w t) -
    (∫ t in d..((1/2-δ)/2), f t*w t) ≤ _ at hlag
  have hi : (∫ t in d..((1/2-δ)/2), f t*w t) =
      ∫ t in d..((1/2-δ)/2), effectiveKernel δ t := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [f,w,effectiveKernel,div_eq_mul_inv]
  rw [hi] at hlag
  dsimp [d,f,clippedNode] at hlag hover hp hpay ⊢
  linarith only [hlag,hover,hp,hpay]

end Wu2008DoubleSieve.SingleUpperHCoarseLimit
