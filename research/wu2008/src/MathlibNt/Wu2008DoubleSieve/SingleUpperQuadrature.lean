import MathlibNt.Wu2008DoubleSieve.SingleUpperClassicalLimit
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureWeighted

namespace Wu2008DoubleSieve.SingleUpperQuadrature
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology

/-- A compact slope bound follows from the actual delay integral identity. -/
theorem coefficient_regular : ∃ M L : ℝ, 0 < M ∧ 0 < L ∧
    (∀ s ∈ Icc (2 : ℝ) 10, |wuUpperCoefficient s| ≤ M) ∧
    (∀ x ∈ Icc (2 : ℝ) 10, ∀ y ∈ Icc (2 : ℝ) 10,
      |wuUpperCoefficient x-wuUpperCoefficient y| ≤ L*|x-y|) := by
  have hc : ContinuousOn wuUpperCoefficient (Icc (2 : ℝ) 10) :=
    continuousOn_wuUpperCoefficient.mono (fun _ h => lt_of_lt_of_le (by norm_num) h.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hd : ContinuousOn (fun t => wuLowerCoefficient t/t) (Icc (1 : ℝ) 9) :=
    (continuousOn_wuLowerCoefficient.mono (fun _ h => lt_of_lt_of_le (by norm_num) h.1)).div
      continuousOn_id (fun t ht => ne_of_gt (by linarith [ht.1]))
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  refine ⟨|M|+1, |L|+1, by positivity, by positivity, ?_, ?_⟩
  · intro s hs
    have hh : |wuUpperCoefficient s| ≤ M := by simpa only [Real.norm_eq_abs] using hM s hs
    exact hh.trans (by linarith [le_abs_self M])
  · have hordered (x y : ℝ) (hx : x ∈ Icc (2 : ℝ) 10)
        (hy : y ∈ Icc (2 : ℝ) 10) (hxy : x ≤ y) :
        |wuUpperCoefficient y-wuUpperCoefficient x| ≤ (|L|+1)*|y-x| := by
      rw [wuUpperCoefficient_sub_eq_integral hx.1 hxy, ← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := x-1) (b := y-1) (C := |L|+1) (f := fun t => wuLowerCoefficient t/t)
        (fun t ht => (hL t (by
          rw [uIoc_of_le (by linarith : x-1 ≤ y-1)] at ht
          exact ⟨by linarith [ht.1, hx.1], by linarith [ht.2, hy.2]⟩)).trans
          (by linarith [le_abs_self L]))
      simpa only [sub_sub_sub_cancel_right] using h
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · simpa only [abs_sub_comm] using hordered x y hx hy hxy
    · exact hordered y x hy hx hyx

noncomputable def weight (δ t : ℝ) : ℝ :=
  wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha)/((1/2-δ)-t)

/-- This slab includes a fixed positive margin below alpha. It is not the
incorrect fixed one-tenth slab in the original N-coordinate. -/
theorem argument_mem {δ t : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (1/15 : ℝ) (1/3)) :
    ((1/2-δ)-t)/truncatedSixthLowerAlpha ∈ Icc (2 : ℝ) 10 := by
  constructor
  · apply (le_div_iff₀ (by norm_num [truncatedSixthLowerAlpha])).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith [ht.2]
  · apply (div_le_iff₀ (by norm_num [truncatedSixthLowerAlpha])).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith [ht.1]

/-- Uniform bounded Lipschitz constants for the genuine arithmetic weight.
Only A is used; no regularity premise on H is introduced. -/
theorem weight_regular : ∃ M K : ℝ, 0 < M ∧ 0 < K ∧
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1/100 →
    ContinuousOn (weight δ) (Icc (1/15 : ℝ) (1/3)) ∧
    (∀ t ∈ Icc (1/15 : ℝ) (1/3), |weight δ t| ≤ M) ∧
    (∀ x ∈ Icc (1/15 : ℝ) (1/3), ∀ y ∈ Icc (1/15 : ℝ) (1/3),
      |weight δ x-weight δ y| ≤ K*|x-y|) := by
  obtain ⟨M,L,hM,hL,hMb,hLb⟩ := coefficient_regular
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  refine ⟨10*M, 10*L/truncatedSixthLowerAlpha+100*M, by positivity,
    by positivity, ?_⟩
  intro δ hδ hδhi
  have hd (t : ℝ) (ht : t ∈ Icc (1/15 : ℝ) (1/3)) :
      (1/10 : ℝ) ≤ (1/2-δ)-t := by linarith [ht.2]
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hc : ContinuousOn (weight δ) (Icc (1/15 : ℝ) (1/3)) := by
    apply ContinuousOn.div _ (by fun_prop)
      (fun t ht => ne_of_gt (lt_of_lt_of_le (by norm_num) (hd t ht)))
    exact continuousOn_wuUpperCoefficient.comp (by fun_prop)
      (fun t ht => lt_of_lt_of_le (by norm_num) (argument_mem hδ hδhi ht).1)
  refine ⟨hc, ?_, ?_⟩
  · intro t ht
    unfold weight
    rw [abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) (hd t ht))]
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hd t ht))).mpr
    have hb := hMb _ (argument_mem hδ hδhi ht)
    have hm := mul_le_mul_of_nonneg_left (hd t ht) (show 0 ≤ 10*M by positivity)
    nlinarith
  · intro x hx y hy
    let dx := (1/2-δ)-x
    let dy := (1/2-δ)-y
    have hx0 : 0 < dx := lt_of_lt_of_le (by norm_num) (hd x hx)
    have hy0 : 0 < dy := lt_of_lt_of_le (by norm_num) (hd y hy)
    have hdprod : (1/100 : ℝ) ≤ dx*dy := by
      have hh := mul_le_mul (hd x hx) (hd y hy) (by norm_num) hx0.le
      norm_num at hh
      exact hh
    have hdiff := hLb _ (argument_mem hδ hδhi hx) _ (argument_mem hδ hδhi hy)
    have he : dx/truncatedSixthLowerAlpha-dy/truncatedSixthLowerAlpha =
        -(x-y)/truncatedSixthLowerAlpha := by dsimp [dx,dy]; ring
    rw [show ((1/2-δ)-x)/truncatedSixthLowerAlpha-
        ((1/2-δ)-y)/truncatedSixthLowerAlpha = -(x-y)/truncatedSixthLowerAlpha from he,
      abs_div, abs_neg, abs_of_pos ha] at hdiff
    have heq : weight δ x-weight δ y =
        (wuUpperCoefficient (dx/truncatedSixthLowerAlpha)-wuUpperCoefficient (dy/truncatedSixthLowerAlpha))/dx +
        wuUpperCoefficient (dy/truncatedSixthLowerAlpha)*(dy-dx)/(dx*dy) := by
      change wuUpperCoefficient (dx/truncatedSixthLowerAlpha)/dx -
        wuUpperCoefficient (dy/truncatedSixthLowerAlpha)/dy = _
      field_simp [hx0.ne',hy0.ne']
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    have hfirst : |(wuUpperCoefficient (dx/truncatedSixthLowerAlpha)-
        wuUpperCoefficient (dy/truncatedSixthLowerAlpha))/dx| ≤
        (10*L/truncatedSixthLowerAlpha)*|x-y| := by
      rw [abs_div, abs_of_pos hx0]
      apply (div_le_iff₀ hx0).mpr
      have hm := mul_le_mul_of_nonneg_left (hd x hx)
        (show 0 ≤ (10*L/truncatedSixthLowerAlpha)*|x-y| by positivity)
      have hh : L*(|x-y|/truncatedSixthLowerAlpha) ≤
          (10*L/truncatedSixthLowerAlpha)*|x-y| * dx := by
        calc
          _ = ((10*L/truncatedSixthLowerAlpha)*|x-y|) * (1/10) := by ring
          _ ≤ _ := hm
      exact hdiff.trans hh
    have hsecond : |wuUpperCoefficient (dy/truncatedSixthLowerAlpha)*(dy-dx)/(dx*dy)| ≤
        100*M*|x-y| := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hx0 hy0)]
      have hey : dy-dx = x-y := by dsimp [dx,dy]; ring
      rw [hey]
      apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
      have hb := mul_le_mul_of_nonneg_right (hMb _ (argument_mem hδ hδhi hy)) (abs_nonneg (x-y))
      have hm := mul_le_mul_of_nonneg_left hdprod (show 0 ≤ 100*M*|x-y| by positivity)
      nlinarith
    linarith

/-- Exact exponent rescaling places the whole original slab inside the
accepted quadrature slab without imposing alpha >= one tenth. -/
theorem rescaled_integral (f : ℝ → ℝ) (a b : ℝ) :
    (∫ t in (3/2*a)..(3/2*b), f ((2/3)*t)/t) =
      ∫ t in a..b, f t/t := by
  have he (t : ℝ) : f ((2/3)*t)/t = (2/3)*(f ((2/3)*t)/((2/3)*t)) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t => f t/t) (by norm_num : (2/3 : ℝ) ≠ 0)]
  norm_num only [show (2/3 : ℝ)*(3/2*a) = a by ring,
    show (2/3 : ℝ)*(3/2*b) = b by ring, smul_eq_mul]
  ring

/-- Actual unmasked prime quadrature. All constants and the fixed macrogrid
precede N, delta and both endpoints. No error is summed over the microgrid. -/
theorem weighted_prime_quadrature {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ δ a b : ℝ, 0 ≤ δ → δ ≤ 1/100 → 1/15 ≤ a → a ≤ b → b ≤ 1/3 →
      |(∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b),
        weight δ (log p/log N)/(p : ℝ)) - ∫ t in a..b, weight δ t/t| < ε := by
  obtain ⟨M,K,hM,hK,hreg⟩ := weight_regular
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(2/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (ht.eventually (primeOrdered_weighted_uniform M K ε hM.le hK.le hε))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN δ a b hδ hδhi ha hab hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hmap (t : ℝ) (ht : t ∈ Icc (1/10 : ℝ) (1/2)) :
      (2/3)*t ∈ Icc (1/15 : ℝ) (1/3) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc := (hreg δ hδ hδhi).1.comp (by fun_prop :
    ContinuousOn (fun t : ℝ => (2/3)*t) (Icc (1/10 : ℝ) (1/2))) hmap
  have hbound := fun t ht => (hreg δ hδ hδhi).2.1 _ (hmap t ht)
  have hlip : ∀ x ∈ Icc (1/10 : ℝ) (1/2), ∀ y ∈ Icc (1/10 : ℝ) (1/2),
      |weight δ ((2/3)*x)-weight δ ((2/3)*y)| ≤ K*|x-y| := by
    intro x hx y hy
    have h := (hreg δ hδ hδhi).2.2 _ (hmap x hx) _ (hmap y hy)
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2/3)] at h
    have hn := mul_nonneg hK.le (abs_nonneg (x-y))
    nlinarith
  have h := hT N ((le_max_right _ _).trans hN) (fun t => weight δ ((2/3)*t))
    (3/2*a) (3/2*b) hc hbound hlip (by linarith) (by linarith) (by linarith)
  rw [rescaled_integral] at h
  have he (t : ℝ) : ((N : ℝ)^(2/3 : ℝ))^(3/2*t) = (N : ℝ)^t := by
    rw [← rpow_mul hN0.le, show (2/3 : ℝ)*(3/2*t) = t by ring]
  have htlog (p : ℕ) : (2/3)*(log (p : ℝ)/log ((N : ℝ)^(2/3 : ℝ))) = log p/log N := by
    rw [log_rpow hN0]
    field_simp
  simpa only [primeOrderedClosedSum, he, htlog] using h

end Wu2008DoubleSieve.SingleUpperQuadrature
