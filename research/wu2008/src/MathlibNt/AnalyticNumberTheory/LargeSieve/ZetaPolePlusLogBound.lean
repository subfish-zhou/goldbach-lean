import PrimeNumberTheoremAnd.ZetaBounds

open Complex Topology Filter Set

/-- On a bounded vertical segment to the right of the pole, the Riemann zeta
function is bounded by a constant times the reciprocal of the height. -/
theorem zeta_pole_bound_small_height :
    ∃ Z : ℝ, 0 < Z ∧ ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 → |u| ≤ 3 →
      ‖riemannZeta (1 + x + I * u)‖ ≤ Z / |u| := by
  have hnear : ∀ᶠ s : ℂ in 𝓝[≠] 1, ‖(s - 1) * riemannZeta s‖ < 2 := by
    have hball : Metric.ball (1 : ℂ) 1 ∈ 𝓝 (1 : ℂ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [riemannZeta_residue_one.eventually hball] with s hs
    rw [dist_eq_norm] at hs
    calc
      ‖(s - 1) * riemannZeta s‖
          ≤ ‖(s - 1) * riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
              simpa using norm_add_le ((s - 1) * riemannZeta s - 1) 1
      _ < 2 := by simp only [norm_one]; linarith
  have hnear' : ∀ᶠ s : ℂ in 𝓝 1,
      s ≠ 1 → ‖(s - 1) * riemannZeta s‖ < 2 :=
    (eventually_nhdsWithin_iff).1 hnear
  rcases (eventually_nhds_iff.1 hnear') with ⟨U, hUsub, hUopen, h1U⟩
  rcases Metric.isOpen_iff.mp hUopen 1 h1U with ⟨ε, hεpos, hεU⟩
  let R : Set ℂ := {s | s.re ∈ Icc 1 2 ∧ s.im ∈ Icc (-3) 3}
  have hRcompact : IsCompact R := by
    change IsCompact (Complex.reProdIm (Icc (1 : ℝ) 2) (Icc (-3 : ℝ) 3))
    exact isCompact_Icc.reProdIm isCompact_Icc
  let K : Set ℂ := R ∩ {s | ε ≤ dist s 1}
  have hKclosed : IsClosed K := by
    exact hRcompact.isClosed.inter <|
      isClosed_Ici.preimage (by fun_prop : Continuous fun s : ℂ => dist s 1)
  have hKcompact : IsCompact K := by
    apply hRcompact.of_isClosed_subset hKclosed
    intro s hs
    exact hs.1
  have hKne : ∀ s ∈ K, s ≠ 1 := by
    intro s hs hseq
    have hbad : ε ≤ 0 := by simpa [hseq] using hs.2
    linarith
  have hcont : ContinuousOn riemannZeta K := by
    intro s hs
    exact (differentiableAt_riemannZeta (hKne s hs)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hKcompact hcont
  let C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨max 2 (3 * C'), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x u hx hx1 hu hule
  have huabspos : 0 < |u| := abs_pos.mpr hu
  let s : ℂ := 1 + x + I * u
  have hsne : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [s] at this
    exact hu this
  have hsR : s ∈ R := by
    simp only [R, mem_ofPred_eq, mem_Icc]
    constructor
    · constructor
      · simp [s, hx.le]
      · simp [s]
        linarith
    · simpa [s, abs_le] using hule
  by_cases hsball : dist s 1 < ε
  · have hprod : ‖(s - 1) * riemannZeta s‖ < 2 :=
      hUsub s (hεU hsball) hsne
    have hu_le : |u| ≤ ‖s - 1‖ := by
      have him : (s - 1).im = u := by simp [s]
      rw [← him]
      exact abs_im_le_norm (s - 1)
    apply (le_div_iff₀ huabspos).2
    calc
      ‖riemannZeta s‖ * |u| = |u| * ‖riemannZeta s‖ := mul_comm _ _
      _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ :=
        mul_le_mul_of_nonneg_right hu_le (norm_nonneg _)
      _ = ‖(s - 1) * riemannZeta s‖ := (norm_mul _ _).symm
      _ ≤ 2 := hprod.le
      _ ≤ max 2 (3 * C') := le_max_left _ _
  · have hsK : s ∈ K := ⟨hsR, le_of_not_gt hsball⟩
    have hzC : ‖riemannZeta s‖ ≤ C' :=
      (hC s hsK).trans (le_max_left _ _)
    apply hzC.trans
    apply (le_div_iff₀ huabspos).2
    calc
      C' * |u| ≤ C' * 3 := mul_le_mul_of_nonneg_left hule hC'pos.le
      _ = 3 * C' := mul_comm _ _
      _ ≤ max 2 (3 * C') := le_max_right _ _

/-- Uniformly for `0 < x ≤ 1` away from the real pole, zeta has at most
logarithmic growth in the height, with the pole recorded by `1 / |u|`. -/
theorem zeta_pole_plus_log_bound :
    ∃ Z : ℝ, 0 < Z ∧ ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|) := by
  obtain ⟨z, hz, hsmall⟩ := zeta_pole_bound_small_height
  obtain ⟨A, hA, C, hC, hlarge⟩ := ZetaUpperBnd
  let Z : ℝ := max z C
  have hZpos : 0 < Z := hz.trans_le (le_max_left _ _)
  refine ⟨Z, hZpos, ?_⟩
  intro x u hx hx1 hu
  have huabspos : 0 < |u| := abs_pos.mpr hu
  have hlognonneg : 0 ≤ Real.log (|u| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg u])
  by_cases hsmallHeight : |u| ≤ 3
  · calc
      ‖riemannZeta (1 + x + I * u)‖ ≤ z / |u| :=
        hsmall x u hx hx1 hu hsmallHeight
      _ ≤ Z / |u| := div_le_div_of_nonneg_right (le_max_left _ _) huabspos.le
      _ ≤ Z * (1 + Real.log (|u| + 2) + 1 / |u|) := by
        rw [div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_left (by linarith) hZpos.le
  · have hu3 : 3 < |u| := lt_of_not_ge hsmallHeight
    have hlogpos : 0 < Real.log |u| := Real.log_pos (by linarith)
    have hlower : 1 - A / Real.log |u| ≤ 1 + x := by
      have : 0 < A / Real.log |u| := div_pos hA.1 hlogpos
      linarith
    have hupper : 1 + x ≤ 2 := by linarith
    have hb := hlarge (1 + x) u hu3 ⟨hlower, hupper⟩
    have hb' : ‖riemannZeta (1 + x + I * u)‖ ≤ C * Real.log |u| := by
      simpa [ofReal_add, mul_comm, add_comm] using hb
    have hlogmono : Real.log |u| ≤ Real.log (|u| + 2) := by
      apply Real.strictMonoOn_log.monotoneOn huabspos
      · show 0 < |u| + 2
        linarith
      · linarith
    calc
      ‖riemannZeta (1 + x + I * u)‖ ≤ C * Real.log |u| := hb'
      _ ≤ Z * Real.log |u| :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlogpos.le
      _ ≤ Z * Real.log (|u| + 2) :=
        mul_le_mul_of_nonneg_left hlogmono hZpos.le
      _ ≤ Z * (1 + Real.log (|u| + 2) + 1 / |u|) := by
        apply mul_le_mul_of_nonneg_left _ hZpos.le
        have hinv : 0 < 1 / |u| := one_div_pos.mpr huabspos
        linarith