import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1022CanonicalKernel

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1022

set_option autoImplicit false
set_option maxHeartbeats 800000

open Section10CanonicalXi

/-- Conjugating the local integral inequality (10.33) by the canonical phase
turns the canonical-kernel estimate into the strict local growth used at the
least downward crossing. -/
lemma weighted_strict_growth
    {b E c s L : ℝ} {f : ℝ → ℝ}
    (hb : 0 < b) (hden : 0 < s + E)
    (hs : 0 ≤ s - 1)
    (hfcont : ContinuousOn f (Icc (s - 1) s))
    (hlocal : (s + E) * f s ≥ b * ∫ t in s - 1..s, f t)
    (hkernel : 1 < lowerKernel b E c s)
    (hfloor : ∀ t ∈ Icc (s - 1) s, L ≤ lowerWeighted f b c t)
    (hL : 0 < L) :
    L < lowerWeighted f b c s := by
  have hphasecont : ContinuousOn (lowerPhase b c) (Icc (s - 1) s) :=
    (lowerPhase_continuousOn hs).mono (by intro t ht; exact ht.1)
  have hintegrableF : IntervalIntegrable f volume (s - 1) s :=
    by
      rw [← uIcc_of_le (by linarith : s - 1 ≤ s)] at hfcont
      exact hfcont.intervalIntegrable
  have hminor : ∀ t ∈ Icc (s - 1) s,
      L * Real.exp (-lowerPhase b c t) ≤ f t := by
    intro t ht
    have hmul := mul_le_mul_of_nonneg_right (hfloor t ht)
      (Real.exp_pos (-lowerPhase b c t)).le
    simpa [lowerWeighted, mul_assoc, ← Real.exp_add] using hmul
  have hminorCont : ContinuousOn
      (fun t : ℝ => L * Real.exp (-lowerPhase b c t)) (Icc (s - 1) s) :=
    (continuousOn_const.mul
      (Real.continuous_exp.comp_continuousOn hphasecont.neg))
  have hminorIntegrable : IntervalIntegrable
      (fun t : ℝ => L * Real.exp (-lowerPhase b c t)) volume (s - 1) s := by
    rw [← uIcc_of_le (by linarith : s - 1 ≤ s)] at hminorCont
    exact hminorCont.intervalIntegrable
  have hminorInt := intervalIntegral.integral_mono_on (by linarith)
    hminorIntegrable hintegrableF hminor
  have hdiv : b * (∫ t in s - 1..s, f t) / (s + E) ≤ f s := by
    apply (div_le_iff₀ hden).2
    linarith
  have hweighted : lowerKernel b E c s * L ≤ lowerWeighted f b c s := by
    rw [lowerKernel, lowerWeighted]
    have hexpPos : 0 < Real.exp (lowerPhase b c s) := Real.exp_pos _
    have hfactor :
        (∫ t in s - 1..s, Real.exp (lowerPhase b c s - lowerPhase b c t)) =
          Real.exp (lowerPhase b c s) *
            ∫ t in s - 1..s, Real.exp (-lowerPhase b c t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [← Real.exp_add]
      ring_nf
    rw [hfactor]
    calc
      (b / (s + E) *
          (Real.exp (lowerPhase b c s) *
            ∫ t in s - 1..s, Real.exp (-lowerPhase b c t))) * L
          = (b * (∫ t in s - 1..s,
              L * Real.exp (-lowerPhase b c t)) / (s + E)) *
              Real.exp (lowerPhase b c s) := by
                rw [intervalIntegral.integral_const_mul]
                ring
      _ ≤ (b * (∫ t in s - 1..s, f t) / (s + E)) *
              Real.exp (lowerPhase b c s) := by
                exact mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hminorInt hb.le)
                    hden.le) hexpPos.le
      _ ≤ f s * Real.exp (lowerPhase b c s) :=
        mul_le_mul_of_nonneg_right hdiv hexpPos.le
  nlinarith [mul_lt_mul_of_pos_right hkernel hL]

/-- Source-faithful topological half of Suzuki Lemma 10.22.  The canonical
kernel estimate is obtained from `canonicalKernel_growth`; neither the desired
barrier nor first-crossing exclusion is a premise.  One common eventual
threshold is fixed before the least-crossing argument, so every later point has
both the local inequality and the strict kernel estimate. -/
theorem lemma10_22_lower_barrier_eventually_of_kernel
    {b E s₀ : ℝ} {f : ℝ → ℝ}
    (hb : 0 < b) (_hE : 1 ≤ E)
    (hcanonical : CanonicalKernelGrowth b E) (hs₀ : 0 ≤ s₀)
    (hcont : ContinuousOn f (Ici s₀))
    (hpos : ∀ s, s₀ ≤ s → 0 < f s)
    (hlocal : ∀ᶠ s in atTop,
      (s + E) * f s ≥ b * ∫ t in s - 1..s, f t) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ s in atTop,
      Real.exp (-(∫ t in b..s, xi (t / b)) -
        c * Real.log (s + Real.exp 1)) < f s := by
  rcases hcanonical with ⟨c, hc, hk⟩
  have hfuture : ∀ᶠ s in atTop,
      (s + E) * f s ≥ b * ∫ t in s - 1..s, f t ∧
      (0 < s + E ∧ 1 < lowerKernel b E c s) := hlocal.and hk
  rcases (eventually_atTop.1 hfuture) with ⟨S₁, hS₁⟩
  let S : ℝ := max S₁ (max (s₀ + 1) 1)
  have hSfuture : ∀ s, S ≤ s →
      (s + E) * f s ≥ b * ∫ t in s - 1..s, f t ∧
      (0 < s + E ∧ 1 < lowerKernel b E c s) := by
    intro s hs
    exact hS₁ s (le_trans (le_max_left _ _) hs)
  have hSbig : max (s₀ + 1) 1 ≤ S := le_max_right _ _
  have hSm1 : s₀ ≤ S - 1 := by
    linarith [le_trans (le_max_left (s₀ + 1) 1) hSbig]
  let g : ℝ → ℝ := lowerWeighted f b c
  have hgcont : ContinuousOn g (Ici (S - 1)) := by
    exact (lowerWeighted_continuousOn hs₀ hcont).mono
      (by intro t ht; exact hSm1.trans ht)
  obtain ⟨u, hu, humin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : S - 1 ≤ S))
    (hgcont.mono (by intro t ht; exact ht.1))
  let L : ℝ := g u
  have hLpos : 0 < L := by
    dsimp only [L, g, lowerWeighted]
    exact mul_pos (hpos u (hSm1.trans hu.1)) (Real.exp_pos _)
  have hinit : ∀ t ∈ Icc (S - 1) S, L ≤ g t := by
    intro t ht
    exact humin ht
  have hboost : ∀ s, S ≤ s →
      (∀ t ∈ Icc (s - 1) s, L ≤ g t) → L < g s := by
    intro s hs hfloor
    have hsdata := hSfuture s hs
    have hs₀' : s₀ ≤ s - 1 := by linarith
    have hsnonneg : 0 ≤ s - 1 := hs₀.trans hs₀'
    exact weighted_strict_growth hb hsdata.2.1 hsnonneg
      (hcont.mono (by intro t ht; exact hs₀'.trans ht.1)) hsdata.1 hsdata.2.2
      hfloor hLpos
  have htail : ∀ s, S ≤ s → L < g s :=
    least_downward_crossing hgcont hinit hboost
  let d : ℝ := max 0 (-Real.log L / Real.log (S + Real.exp 1))
  refine ⟨c + d, by dsimp [d]; linarith [le_max_left 0 (-Real.log L / Real.log (S + Real.exp 1))], ?_⟩
  filter_upwards [eventually_ge_atTop S] with s hs
  have hlogpos : 0 < Real.log (s + Real.exp 1) := Real.log_pos (by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith [le_trans (le_max_right (s₀ + 1) 1) hSbig])
  have hdnonneg : 0 ≤ d := le_max_left _ _
  have hbar := htail s hs
  dsimp only [g, lowerWeighted, lowerPhase] at hbar
  have hLlog : -d * Real.log (s + Real.exp 1) ≤ Real.log L := by
    have hSlog : 0 < Real.log (S + Real.exp 1) := Real.log_pos (by
      have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith [le_trans (le_max_right (s₀ + 1) 1) hSbig])
    have hlogs : Real.log (S + Real.exp 1) ≤ Real.log (s + Real.exp 1) :=
      Real.strictMonoOn_log.monotoneOn
        (by
          have hSone : 1 ≤ S := le_trans (le_max_right (s₀ + 1) 1) hSbig
          show 0 < S + Real.exp 1
          linarith [Real.exp_pos (1 : ℝ)])
        (by
          have hSone : 1 ≤ S := le_trans (le_max_right (s₀ + 1) 1) hSbig
          show 0 < s + Real.exp 1
          linarith [Real.exp_pos (1 : ℝ)])
        (by linarith)
    dsimp only [d]
    have hd : -Real.log L / Real.log (S + Real.exp 1) ≤ d := le_max_right _ _
    have hd' : -Real.log L ≤ d * Real.log (S + Real.exp 1) :=
      (div_le_iff₀ hSlog).mp hd
    have hmul := mul_le_mul_of_nonneg_left hlogs hdnonneg
    linarith
  have hrewrite :
      Real.exp (-(∫ t in b..s, xi (t / b)) - (c + d) * Real.log (s + Real.exp 1)) ≤
      L * Real.exp (-(∫ t in b..s, xi (t / b)) - c * Real.log (s + Real.exp 1)) := by
    rw [← Real.exp_log hLpos]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hfromWeighted :
      L * Real.exp (-(∫ t in b..s, xi (t / b)) - c * Real.log (s + Real.exp 1)) < f s := by
    have hepos := Real.exp_pos ((∫ t in b..s, xi (t / b)) + c * Real.log (s + Real.exp 1))
    have hmul :
        (L * Real.exp (-(∫ t in b..s, xi (t / b)) -
          c * Real.log (s + Real.exp 1))) *
            Real.exp ((∫ t in b..s, xi (t / b)) +
              c * Real.log (s + Real.exp 1)) <
          f s * Real.exp ((∫ t in b..s, xi (t / b)) +
            c * Real.log (s + Real.exp 1)) := by
      have hcancel :
          (L * Real.exp (-(∫ t in b..s, xi (t / b)) -
            c * Real.log (s + Real.exp 1))) *
              Real.exp ((∫ t in b..s, xi (t / b)) +
                c * Real.log (s + Real.exp 1)) = L := by
        let phase : ℝ := (∫ t in b..s, xi (t / b)) +
          c * Real.log (s + Real.exp 1)
        have hneg : -(∫ t in b..s, xi (t / b)) -
            c * Real.log (s + Real.exp 1) = -phase := by
          dsimp [phase]
          ring
        rw [hneg]
        change (L * Real.exp (-phase)) * Real.exp phase = L
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      rw [hcancel]
      exact hbar
    exact lt_of_mul_lt_mul_right hmul hepos.le
  exact lt_of_le_of_lt hrewrite hfromWeighted



/-- Suzuki Lemma 10.22 specialized to the κ=b=1 application used in Section 13. -/
theorem lemma10_22_lower_barrier_one
    {E s₀ : ℝ} {f : ℝ → ℝ}
    (hE : 1 ≤ E) (hs₀ : 0 ≤ s₀)
    (hcont : ContinuousOn f (Ici s₀))
    (hpos : ∀ s, s₀ ≤ s → 0 < f s)
    (hlocal : ∀ᶠ s in atTop,
      (s + E) * f s ≥ ∫ t in s - 1..s, f t) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ᶠ s in atTop,
      Real.exp (-(∫ t in (1 : ℝ)..s, xi t) -
        c * Real.log (s + Real.exp 1)) < f s := by
  simpa using lemma10_22_lower_barrier_eventually_of_kernel
    (b := (1 : ℝ)) (E := E) (s₀ := s₀) (f := f)
    (by norm_num) hE (canonicalKernelGrowth_one hE) hs₀ hcont hpos (by simpa using hlocal)

end Section10Lemma1022
