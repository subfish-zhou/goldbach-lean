import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053KernelExpansion
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiConstruction

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# The plus first-crossing half of Suzuki Lemma 10.28

This file treats the plus branch directly.  In particular, it does not obtain it
by changing signs in the minus first-crossing theorem: the first-crossing set,
window order, and pairing inequality all have the opposite orientation.
-/

namespace Section10Lemma1028PlusAssembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053
open Section10Equation1053NonCircular
open Section10Equation1053KernelExpansion
open Section10CanonicalXi

/-- The plus phase `φ₊(s)=∫₁ˢ ξ(t)dt+cs`. -/
noncomputable def phiPlus (ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  xiPhase ξ s + c * s

/-- The plus exponent `ψ₊(s)=φ₊(s)-log r(s+1)`. -/
noncomputable def psiPlus (r ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  phiPlus ξ c s - Real.log (r (s + 1))

/-- Suzuki's weighted plus envelope. -/
noncomputable def envelopePlus (R ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  R s * Real.exp (phiPlus ξ c s)

/-- Its logarithm, used to state the first-crossing history. -/
noncomputable def logEnvelopePlus (R ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  Real.log (R s) + xiPhase ξ s + c * s

@[simp] lemma exp_neg_psiPlus
    {r ξ : ℝ → ℝ} {c t : ℝ} (hr : 0 < r (t + 1)) :
    Real.exp (-psiPlus r ξ c t) =
      r (t + 1) * Real.exp (-phiPlus ξ c t) := by
  rw [psiPlus, neg_sub, Real.exp_sub, Real.exp_log hr]
  rw [Real.exp_neg]
  rfl

/-- Direct plus version of (10.44). -/
theorem logEnvelopePlus_hasDerivAt
    {R ξ : ℝ → ℝ} (hξ : Proposition1020Xi ξ) {c s : ℝ}
    (hs : 0 < s) (hR : 0 < R s)
    (hDDE : HasDerivAt R (-(2 * R s + R (s - 1)) / s) s) :
    HasDerivAt (logEnvelopePlus R ξ c)
      (-R (s - 1) / (s * R s) + ξ s + c - 2 / s) s := by
  have hlog := hDDE.log (ne_of_gt hR)
  have hphase := xiPhase_hasDerivAt hξ s
  have hlin : HasDerivAt (fun u : ℝ => c * u) c s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul c
  have hsum := (hlog.add hphase).add hlin
  have hcoeff :
      (-(2 * R s + R (s - 1)) / s) / R s + ξ s + c =
        -R (s - 1) / (s * R s) + ξ s + c - 2 / s := by
    field_simp [ne_of_gt hs, ne_of_gt hR]
    <;> ring
  have hfun :
      ((fun y : ℝ => Real.log (R y)) + xiPhase ξ + fun u : ℝ => c * u) =
        logEnvelopePlus R ξ c := by
    funext u
    rfl
  rw [hfun] at hsum
  exact hsum.congr_deriv hcoeff

/-- A genuine plus first crossing: the logarithmic slope starts positive and
`s` is the first point after `s₀` at which it is nonpositive. -/
structure PlusFirstCrossing
    (R ξ : ℝ → ℝ) (c β s₀ : ℝ) where
  s : ℝ
  slope : ℝ → ℝ
  beta_lt_s₀ : β < s₀
  s₀_lt_s : s₀ < s
  beta_add_one_le_s : β + 1 ≤ s
  slope_continuousOn : ContinuousOn slope (Ioc β s)
  logEnvelope_continuousOn :
    ContinuousOn (logEnvelopePlus R ξ c) (Icc β s)
  hasDeriv : ∀ u ∈ Ioc β s,
    HasDerivAt (logEnvelopePlus R ξ c) (slope u) u
  initial_pos : ∀ u ∈ Icc β s₀, 0 < slope u
  before_crossing_pos : ∀ u, s₀ < u → u < s → 0 < slope u
  crossing_nonpos : slope s ≤ 0

lemma PlusFirstCrossing.slope_pos_before
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : PlusFirstCrossing R ξ c β s₀)
    {u : ℝ} (hβu : β ≤ u) (hus : u < w.s) :
    0 < w.slope u := by
  by_cases hu : u ≤ s₀
  · exact w.initial_pos u ⟨hβu, hu⟩
  · exact w.before_crossing_pos u (lt_of_not_ge hu) hus

/-- The witness really records the least point in the closed nonpositive set. -/
lemma PlusFirstCrossing.isLeast_nonpositive
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : PlusFirstCrossing R ξ c β s₀) :
    IsLeast {u : ℝ | s₀ ≤ u ∧ w.slope u ≤ 0} w.s := by
  constructor
  · exact ⟨w.s₀_lt_s.le, w.crossing_nonpos⟩
  · intro u hu
    by_contra hsu
    have hus : u < w.s := lt_of_not_ge hsu
    have hβu : β ≤ u := le_trans w.beta_lt_s₀.le hu.1
    exact (not_lt_of_ge hu.2) (w.slope_pos_before hβu hus)

/-- Continuity turns the weak sign at the first point into stationarity. -/
lemma PlusFirstCrossing.slope_at_crossing_eq_zero
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : PlusFirstCrossing R ξ c β s₀) :
    w.slope w.s = 0 := by
  have hβs : β < w.s := w.beta_lt_s₀.trans w.s₀_lt_s
  have hsub : 𝓝[<] w.s ≤ 𝓝[Ioc β w.s] w.s := by
    rw [Filter.le_def]
    intro U hU
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU ⊢
    obtain ⟨V, hV, hVU⟩ := hU
    refine ⟨V ∩ Ioi β, inter_mem hV (Ioi_mem_nhds hβs), ?_⟩
    intro u hu
    exact hVU ⟨hu.1.1, ⟨hu.1.2, hu.2.le⟩⟩
  have hsI : w.s ∈ Ioc β w.s := ⟨hβs, le_rfl⟩
  have hlim : Tendsto w.slope (𝓝[<] w.s) (𝓝 (w.slope w.s)) :=
    (w.slope_continuousOn w.s hsI).mono_left hsub
  have hevent : ∀ᶠ u in 𝓝[<] w.s, 0 ≤ w.slope u := by
    filter_upwards [eventually_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hβs)] with u hus hβu
    exact (w.slope_pos_before hβu.le hus).le
  exact le_antisymm w.crossing_nonpos (ge_of_tendsto hlim hevent)

lemma PlusFirstCrossing.stationary
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : PlusFirstCrossing R ξ c β s₀) :
    HasDerivAt (logEnvelopePlus R ξ c) 0 w.s := by
  have hsI : w.s ∈ Ioc β w.s :=
    ⟨w.beta_lt_s₀.trans w.s₀_lt_s, le_rfl⟩
  simpa [w.slope_at_crossing_eq_zero] using w.hasDeriv w.s hsI

/-- At the plus crossing, (10.44) is exactly (10.45) with the plus sign. -/
lemma PlusFirstCrossing.stationary_equation
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hξ : Proposition1020Xi ξ)
    (w : PlusFirstCrossing R ξ c β s₀) :
    ξ w.s + c - 2 / w.s = R (w.s - 1) / (w.s * R w.s) := by
  have hβs : β < w.s := w.beta_lt_s₀.trans w.s₀_lt_s
  have hs0 : 0 < w.s := by linarith [h.beta_ge_one]
  have hRs : 0 < R w.s := h.positive w.s (by
    linarith [w.beta_add_one_le_s])
  have hd := logEnvelopePlus_hasDerivAt hξ (c := c) hs0 hRs
    (h.original_dde w.s hβs)
  have hz := w.stationary
  have heq := hz.unique hd
  have hneg :
      -R (w.s - 1) / (w.s * R w.s) =
        -(R (w.s - 1) / (w.s * R w.s)) := by ring
  rw [hneg] at heq
  linarith

/-- Before the first nonpositive crossing, `log W₊` is monotone. -/
lemma PlusFirstCrossing.log_monotoneOn
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : PlusFirstCrossing R ξ c β s₀) :
    MonotoneOn (logEnvelopePlus R ξ c) (Icc β w.s) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc β w.s)
    w.logEnvelope_continuousOn
  · intro u hu
    rw [interior_Icc] at hu
    exact (w.hasDeriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    exact (w.slope_pos_before hu.1.le hu.2).le

lemma envelopePlus_eq_exp_logEnvelopePlus_of_pos
    {R ξ : ℝ → ℝ} {c t : ℝ} (hRt : 0 < R t) :
    envelopePlus R ξ c t = Real.exp (logEnvelopePlus R ξ c t) := by
  rw [logEnvelopePlus, envelopePlus, phiPlus]
  calc
    R t * Real.exp (xiPhase ξ t + c * t) =
        Real.exp (Real.log (R t)) * Real.exp (xiPhase ξ t + c * t) := by
          rw [Real.exp_log hRt]
    _ = Real.exp (Real.log (R t) + (xiPhase ξ t + c * t)) := by
          rw [← Real.exp_add]
    _ = Real.exp (Real.log (R t) + xiPhase ξ t + c * t) := by
          congr 1
          ring

lemma PlusFirstCrossing.envelope_monotoneOn
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (w : PlusFirstCrossing R ξ c β s₀) :
    MonotoneOn (envelopePlus R ξ c) (Icc β w.s) := by
  intro x hx y hy hxy
  have hRx : 0 < R x := h.positive x (by linarith [hx.1])
  have hRy : 0 < R y := h.positive y (by linarith [hy.1])
  rw [envelopePlus_eq_exp_logEnvelopePlus_of_pos hRx,
    envelopePlus_eq_exp_logEnvelopePlus_of_pos hRy]
  exact Real.exp_le_exp.mpr (w.log_monotoneOn hx hy hxy)

/-- Correct plus window order: `W₊(s) ≥ W₊(t) ≥ W₊(s-1)`. -/
theorem PlusFirstCrossing.window_order
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (w : PlusFirstCrossing R ξ c β s₀)
    {t : ℝ} (ht : t ∈ Icc (w.s - 1) w.s) :
    envelopePlus R ξ c (w.s - 1) ≤ envelopePlus R ξ c t ∧
      envelopePlus R ξ c t ≤ envelopePlus R ξ c w.s := by
  have hleftI : w.s - 1 ∈ Icc β w.s := by
    constructor <;> linarith [w.beta_add_one_le_s]
  have htI : t ∈ Icc β w.s :=
    ⟨by linarith [w.beta_add_one_le_s, ht.1], ht.2⟩
  have hsI : w.s ∈ Icc β w.s :=
    ⟨by linarith [w.beta_add_one_le_s], le_rfl⟩
  exact ⟨w.envelope_monotoneOn h hleftI htI ht.1,
    w.envelope_monotoneOn h htI hsI ht.2⟩

/-- Pairing-zero rewritten directly in plus variables. -/
theorem plus_pairing_weighted_identity
    {R ξ : ℝ → ℝ} {β c s : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (hβs : β < s) (hs2 : 2 ≤ s) :
    s * explicitKappaOneAdjointPlus s * R s =
      ∫ t in s - 1..s,
        envelopePlus R ξ c t *
          Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t) := by
  have hp := h.pairing_zero s hβs
  rw [hadj] at hp
  rw [hp]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (s - 1) s := by
    simpa [uIcc_of_le (by linarith : s - 1 ≤ s)] using ht
  have hr : 0 < explicitKappaOneAdjointPlus (t + 1) :=
    explicitKappaOneAdjointPlus_pos (by linarith [ht'.1])
  change explicitKappaOneAdjointPlus (t + 1) * R t =
    envelopePlus R ξ c t *
      Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t)
  rw [exp_neg_psiPlus hr]
  dsimp [envelopePlus]
  have hexp : Real.exp (phiPlus ξ c t) * Real.exp (-phiPlus ξ c t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    explicitKappaOneAdjointPlus (t + 1) * R t =
        explicitKappaOneAdjointPlus (t + 1) * R t *
          (Real.exp (phiPlus ξ c t) * Real.exp (-phiPlus ξ c t)) := by
            rw [hexp, mul_one]
    _ = R t * Real.exp (phiPlus ξ c t) *
          (explicitKappaOneAdjointPlus (t + 1) *
            Real.exp (-phiPlus ξ c t)) := by ring

/-- Equation (10.54): increasing plus history gives a lower pairing bound. -/
theorem plus_pairing_ge_leftEndpoint_kernel
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (w : PlusFirstCrossing R ξ c β s₀)
    (hs2 : 2 ≤ w.s)
    (hprodInt : IntervalIntegrable
      (fun t => envelopePlus R ξ c t *
        Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t))
      volume (w.s - 1) w.s)
    (hkernelInt : IntervalIntegrable
      (fun t => Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t))
      volume (w.s - 1) w.s) :
    envelopePlus R ξ c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t)) ≤
      w.s * explicitKappaOneAdjointPlus w.s * R w.s := by
  have hβs : β < w.s := w.beta_lt_s₀.trans w.s₀_lt_s
  rw [plus_pairing_weighted_identity h hadj hβs hs2]
  calc
    envelopePlus R ξ c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t)) =
      ∫ t in w.s - 1..w.s,
        envelopePlus R ξ c (w.s - 1) *
          Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t) := by
            rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ t in w.s - 1..w.s,
        envelopePlus R ξ c t *
          Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t) := by
            apply intervalIntegral.integral_mono_on (by linarith)
            · exact hkernelInt.const_mul _
            · exact hprodInt
            · intro t ht
              exact mul_le_mul_of_nonneg_right
                ((w.window_order h ht).1) (Real.exp_pos _).le

/-- The scalar expression on the right of source (10.55). -/
noncomputable def plusPairingScalarRatio
    (ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  (ξ s + c - 2 / s) *
    (∫ t in s - 1..s,
      Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c t)) /
    Real.exp (-psiPlus explicitKappaOneAdjointPlus ξ c (s - 1))

/-- The strict scalar conclusion of (10.55), separated from the topological and
pairing argument rather than hidden in a final exclusion field. -/
def PlusPairingScalarInequality (ξ : ℝ → ℝ) (c s : ℝ) : Prop :=
  1 < plusPairingScalarRatio ξ c s

/-- Equations (10.54)--(10.55), lower half: pairing and stationarity force the
plus scalar ratio to be at most one. -/
theorem plusFirstCrossing_scalarRatio_le_one
    {R : ℝ → ℝ} {β c s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (w : PlusFirstCrossing R xi c β s₀) :
    plusPairingScalarRatio xi c w.s ≤ 1 := by
  have hs2 : 2 ≤ w.s := by linarith [h.beta_ge_one, w.beta_add_one_le_s]
  have hs0 : 0 < w.s := by linarith
  have hRs : 0 < R w.s := h.positive w.s (by
    linarith [w.beta_add_one_le_s])
  have hadjs : 0 < explicitKappaOneAdjointPlus w.s :=
    explicitKappaOneAdjointPlus_pos hs2
  have hkernelCont : ContinuousOn
      (fun t => Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))
      (Icc (w.s - 1) w.s) := by
    intro t ht
    have hadjpos : 0 < explicitKappaOneAdjointPlus (t + 1) :=
      explicitKappaOneAdjointPlus_pos (by linarith [ht.1])
    have hadjcont : ContinuousAt
        (fun u : ℝ => explicitKappaOneAdjointPlus (u + 1)) t := by
      dsimp [explicitKappaOneAdjointPlus]
      fun_prop
    have hphase : ContinuousAt (phiPlus xi c) t := by
      exact ((xiPhase_hasDerivAt canonicalXi_proposition1020 t).add
        (by simpa only [id_eq, mul_one] using
          (hasDerivAt_id t).const_mul c)).continuousAt
    have hpsi : ContinuousAt (psiPlus explicitKappaOneAdjointPlus xi c) t :=
      hphase.sub (hadjcont.log (ne_of_gt hadjpos))
    exact (Real.continuous_exp.continuousAt.comp hpsi.neg).continuousWithinAt
  have hkernelInt : IntervalIntegrable
      (fun t => Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))
      volume (w.s - 1) w.s :=
    hkernelCont.intervalIntegrable_of_Icc (by linarith)
  have hprodCont : ContinuousOn
      (fun t => envelopePlus R xi c t *
        Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))
      (Icc (w.s - 1) w.s) := by
    intro t ht
    have hRt : 0 < R t := h.positive t (by
      linarith [w.beta_add_one_le_s, ht.1])
    have hRc : ContinuousAt R t :=
      h.continuous.continuousAt
        (Ioi_mem_nhds (by linarith [w.beta_add_one_le_s, ht.1]))
    have hphase : ContinuousAt (phiPlus xi c) t := by
      exact ((xiPhase_hasDerivAt canonicalXi_proposition1020 t).add
        (by simpa only [id_eq, mul_one] using
          (hasDerivAt_id t).const_mul c)).continuousAt
    have hadjpos : 0 < explicitKappaOneAdjointPlus (t + 1) :=
      explicitKappaOneAdjointPlus_pos (by linarith [ht.1])
    have hadjcont : ContinuousAt
        (fun u : ℝ => explicitKappaOneAdjointPlus (u + 1)) t := by
      dsimp [explicitKappaOneAdjointPlus]
      fun_prop
    have hpsi : ContinuousAt (psiPlus explicitKappaOneAdjointPlus xi c) t :=
      hphase.sub (hadjcont.log (ne_of_gt hadjpos))
    exact ((hRc.mul (Real.continuous_exp.continuousAt.comp hphase)).mul
      (Real.continuous_exp.continuousAt.comp hpsi.neg)).continuousWithinAt
  have hprodInt : IntervalIntegrable
      (fun t => envelopePlus R xi c t *
        Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))
      volume (w.s - 1) w.s :=
    hprodCont.intervalIntegrable_of_Icc (by linarith)
  have hpair := plus_pairing_ge_leftEndpoint_kernel h hadj w hs2 hprodInt hkernelInt
  have hAeq := w.stationary_equation h canonicalXi_proposition1020
  have hdenPos : 0 < w.s * explicitKappaOneAdjointPlus w.s * R w.s :=
    mul_pos (mul_pos hs0 hadjs) hRs
  have hratio : plusPairingScalarRatio xi c w.s =
      (envelopePlus R xi c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))) /
        (w.s * explicitKappaOneAdjointPlus w.s * R w.s) := by
    unfold plusPairingScalarRatio
    have hadjs' : 0 < explicitKappaOneAdjointPlus (w.s - 1 + 1) := by
      simpa only [sub_add_cancel] using hadjs
    rw [hAeq, exp_neg_psiPlus hadjs']
    simp only [sub_add_cancel]
    dsimp [envelopePlus]
    field_simp [ne_of_gt hs0, ne_of_gt hRs, ne_of_gt hadjs,
      Real.exp_ne_zero]
    have hcancel :
        Real.exp (-phiPlus xi c (w.s - 1)) *
          Real.exp (phiPlus xi c (w.s - 1)) = 1 := by
      rw [← Real.exp_add]
      simp
    let I : ℝ := R (w.s - 1) * (∫ t in w.s - 1..w.s,
      Real.exp (-psiPlus explicitKappaOneAdjointPlus xi c t))
    change I = I * Real.exp (-phiPlus xi c (w.s - 1)) *
      Real.exp (phiPlus xi c (w.s - 1))
    calc
      I = I * 1 := by ring
      _ = I * (Real.exp (-phiPlus xi c (w.s - 1)) *
            Real.exp (phiPlus xi c (w.s - 1))) := by rw [hcancel]
      _ = _ := by ring
  rw [hratio]
  exact (div_le_one hdenPos).2 hpair

/-- Source-facing producer of a genuine plus first crossing.  It is a theorem
premise about the least crossing, not an arbitrary-stationary exclusion. -/
def ProducesPlusFirstCrossing
    (R : ℝ → ℝ) (β c S : ℝ) : Prop :=
  ∀ v, S ≤ v → normalizedMinusBase R xi v + c ≤ 0 →
    ∃ w : PlusFirstCrossing R xi c β S, S ≤ w.s

/-- Continuity of the normalized slope on the full legal half-line, including
`β`; only differentiability uses the open left endpoint. -/
lemma normalizedMinusBase_continuousAt
    {R : ℝ → ℝ} {β s : ℝ} (h : FirstCrossingDDEApparatus R β)
    (hβs : β < s) : ContinuousAt (normalizedMinusBase R xi) s := by
  have hsR : β - 1 < s := by linarith
  have hsmR : β - 1 < s - 1 := by linarith
  have hs0 : s ≠ 0 := by linarith [h.beta_ge_one]
  have hRs : 0 < R s := h.positive s hsR
  have hRc : ContinuousAt R s :=
    h.continuous.continuousAt (Ioi_mem_nhds hsR)
  have hRmc : ContinuousAt (fun u : ℝ => R (u - 1)) s :=
    (h.continuous.continuousAt (Ioi_mem_nhds hsmR)).comp_of_eq
      (continuousAt_id.sub continuousAt_const) (by simp)
  exact (((hRmc.neg.div (continuousAt_id.mul hRc)
    (mul_ne_zero hs0 (ne_of_gt hRs))).add xi_continuous.continuousAt).sub
      (continuousAt_const.div continuousAt_id hs0))

/-- Compactness constructs the least plus crossing.  No derivative at the
apparatus endpoint `β` is requested. -/
theorem plusFirstCrossing_of_reaches
    {R : ℝ → ℝ} {β c S v : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hβS : β < S) (hβoneS : β + 1 ≤ S)
    (hinitial : ∀ u ∈ Icc β S, 0 < normalizedMinusBase R xi u + c)
    (hSv : S ≤ v) (hv : normalizedMinusBase R xi v + c ≤ 0) :
    ∃ w : PlusFirstCrossing R xi c β S, S ≤ w.s := by
  let f : ℝ → ℝ := fun u => normalizedMinusBase R xi u + c
  let K : Set ℝ := Icc S v ∩ f ⁻¹' Iic 0
  have hfcont : ContinuousOn f (Icc S v) := by
    intro u hu
    exact ((normalizedMinusBase_continuousAt h (hβS.trans_le hu.1)).add
      continuousAt_const).continuousWithinAt
  have hKclosed : IsClosed K :=
    hfcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hKcompact : IsCompact K :=
    isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
  have hvK : v ∈ K := ⟨⟨hSv, le_rfl⟩, hv⟩
  obtain ⟨s, hsK, hsleast⟩ := hKcompact.exists_isLeast ⟨v, hvK⟩
  have hSs : S ≤ s := hsK.1.1
  have hsv : s ≤ v := hsK.1.2
  have hcross : f s ≤ 0 := hsK.2
  have hSlt : S < s := by
    apply lt_of_le_of_ne hSs
    intro hEq
    have hfS : 0 < f S := hinitial S ⟨hβS.le, le_rfl⟩
    rw [← hEq] at hcross
    exact (not_le_of_gt hfS) hcross
  have hslopeCont : ContinuousOn f (Ioc β s) := by
    intro u hu
    exact ((normalizedMinusBase_continuousAt h hu.1).add
      continuousAt_const).continuousWithinAt
  have hlogCont : ContinuousOn (logEnvelopePlus R xi c) (Icc β s) := by
    intro u hu
    have huR : β - 1 < u := by linarith [hu.1]
    have hRu : 0 < R u := h.positive u huR
    have hRc : ContinuousAt R u :=
      h.continuous.continuousAt (Ioi_mem_nhds huR)
    have hphase : ContinuousAt (xiPhase xi) u :=
      (xiPhase_hasDerivAt canonicalXi_proposition1020 u).continuousAt
    exact ((hRc.log (ne_of_gt hRu)).add hphase |>.add
      ((hasDerivAt_id u).const_mul c).continuousAt).continuousWithinAt
  have hderiv : ∀ u ∈ Ioc β s,
      HasDerivAt (logEnvelopePlus R xi c) (f u) u := by
    intro u hu
    have hu0 : 0 < u := by linarith [h.beta_ge_one, hu.1]
    have hRu : 0 < R u := h.positive u (by linarith [hu.1])
    have hd := logEnvelopePlus_hasDerivAt canonicalXi_proposition1020
      (c := c) hu0 hRu (h.original_dde u hu.1)
    convert hd using 1
    dsimp [f, normalizedMinusBase]
    ring
  have hbefore : ∀ u, S < u → u < s → 0 < f u := by
    intro u hSu hus
    have huv : u ≤ v := le_trans hus.le hsv
    by_contra hn
    have hfu : f u ≤ 0 := le_of_not_gt hn
    have huK : u ∈ K := ⟨⟨hSu.le, huv⟩, hfu⟩
    exact (not_le_of_gt hus) (hsleast huK)
  let w : PlusFirstCrossing R xi c β S :=
    { s := s
      slope := f
      beta_lt_s₀ := hβS
      s₀_lt_s := hSlt
      beta_add_one_le_s := hβoneS.trans hSs
      slope_continuousOn := hslopeCont
      logEnvelope_continuousOn := hlogCont
      hasDeriv := hderiv
      initial_pos := hinitial
      before_crossing_pos := hbefore
      crossing_nonpos := hcross }
  exact ⟨w, hSs⟩

/-- The topological producer, now proved rather than assumed. -/
theorem producesPlusFirstCrossing
    {R : ℝ → ℝ} {β c S : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hβS : β < S) (hβoneS : β + 1 ≤ S)
    (hinitial : ∀ u ∈ Icc β S, 0 < normalizedMinusBase R xi u + c) :
    ProducesPlusFirstCrossing R β c S := by
  intro v hSv hv
  exact plusFirstCrossing_of_reaches h hβS hβoneS hinitial hSv hv

/-- Plus half of the common-majorant conclusion.  This is an output type; no
input apparatus contains the final slope conclusion. -/
structure Section10PlusCommonMajorant (R : ℝ → ℝ) where
  cPlus : ℝ
  cutoff : ℝ
  one_le_cPlus : 1 ≤ cPlus
  four_le_cutoff : 4 ≤ cutoff
  envelope_slope_nonneg : ∀ s, cutoff ≤ s →
    0 ≤ -(R (s - 1)) + s * (xi s + cPlus - 2 / s) * R s


end Section10Lemma1028PlusAssembly


/-!
# Source-faithful stationary closure of the plus case of (10.55)

`plusPairingScalarRatio` above is the exact ratio before the source expansion.
It was previously called `equation1055PlusScalarRatio`; that attribution is
withdrawn: the printed (10.55) contains the positive `λ / (s A)` prefactor.
The definitions below record that prefactor literally and use the expansion only
at stationary candidates, exactly as in the source proof.
-/

namespace Section10Equation1055UniformStationary

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053NonCircular
open Section10CanonicalXi
open Section10Lemma1028PlusAssembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The denominator `A = ξ(s) + c - λ/s` in the first factor of (10.55). -/
noncomputable def equation1055PlusDenominator (lam c s : ℝ) : ℝ :=
  xi s + c - lam / s

/-- The exponentially small negative term displayed in the plus case of
(10.55). -/
noncomputable def equation1055PlusExponentialTerm (lam c s : ℝ) : ℝ :=
  lam * Real.exp (-c / 2) / (s * xi s)

/-- The literal two-factor scalar on the right of source (10.55).  In
particular, its positive correction is `λ / (s A)`, not merely `1/A`. -/
noncomputable def equation1055PlusScalarRatio
    (lam c s remainder : ℝ) : ℝ :=
  (1 + lam / (s * equation1055PlusDenominator lam c s)) *
    (1 - equation1055PlusExponentialTerm lam c s + remainder)

/-- A candidate is required to be stationary and to lie beyond the fixed
source cutoff `S₀`; no unconditional assertion over all points at infinity is
used. -/
structure PlusStationaryCandidate
    (R : ℝ → ℝ) (c S₀ : ℝ) where
  s : ℝ
  cutoff_le : S₀ ≤ s
  stationary : normalizedMinusBase R xi s + c = 0

/-- The source inputs used after (10.45)--(10.46).  The fields are the
stationary expansion (10.55), its two quantitative remainder estimates, and a
bounded fixed initial segment.  There is deliberately no final strict
inequality and no first-crossing producer field. -/
structure Equation1055StationarySource
    (R : ℝ → ℝ) (β S₀ : ℝ) where
  lam : ℝ
  C : ℝ
  remainder : ℝ → ℝ → ℝ
  lambda_pos : 0 < lam
  one_le_C : 1 ≤ C
  cutoff_pos : 0 < S₀
  initial_bounded :
    ∃ B : ℝ, ∀ u ∈ Icc β S₀, -normalizedMinusBase R xi u ≤ B
  denominator_pos : ∀ c, C ≤ c → ∀ w : PlusStationaryCandidate R c S₀,
    0 < equation1055PlusDenominator lam c w.s
  correction_lt_one : ∀ c, C ≤ c → ∀ w : PlusStationaryCandidate R c S₀,
    lam / (w.s * equation1055PlusDenominator lam c w.s) < 1
  exponential_dominated : ∀ c, C ≤ c → ∀ w : PlusStationaryCandidate R c S₀,
    equation1055PlusExponentialTerm lam c w.s ≤
      (1 / 4 : ℝ) * (lam / (w.s * equation1055PlusDenominator lam c w.s))
  remainder_control : ∀ c, C ≤ c → ∀ w : PlusStationaryCandidate R c S₀,
    |remainder c w.s| ≤
      (1 / 4 : ℝ) * (lam / (w.s * equation1055PlusDenominator lam c w.s))
  expansion : ∀ c, C ≤ c → ∀ w : PlusStationaryCandidate R c S₀,
    plusPairingScalarRatio xi c w.s =
      equation1055PlusScalarRatio lam c w.s (remainder c w.s)

/-- The source (10.55) scalar is strictly greater than one at every stationary
candidate, uniformly for all `c ≥ C`.  The positive `λ/(sA)` correction absorbs
both the exponentially small term and the signed remainder. -/
theorem equation1055_strict_at_stationary
    {R : ℝ → ℝ} {β S₀ c : ℝ}
    (src : Equation1055StationarySource R β S₀) (hc : src.C ≤ c)
    (w : PlusStationaryCandidate R c S₀) :
    1 < plusPairingScalarRatio xi c w.s := by
  let q : ℝ := src.lam /
    (w.s * equation1055PlusDenominator src.lam c w.s)
  let d : ℝ := equation1055PlusExponentialTerm src.lam c w.s
  let e : ℝ := src.remainder c w.s
  have hs0 : 0 < w.s := src.cutoff_pos.trans_le w.cutoff_le
  have hA : 0 < equation1055PlusDenominator src.lam c w.s :=
    src.denominator_pos c hc w
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos src.lambda_pos (mul_pos hs0 hA)
  have hq1 : q < 1 := by
    simpa only [q] using src.correction_lt_one c hc w
  have hd : d ≤ (1 / 4 : ℝ) * q := by
    simpa only [d, q] using src.exponential_dominated c hc w
  have heabs : |e| ≤ (1 / 4 : ℝ) * q := by
    simpa only [e, q] using src.remainder_control c hc w
  have he : -(1 / 4 : ℝ) * q ≤ e := by
    have := (abs_le.mp heabs).1
    linarith
  have hform : plusPairingScalarRatio xi c w.s =
      (1 + q) * (1 - d + e) := by
    rw [src.expansion c hc w]
    rfl
  rw [hform]
  nlinarith

/-- Uniform stationary formulation: for the fixed `S₀`, every `c` beyond the
single source threshold excludes every stationary candidate by strict (10.55).
-/
theorem equation1055_uniform_stationary
    {R : ℝ → ℝ} {β S₀ : ℝ}
    (src : Equation1055StationarySource R β S₀) :
    ∀ c, src.C ≤ c → ∀ w : PlusStationaryCandidate R c S₀,
      1 < plusPairingScalarRatio xi c w.s := by
  intro c hc w
  exact equation1055_strict_at_stationary src hc w

private def crossing_to_stationaryCandidate
    {R : ℝ → ℝ} {β c S₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (w : PlusFirstCrossing R xi c β S₀) (hS : S₀ ≤ w.s) :
    PlusStationaryCandidate R c S₀ := by
  refine ⟨w.s, hS, ?_⟩
  have heq := w.stationary_equation h canonicalXi_proposition1020
  dsimp [normalizedMinusBase]
  calc
    -R (w.s - 1) / (w.s * R w.s) + xi w.s - 2 / w.s + c =
        -(R (w.s - 1) / (w.s * R w.s)) +
          (xi w.s + c - 2 / w.s) := by ring
    _ = 0 := by rw [heq]; ring

/-- Plus common majorant with both former residual premises removed.  The
already-proved topological producer is invoked internally, and strict (10.55)
is needed only for the stationary crossing it produces. -/
noncomputable def section10_plus_commonMajorant_of_stationary_source
    {R : ℝ → ℝ} {β S₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (hβ : β ≤ 3) (hβS : β < S₀) (hβoneS : β + 1 ≤ S₀)
    (src : Equation1055StationarySource R β S₀) :
    Section10PlusCommonMajorant R := by
  let B : ℝ := Classical.choose src.initial_bounded
  have hB : ∀ u ∈ Icc β S₀, -normalizedMinusBase R xi u ≤ B :=
    Classical.choose_spec src.initial_bounded
  let c : ℝ := max src.C (max 1 (B + 1))
  have hCc : src.C ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := (le_max_left 1 (B + 1)).trans
    (le_max_right src.C (max 1 (B + 1)))
  have hBc : B + 1 ≤ c := (le_max_right 1 (B + 1)).trans
    (le_max_right src.C (max 1 (B + 1)))
  have hinitial : ∀ u ∈ Icc β S₀,
      0 < normalizedMinusBase R xi u + c := by
    intro u hu
    have huB := hB u hu
    linarith
  have hproducer : ProducesPlusFirstCrossing R β c S₀ :=
    producesPlusFirstCrossing h hβS hβoneS hinitial
  have hslope : ∀ s, 4 ≤ s → 0 ≤ normalizedMinusBase R xi s + c := by
    intro v hv4
    by_cases hvS : v ≤ S₀
    · have hβv : β ≤ v := hβ.trans (by linarith)
      exact (hinitial v ⟨hβv, hvS⟩).le
    · have hSv : S₀ ≤ v := (lt_of_not_ge hvS).le
      by_contra hn
      have hvnonpos : normalizedMinusBase R xi v + c ≤ 0 := le_of_not_ge hn
      obtain ⟨w, hSw⟩ := hproducer v hSv hvnonpos
      let wc : PlusStationaryCandidate R c S₀ :=
        crossing_to_stationaryCandidate h w hSw
      have hlower0 := equation1055_strict_at_stationary src hCc wc
      have hlower : 1 < plusPairingScalarRatio xi c w.s := by
        simpa only [wc, crossing_to_stationaryCandidate] using hlower0
      have hupper : plusPairingScalarRatio xi c w.s ≤ 1 :=
        plusFirstCrossing_scalarRatio_le_one h hadj w
      linarith
  refine ⟨c, 4, hc1, le_rfl, ?_⟩
  intro s hs
  have hs0 : 0 < s := by linarith
  have hRs : 0 < R s := h.positive s (by linarith [hβ])
  have hn := hslope s hs
  have hscale : 0 < s * R s := mul_pos hs0 hRs
  have heq :
      -(R (s - 1)) + s * (xi s + c - 2 / s) * R s =
        (s * R s) * (normalizedMinusBase R xi s + c) := by
    dsimp [normalizedMinusBase]
    field_simp [ne_of_gt hs0, ne_of_gt hRs]
    ring
  rw [heq]
  exact mul_nonneg hscale.le hn


end Section10Equation1055UniformStationary
