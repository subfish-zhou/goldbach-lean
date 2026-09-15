import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1017Comparison

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! A κ=1, source-facing core of Lemma 10.17.  The input package contains only
signed DDEs, positivity/continuity, and the already proved zero-pairing
identities.  In particular, no global comparison `|P| ≤ ρ Q` is a field. -/

noncomputable def adjointPlus (s : ℝ) : ℝ := s ^ 2 - 2 * s + 1 / 2

def adjointMinus (_s : ℝ) : ℝ := 1

theorem adjointPlus_dde (s : ℝ) :
    HasDerivAt (fun u => u * adjointPlus u)
      (2 * adjointPlus s + adjointPlus (s + 1)) s := by
  have hsquare := (hasDerivAt_id s).mul (hasDerivAt_id s)
  have hpoly := (hsquare.sub ((hasDerivAt_id s).const_mul 2)).add_const (1 / 2)
  have h := (hasDerivAt_id s).mul hpoly
  have hev :
      (id * fun u : ℝ => u * u - 2 * u + 1 / 2) =
        (fun u => u * adjointPlus u) := by
    funext u
    simp [adjointPlus, pow_two]
  rw [← hev]
  apply h.congr_deriv
  norm_num [adjointPlus]
  ring

theorem adjointMinus_dde (s : ℝ) :
    HasDerivAt (fun u => u * adjointMinus u)
      (2 * adjointMinus s - adjointMinus (s + 1)) s := by
  norm_num [adjointMinus]
  exact hasDerivAt_id s

theorem adjointPlus_pos {s : ℝ} (hs : 2 ≤ s) : 0 < adjointPlus s := by
  dsimp [adjointPlus]
  nlinarith [sq_nonneg (s - 1)]

/-- The exact admissible input boundary for the κ=1 P/Q argument. -/
structure SignedPQData (P Q : ℝ → ℝ) : Prop where
  continuousP : Continuous P
  continuousQ : Continuous Q
  positiveQ : ∀ s, 0 < s → 0 < Q s
  ddeP : ∀ s, 3 < s →
    HasDerivAt P (-(2 * P s - P (s - 1)) / s) s
  ddeQ : ∀ s, 3 < s →
    HasDerivAt Q (-(2 * Q s + Q (s - 1)) / s) s
  pairingP_zero : ∀ s, 3 ≤ s →
    s * adjointMinus s * P s +
      (∫ t in s - 1..s, adjointMinus (t + 1) * P t) = 0
  pairingQ_zero : ∀ s, 3 ≤ s →
    s * adjointPlus s * Q s -
      (∫ t in s - 1..s, adjointPlus (t + 1) * Q t) = 0

/-- Strict integral comparison behind Claim 10.18.  It uses the explicit
positive adjoint, rather than assuming any P/Q estimate. -/
theorem strict_adjoint_window
    {Q : ℝ → ℝ} (hQ : Continuous Q) (hQpos : ∀ t, 0 < t → 0 < Q t)
    {s : ℝ} (hs : 3 ≤ s) :
    adjointPlus s * (∫ t in s - 1..s, Q t) <
      ∫ t in s - 1..s, adjointPlus (t + 1) * Q t := by
  let g : ℝ → ℝ := fun t => (adjointPlus (t + 1) - adjointPlus s) * Q t
  have hcont : ContinuousOn g (Icc (s - 1) s) := by
    dsimp [g, adjointPlus]
    fun_prop
  have hnonneg : ∀ t ∈ Ioc (s - 1) s, 0 ≤ g t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hdiff : 0 ≤ adjointPlus (t + 1) - adjointPlus s := by
      have h₁ : 0 ≤ t - (s - 1) := by linarith [ht.1]
      have h₂ : 0 ≤ t + (s - 1) := by linarith [ht.1]
      dsimp [adjointPlus]
      nlinarith [mul_nonneg h₁ h₂]
    exact mul_nonneg hdiff (hQpos t ht0).le
  have hc_mem : s - 1 / 2 ∈ Icc (s - 1) s := by constructor <;> linarith
  have hc_pos : 0 < g (s - 1 / 2) := by
    apply mul_pos
    · dsimp [adjointPlus]
      nlinarith
    · apply hQpos
      linarith
  have hgap : 0 < ∫ t in s - 1..s, g t :=
    intervalIntegral.integral_pos (by linarith) hcont hnonneg
      ⟨s - 1 / 2, hc_mem, hc_pos⟩
  have hQint : IntervalIntegrable Q volume (s - 1) s := hQ.intervalIntegrable _ _
  have hWint : IntervalIntegrable (fun t => adjointPlus (t + 1) * Q t)
      volume (s - 1) s := by
    apply Continuous.intervalIntegrable
    dsimp [adjointPlus]
    fun_prop
  have heq :
      (∫ t in s - 1..s, g t) =
        (∫ t in s - 1..s, adjointPlus (t + 1) * Q t) -
          adjointPlus s * (∫ t in s - 1..s, Q t) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub hWint (hQint.const_mul (adjointPlus s))]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [g]
    ring
  rw [heq] at hgap
  linarith

/-- Claim 10.18, one-step strict improvement.  A weak envelope on the current
unit window becomes strict at its right endpoint.  This is the local induction
step; the data package itself contains no comparison assumption. -/
theorem claim10_18_one_step_strict
    {P Q : ℝ → ℝ} (h : SignedPQData P Q) {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : 3 ≤ s)
    (hwindow : ∀ t ∈ Icc (s - 1) s, |P t| ≤ ρ * Q t) :
    |P s| < ρ * Q s := by
  have hs0 : 0 < s := by linarith
  have hq : 0 < adjointPlus s := adjointPlus_pos (by linarith)
  have hQint : IntervalIntegrable Q volume (s - 1) s := h.continuousQ.intervalIntegrable _ _
  have hPint : IntervalIntegrable P volume (s - 1) s := h.continuousP.intervalIntegrable _ _
  have habsint : IntervalIntegrable (fun t => |P t|) volume (s - 1) s := hPint.norm
  have hrQint : IntervalIntegrable (fun t => ρ * Q t) volume (s - 1) s := hQint.const_mul ρ
  have hmono : (∫ t in s - 1..s, |P t|) ≤ ρ * (∫ t in s - 1..s, Q t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith) habsint hrQint hwindow
  have habs : |∫ t in s - 1..s, P t| ≤ ∫ t in s - 1..s, |P t| :=
    intervalIntegral.abs_integral_le_integral_abs (by linarith)
  have hQstrict := strict_adjoint_window h.continuousQ h.positiveQ hs
  have hQpair := h.pairingQ_zero s hs
  have hQwindow : (∫ t in s - 1..s, Q t) < s * Q s := by
    have hw : (∫ t in s - 1..s, adjointPlus (t + 1) * Q t) =
        s * adjointPlus s * Q s := by linarith
    rw [hw] at hQstrict
    nlinarith
  have hPpair := h.pairingP_zero s hs
  simp only [adjointMinus, one_mul, mul_one] at hPpair
  have hPeq : s * |P s| = |∫ t in s - 1..s, P t| := by
    have heq : s * P s = -(∫ t in s - 1..s, P t) := by linarith
    calc
      s * |P s| = |s * P s| := by rw [abs_mul, abs_of_pos hs0]
      _ = |∫ t in s - 1..s, P t| := by rw [heq, abs_neg]
  have hchain : s * |P s| < ρ * (s * Q s) := by
    rw [hPeq]
    calc
      |∫ t in s - 1..s, P t| ≤ ∫ t in s - 1..s, |P t| := habs
      _ ≤ ρ * (∫ t in s - 1..s, Q t) := hmono
      _ < ρ * (s * Q s) := mul_lt_mul_of_pos_left hQwindow hρ
  exact (mul_lt_mul_iff_right₀ hs0).mp (by simpa only [mul_left_comm ρ s] using hchain)

/-- Compact extraction of a uniform coefficient strictly below one.  This is
applied to the positive hat-layer identities `P=T⁺-T⁻`, `Q=T⁺+T⁻`; those
identities give the pointwise strict hypothesis without assuming a uniform
comparison. -/
theorem compact_eta_extraction
    {P Q : ℝ → ℝ} (hP : Continuous P) (hQ : Continuous Q)
    {a b : ℝ} (hab : a ≤ b) (hQpos : ∀ s ∈ Icc a b, 0 < Q s)
    (hpoint : ∀ s ∈ Icc a b, |P s| < Q s) :
    ∃ η : ℝ, 0 ≤ η ∧ η < 1 ∧
      ∀ s ∈ Icc a b, |P s| ≤ η * Q s := by
  let r : ℝ → ℝ := fun s => |P s| / Q s
  have hrcont : ContinuousOn r (Icc a b) := by
    apply ContinuousOn.div hP.abs.continuousOn hQ.continuousOn
    intro s hs
    exact ne_of_gt (hQpos s hs)
  have hne : (Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn hne hrcont
  refine ⟨r x, ?_, ?_, ?_⟩
  · exact div_nonneg (abs_nonneg _) (hQpos x hx).le
  · exact (div_lt_one (hQpos x hx)).mpr (hpoint x hx)
  · intro s hs
    have hrs : r s ≤ r x := hxmax hs
    exact (div_le_iff₀ (hQpos s hs)).mp hrs

/-- For the Section 13 definitions `P=T⁺-T⁻` and `Q=T⁺+T⁻`, the compact seed
is automatic from strict positivity of the two hat layers.  Thus the exported
seed theorem does not take any P/Q comparison as a premise. -/
theorem compact_eta_for_positive_pair
    {Tplus Tminus : ℝ → ℝ} (hp : Continuous Tplus) (hm : Continuous Tminus)
    {a b : ℝ} (hab : a ≤ b)
    (hp_pos : ∀ s ∈ Icc a b, 0 < Tplus s)
    (hm_pos : ∀ s ∈ Icc a b, 0 < Tminus s) :
    ∃ η : ℝ, 0 ≤ η ∧ η < 1 ∧
      ∀ s ∈ Icc a b,
        |Tplus s - Tminus s| ≤ η * (Tplus s + Tminus s) := by
  apply compact_eta_extraction (hp.sub hm) (hp.add hm) hab
  · intro s hs
    exact add_pos (hp_pos s hs) (hm_pos s hs)
  · intro s hs
    rw [abs_lt]
    change -(Tplus s + Tminus s) < Tplus s - Tminus s ∧
      Tplus s - Tminus s < Tplus s + Tminus s
    constructor <;> linarith [hp_pos s hs, hm_pos s hs]

/-- The compact seed followed by Claim 10.18 at its right endpoint. -/
theorem compact_eta_and_one_step
    {P Q : ℝ → ℝ} (h : SignedPQData P Q) {a : ℝ} (ha : 4 ≤ a)
    (hpoint : ∀ t ∈ Icc (a - 1) a, |P t| < Q t) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (∀ t ∈ Icc (a - 1) a, |P t| ≤ η * Q t) ∧
      |P a| < η * Q a := by
  obtain ⟨η₀, hη₀, hη₀1, hseed₀⟩ := compact_eta_extraction
    h.continuousP h.continuousQ (by linarith)
    (fun t ht => h.positiveQ t (by linarith [ht.1])) hpoint
  let η : ℝ := (η₀ + 1) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  have hseed : ∀ t ∈ Icc (a - 1) a, |P t| ≤ η * Q t := by
    intro t ht
    have hQt := h.positiveQ t (by linarith [ht.1])
    have hη₀η : η₀ ≤ η := by dsimp [η]; linarith
    exact (hseed₀ t ht).trans (mul_le_mul_of_nonneg_right hη₀η hQt.le)
  exact ⟨η, hη, hη1, hseed, claim10_18_one_step_strict h hη (by linarith) hseed⟩

/-- Section-13-shaped public endpoint: positivity of `T⁺,T⁻`, the defining
identities for `P,Q`, signed DDEs, explicit adjoints and pairing-zero produce a
uniform compact coefficient and its strict Claim-10.18 improvement.  There is
no comparison hypothesis in this statement. -/
theorem positive_pair_compact_eta_and_one_step
    {Tplus Tminus P Q : ℝ → ℝ} (h : SignedPQData P Q)
    (hP : P = fun s => Tplus s - Tminus s)
    (hQ : Q = fun s => Tplus s + Tminus s)
    {a : ℝ} (ha : 4 ≤ a)
    (hp_pos : ∀ s ∈ Icc (a - 1) a, 0 < Tplus s)
    (hm_pos : ∀ s ∈ Icc (a - 1) a, 0 < Tminus s) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (∀ s ∈ Icc (a - 1) a, |P s| ≤ η * Q s) ∧
      |P a| < η * Q a := by
  apply compact_eta_and_one_step h ha
  intro s hs
  rw [hP, hQ, abs_lt]
  change -(Tplus s + Tminus s) < Tplus s - Tminus s ∧
    Tplus s - Tminus s < Tplus s + Tminus s
  constructor <;> linarith [hp_pos s hs, hm_pos s hs]


end Section10Lemma1017Comparison
