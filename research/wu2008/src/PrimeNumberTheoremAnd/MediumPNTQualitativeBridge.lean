import PrimeNumberTheoremAnd.PNTEnvironmentCompat
import PrimeNumberTheoremAnd.MediumPNT
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-! Qualitative prime counting from the quantitative MediumPNT bound.
The proof uses the psi-theta gap and Chebyshev's prime-counting estimate. -/

namespace AnalyticNumberTheory.PrimeDistribution.MediumBridge

open Asymptotics Filter Real
open scoped Topology

private theorem sqrt_isLittleO_id : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro hzero
    exact (hx.ne' hzero).elim
  · convert! Real.tendsto_sqrt_atTop.inv_tendsto_atTop using 1
    ext x
    simp only [id_eq, Real.sqrt_div_self, Pi.inv_apply]

private theorem logSquaredScale_isLittleO :
    (fun x : ℝ => x / log x ^ 2) =o[atTop] (fun x => x / log x) := by
  -- Same quotient reduction as pinned Chebyshev.integral_theta_div_log_sq_isLittleO.
  refine (isLittleO_iff_tendsto' (by simp)).mpr ?_
  refine Tendsto.congr' (f₁ := fun x => (log x)⁻¹) ?_
    tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
  field

/-- Only the eventual equivalence is analytic; the all-real identity is algebraic. -/
private theorem realPrimeCountingNormalForm_of_equivalent
    (hpi : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x => x / log x)) :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  refine ⟨fun x => (log x / x) * Nat.primeCounting ⌊x⌋₊ - 1, ?_, ?_⟩
  · rw [isLittleO_one_iff]
    have hz : ∀ᶠ x : ℝ in atTop, x / log x ≠ 0 := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)) (log_pos hx).ne'
    have hratio := (isEquivalent_iff_tendsto_one hz).mp hpi
    have hratio' : Tendsto
        (fun x : ℝ => (log x / x) * Nat.primeCounting ⌊x⌋₊) atTop (𝓝 1) := by
      convert hratio using 1
      funext x
      simp only [Pi.div_apply, div_div_eq_mul_div]
      ring
    simpa using hratio'.sub_const 1
  · -- Preserve the original pi_alt total-field cases, including x=-1.
    intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

/-- MediumPNT alone supplies the qualitative psi-to-prime-counting bridge. -/
private theorem primeCounting_equivalent_of_medium
    {c : ℝ} (hc : 0 < c)
    (hmedium : (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)))) :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x => x / log x) := by
  have hdecay :
      (fun x : ℝ => exp (-c * log x ^ ((1 : ℝ) / 10))) =o[atTop]
        (fun _ => (1 : ℝ)) := by
    simpa only [Real.rpow_zero, Function.comp_def] using
      (isLittleO_exp_neg_mul_rpow_atTop hc (0 : ℝ)).comp_tendsto
        ((tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp
          Real.tendsto_log_atTop)
  have hscale :
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10))) =o[atTop]
        (id : ℝ → ℝ) := by
    convert! (isBigO_refl (id : ℝ → ℝ) atTop).mul_isLittleO hdecay using 1
    simp only [id_eq, mul_one]
    rfl
  have hpsi : Chebyshev.psi ~[atTop] (id : ℝ → ℝ) :=
    hmedium.trans_isLittleO hscale
  have hgap : (Chebyshev.psi - Chebyshev.theta) =o[atTop] (id : ℝ → ℝ) :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO sqrt_isLittleO_id
  have htheta : Chebyshev.theta ~[atTop] (id : ℝ → ℝ) := by
    convert! hpsi.sub_isLittleO hgap using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hthetaLog :
      (fun x : ℝ => Chebyshev.theta x / log x) ~[atTop]
        (fun x => x / log x) :=
    htheta.div (IsEquivalent.refl (u := log))
  have hcountError :
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / log x)
        =o[atTop] (fun x => x / log x) :=
    Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO
      logSquaredScale_isLittleO
  convert! hthetaLog.add_isLittleO hcountError using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- Exact original public statement; no extra assumption or restriction on x. -/
theorem primeCounting_asymptotic_real :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨c, hc, hmedium⟩ := MediumPNT
  exact realPrimeCountingNormalForm_of_equivalent
    (primeCounting_equivalent_of_medium hc hmedium)

end AnalyticNumberTheory.PrimeDistribution.MediumBridge

/-! Compatibility exports: original source statements and pure helper preserved. -/
open Asymptotics Filter Real Nat
open scoped Topology

lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x :=
  AnalyticNumberTheory.PrimeDistribution.MediumBridge.primeCounting_asymptotic_real

theorem pi_alt' :
    (fun (x : ℝ) ↦ (primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / log x) := by
  obtain ⟨f, ⟨hf1, hf2⟩⟩ := pi_alt
  simp_rw [hf2, IsEquivalent]
  have : ((fun x ↦ (1 + f x) * x / Real.log x) - fun x ↦ x / Real.log x) =
      (fun x ↦ f x * x / Real.log x) := by
    ext
    simp
    ring
  rw [this]
  convert hf1.mul_isBigO (f₂ := (fun x ↦ x / Real.log x)) (g₂ := (fun x ↦ x /Real.log x))
      (isBigO_refl ..) using 2
  all_goals first | ring | rfl
