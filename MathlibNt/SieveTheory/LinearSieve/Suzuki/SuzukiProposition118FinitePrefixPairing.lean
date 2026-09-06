import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceTailPairingZero
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveAmplitudeLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Proposition 11.8 from finite full-layer prefixes

The prefix below follows the production source definition exactly.  Above the
source boundary it contains the first `m` odd and first `m` even source layers;
below the boundary it uses the finite amplitude `A_m / s`.  Thus the initial
history is part of the prefix, rather than being silently replaced by the
out-of-domain values of the recursive layer formula.
-/

open scoped Classical BigOperators Interval
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The genuine full source prefix, including its prescribed initial history. -/
noncomputable def suzukiProposition118SourceQPrefix (m : ℕ) (s : ℝ) : ℝ :=
  if s < 2 then suzukiFiniteLowerAmplitude m / s
  else suzukiOddSourceUpperPartialSum m s + suzukiEvenSourceLowerPartialSum m s

/-- Only the last even layer is left after the finite weighted source equations
telescope.  It starts at the true delayed source boundary `s=3`; below that
point the finite initial history closes the telescope exactly. -/
noncomputable def suzukiProposition118SourceQTerminal (m : ℕ) (s : ℝ) : ℝ :=
  if 3 < s then suzukiLayer 1 2 (2 * m) (s - 1) else 0

/-- The corresponding single-terminal-layer pairing residual. -/
noncomputable def suzukiProposition118SourceQTerminalPairingResidual
    (m : ℕ) (y : ℝ) : ℝ :=
  ∫ s in (2 : ℝ)..y,
    suzukiProposition118KappaOneSourceAdjoint s *
      suzukiProposition118SourceQTerminal m s

theorem suzukiLayer_weighted_eq_integral_to_upper
    {β s : ℝ} {n : ℕ} (hβ : 1 < β) (hn : 2 ≤ n)
    (hs : β + sourceEpsilon n ≤ s) :
    s * suzukiLayer 1 β n s =
      ∫ t in s..(β + n), suzukiLayer 1 β (n - 1) (t - 1) := by
  have hs0 : 0 < s := by
    have heps : (0 : ℝ) ≤ sourceEpsilon n := Nat.cast_nonneg _
    linarith
  rw [show s * suzukiLayer 1 β n s = suzukiLayerNumerator 1 β n s by
    simpa using rpow_mul_suzukiLayer 1 β n hs0]
  rw [SwitchingPrinciple.suzukiLayerNumerator_eq_sourceRecursion_of_two_le β s hn]
  have hlower : recursionLower β s n = min s (β + n) := by
    unfold recursionLower
    rw [max_eq_left (by simpa [sourceEpsilon] using hs)]
  rw [hlower]
  by_cases hsb : s ≤ β + n
  · rw [min_eq_left hsb]
  · have hbs : β + n ≤ s := le_of_not_ge hsb
    rw [min_eq_right hbs, intervalIntegral.integral_same]
    symm
    calc
      (∫ t in s..(β + n), suzukiLayer 1 β (n - 1) (t - 1)) =
          ∫ _t in s..(β + n), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hbs] at ht
        apply suzukiLayer_eq_zero_of_le
        have hnsub : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
        linarith [ht.1, hnsub]
      _ = 0 := intervalIntegral.integral_zero

/-- Away from its parity threshold, the weighted recursive layer has the literal
source derivative.  No infinite sum is differentiated. -/
theorem hasDerivAt_weighted_suzukiLayer_of_threshold_lt
    {β s : ℝ} {n : ℕ} (hβ : 1 < β) (hn : 2 ≤ n)
    (hs : β + sourceEpsilon n < s) :
    HasDerivAt (fun u => u * suzukiLayer 1 β n u)
      (-suzukiLayer 1 β (n - 1) (s - 1)) s := by
  let f : ℝ → ℝ := fun t => suzukiLayer 1 β (n - 1) (t - 1)
  have hshift : β - KappaOneModel.eps (n - 1) < s - 1 := by
    have hpar : (n - 1) % 2 + n % 2 = 1 := by omega
    have hparR : (((n - 1) % 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = 1 := by
      exact_mod_cast hpar
    simp only [sourceEpsilon, KappaOneModel.eps]
    simp only [sourceEpsilon] at hs
    linarith
  have hfOn : ContinuousOn f (Ioi (β + sourceEpsilon n)) := by
    have hmap : Set.MapsTo (fun t : ℝ => t - 1)
        (Ioi (β + sourceEpsilon n)) (KappaOneModel.closedDomain β (n - 1)) := by
      intro t ht
      change β - KappaOneModel.eps (n - 1) ≤ t - 1
      have hpar : (n - 1) % 2 + n % 2 = 1 := by omega
      have hparR : (((n - 1) % 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = 1 := by
        exact_mod_cast hpar
      have heq : β - ((KappaOneModel.eps (n - 1) : ℕ) : ℝ) =
          β + ((sourceEpsilon n : ℕ) : ℝ) - 1 := by
        simp only [sourceEpsilon, KappaOneModel.eps]
        linarith
      rw [heq]
      exact sub_le_sub_right ht.le 1
    have hcomp := (KappaOneModel.regular hβ (n - 1)).continuous.comp
      (continuousOn_id.sub continuousOn_const) hmap
    exact hcomp.congr fun t _ =>
      (KappaOneModel.layer_eq_suzukiLayer β (n - 1) (t - 1)).symm
  have hf : ContinuousAt f s := by
    exact hfOn.continuousAt (Ioi_mem_nhds hs)
  have hInt : IntervalIntegrable f volume s (β + n) := by
    apply ContinuousOn.intervalIntegrable
    have hmap : Set.MapsTo (fun t : ℝ => t - 1) (Set.uIcc s (β + n))
        (KappaOneModel.closedDomain β (n - 1)) := by
        intro t ht
        rw [Set.mem_uIcc] at ht
        rcases ht with ht | ht
        · change β - KappaOneModel.eps (n - 1) ≤ t - 1
          exact le_of_lt (hshift.trans_le (sub_le_sub_right ht.1 1))
        · change β - KappaOneModel.eps (n - 1) ≤ t - 1
          have heps : KappaOneModel.eps (n - 1) ≤ n - 1 := by
            unfold KappaOneModel.eps
            omega
          have hepsR : (KappaOneModel.eps (n - 1) : ℝ) ≤ (n - 1 : ℕ) := by
            exact_mod_cast heps
          have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
            exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
          linarith [ht.1]
    have hcomp := (KappaOneModel.regular hβ (n - 1)).continuous.comp
      (continuousOn_id.sub continuousOn_const) hmap
    exact hcomp.congr fun t _ =>
      (KappaOneModel.layer_eq_suzukiLayer β (n - 1) (t - 1)).symm
  have hleft := intervalIntegral.integral_hasDerivAt_left hInt
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun t ht => hfOn.continuousAt (Ioi_mem_nhds ht)) s hs) hf
  have hevent : (fun u => u * suzukiLayer 1 β n u) =ᶠ[𝓝 s]
      (fun u => ∫ t in u..(β + n), suzukiLayer 1 β (n - 1) (t - 1)) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact suzukiLayer_weighted_eq_integral_to_upper hβ hn hu.le
  exact hleft.congr_of_eventuallyEq hevent


end MathlibNt.SieveTheory
