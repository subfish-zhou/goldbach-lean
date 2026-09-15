import HighThetaTerminal
import MathlibNt.Wu2008DoubleSieve.OmegaWeighted
import MathlibNt.Wu2008DoubleSieve.Omega3SwitchingExceptional

namespace HighCross
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- Actual upper Rosser main plus the full convolution AP error. -/
def rosserUpper {i : ℕ} (N : ℕ) (δ s : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  convolutionRosserMain N W true (wuVariableRosserLevel N δ)
    (fun d => wuLocalCutoff N δ d s) +
    convolutionAPError N (convolutionModulusCutoff N δ) W

/-- No switching exception or repeated-prime label is discarded. -/
def switchingLoss {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  omega3BadDCount N δ s t W + omega3ExceptionalOutputCount N δ s t W +
    wuOmegaRepeatedSum N δ s t W

/-- The actual signed first-weighted candidate, not an Uk coefficient. -/
def switchedUpper {i : ℕ} (N : ℕ) (δ ε ρ s t : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  rosserUpper N δ t W - wuOmega2Sum N δ s t W / 2 +
    (liX N δ s t W * switchedDensity N δ ρ +
      ε * boxTheta N ((N : ℝ)^(1/2-δ)) W + switchingLoss N δ s t W) / 2

/-- A constructed nonnegative improvement of the finite Rosser *upper bound*.
Strict positivity is a separate arithmetic obligation, not built into the name. -/
def finiteGain {i : ℕ} (N : ℕ) (δ ε ρ s t : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  max 0 (rosserUpper N δ s W - switchedUpper N δ ε ρ s t W)

theorem rosser_upper {i N : ℕ} {δ s : ℝ} (W : Fin i → Finset ℕ)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 < (N : ℝ)^(1/2-δ)/d)
    (hs : 1 ≤ s) : wuBoxPhi N δ W s ≤ rosserUpper N δ s W := by
  apply convolution_upper_sieve_with_AP_error
  intro d hd
  have hg := variableRosser_geometry (hQ d hd) hs
  exact ⟨hg.1, hg.2.1, (wuVariableRosserLevel_eq_combined N d δ).le⟩

theorem omega1_eq_twice_phi {i : ℕ} (N : ℕ) (δ t : ℝ) (W : Fin i → Finset ℕ) :
    wuOmega1Sum N δ t W = 2 * wuBoxPhi N δ W t := by
  simp only [wuOmega1Sum, wuOmega1, wuBoxPhi, convolutionSieveCount,
    boxConvolutionSupport, mul_left_comm (convolutionCoeff W _ : ℝ) 2, mul_sum]

/-- Consumes the physical switched count in the literal signed mother. -/
theorem switched_upper {i N : ℕ} {δ ε ρ s t : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (he : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 < (N : ℝ)^(1/2-δ)/d)
    (hs : 2 ≤ s) (hst : s ≤ t)
    (hpaid : SwitchedUpperPaid N δ ε ρ s t W) :
    wuBoxPhi N δ W s ≤ switchedUpper N δ ε ρ s t W := by
  have hw := wu_omega_weighted_box (N := N) (δ := δ) (s := s) (t := t) W
    (fun d hd' => rpow_le_rpow_of_exponent_le (hQ d hd').le
      (one_div_le_one_div_of_le (by linarith) hst))
  have hx := wuOmega3Sum_le_switched_add_badD_add_exceptional
    (δ := δ) (s := s) (t := t) hN he hd
  have hu := rosser_upper (s := t) W hQ (by linarith)
  rw [omega1_eq_twice_phi] at hw
  have hp := hpaid.2
  dsimp [switchedUpper, switchingLoss]
  linarith

theorem finiteGain_nonneg {i : ℕ} (N : ℕ) (δ ε ρ s t : ℝ) (W : Fin i → Finset ℕ) :
    0 ≤ finiteGain N δ ε ρ s t W := le_max_left _ _

/-- Precise remaining positive-gain test, with the signed Omega2 and all costs.
This is an equivalence, not a proof that the test holds on the high domain. -/
theorem finiteGain_pos_iff {i : ℕ} (N : ℕ) (δ ε ρ s t : ℝ) (W : Fin i → Finset ℕ) :
    0 < finiteGain N δ ε ρ s t W ↔
      2 * (rosserUpper N δ t W - rosserUpper N δ s W) +
        liX N δ s t W * switchedDensity N δ ρ +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) W + switchingLoss N δ s t W <
      wuOmega2Sum N δ s t W := by
  rw [finiteGain, lt_max_iff]
  dsimp [switchedUpper]
  constructor
  · rintro (h | h)
    · exact (lt_irrefl (0 : ℝ) h).elim
    · linarith
  · intro h
    right
    linarith

/-- Finite nonnegative gain is subtracted from the same actual upper bound. -/
theorem improved_upper {i N : ℕ} {δ ε ρ s t : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (he : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 < (N : ℝ)^(1/2-δ)/d)
    (hs : 2 ≤ s) (hst : s ≤ t)
    (hpaid : SwitchedUpperPaid N δ ε ρ s t W) :
    wuBoxPhi N δ W s ≤ rosserUpper N δ s W - finiteGain N δ ε ρ s t W := by
  have hR := rosser_upper W hQ (show 1 ≤ s by linarith)
  have hS := switched_upper W hN he hd hQ hs hst hpaid
  unfold finiteGain
  rcases le_total (rosserUpper N δ s W) (switchedUpper N δ ε ρ s t W) with h | h
  · rw [max_eq_left (sub_nonpos.mpr h), sub_zero]
    exact hR
  · rw [max_eq_right (sub_nonneg.mpr h)]
    linarith

/-- High-box geometry gives the only support admission used above. -/
theorem support_admission {i N : ℕ} {δ η : ℝ} (W : Fin i → Finset ℕ)
    (hN : 2 ≤ N) (hη : 0 < η) (hW : ∀ j p, p ∈ W j → p.Prime)
    (hsize : ∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) :
    (∀ d ∈ boxConvolutionSupport W, 0 < d) ∧
      (∀ d ∈ boxConvolutionSupport W, 1 < (N : ℝ)^(1/2-δ)/d) := by
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun d hd => boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
  refine ⟨hd, ?_⟩
  intro d hd'
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd d hd'
  apply (one_lt_div hdr).mpr
  exact (hsize d hd').trans_lt
    (rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < N by omega)) (by linarith))

/-- Actual original and one-insertion upper improvements are constructed,
with epsilon/rho before the common threshold, and without any positive-gain binder. -/
theorem original_and_inserted_improved_upper {δ ε ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        (let W := convolutionWuWindows N Δ V
         wuBoxPhi N δ W s ≤ rosserUpper N δ s W - finiteGain N δ ε ρ s t W) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          let W := convolutionWuWindows N Δ (Fin.cons U V)
          wuBoxPhi N δ W s ≤ rosserUpper N δ s W - finiteGain N δ ε ρ s t W := by
  obtain ⟨T1,hT14,hpaid⟩ := original_and_inserted_switched_upper hδ hδhi hε hρ
  obtain ⟨T2,hsmall⟩ := Filter.eventually_atTop.mp delta_eventually_small
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have hp := hpaid N hN1 he Δ hlo hhi V hV hrect s t hs hst ht
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  have ha := support_admission _ (show 2 ≤ N by omega)
    (show 0 < highEta by norm_num [highEta]) (fun j p hp => (hg.1 j p hp).1) hg.2
  refine ⟨improved_upper _ hN4 he ha.1 ha.2 hs hst hp.1,?_⟩
  intro U hw
  have hi := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  have ha' := support_admission _ (show 2 ≤ N by omega)
    (show 0 < highEta by norm_num [highEta]) (fun j p hp => (hi.1 j p hp).1) hi.2
  exact improved_upper _ hN4 he ha'.1 ha'.2 hs hst (hp.2 U hw)

end
end HighCross
