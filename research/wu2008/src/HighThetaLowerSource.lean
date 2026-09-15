import HighThetaSwitchedCount
import MathlibNt.Wu2008DoubleSieve.VariableLevelGeometry

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery Filter
open scoped Classical Topology
noncomputable section

/-- Actual lower-sieve entry on total-gap support. The ordinary AP error and
the genuine variable-level Rosser main term remain distinct. -/
theorem lower_on_actual_support {i N : ℕ} {δ η s : ℝ} (W : Fin i → Finset ℕ)
    (hN : 2 ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime)
    (hsize : ∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 1 ≤ s) :
    convolutionRosserMain N W false (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) -
      convolutionAPError N (convolutionModulusCutoff N δ) W ≤ wuBoxPhi N δ W s := by
  apply convolution_lower_sieve_with_AP_error W (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s)
  intro d hd
  have hd0 := boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hdQ : (d : ℝ) < (N : ℝ)^(1/2-δ) :=
    (hsize d hd).trans_lt (rpow_lt_rpow_of_exponent_lt hN1 (by linarith))
  have hq : 1 < (N : ℝ)^(1/2-δ)/d := (one_lt_div hdr).mpr hdQ
  have hg := variableRosser_geometry hq hs
  exact ⟨hg.2.1,(wuVariableRosserLevel_eq_combined N d δ).le⟩

/-- This is the actual lower Rosser source, NOT an asserted h improvement. -/
def LowerSourcePaid {i : ℕ} (N : ℕ) (δ ε C s : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  let M := convolutionRosserMain N W false (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s)
  let E := C*N/log (N : ℝ)^(18 : ℝ)
  M-E-ε*boxTheta N ((N : ℝ)^(1/2-δ)) W ≤ wuBoxPhiLE N δ W s ∧
    M-E ≤ wuBoxPhi N δ W s

/-- Constructed lower counts on the original and all occupied inserted boxes.
The BV source is actually applied to all prime labels, with its C before N;
there is no inherited Uk lower coefficient or independently chosen supremum. -/
theorem original_and_inserted_lower_source {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
        LowerSourcePaid N δ ε C s (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          LowerSourcePaid N δ ε C s (convolutionWuWindows N Δ (Fin.cons U V)) := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨C,hC,T1,hBV⟩ := convolution_bombieri_vinogradov 3 hη hδ (show (0 : ℝ)<18 by norm_num)
  obtain ⟨T2,hT24,hend⟩ := original_and_inserted_phi_endpoint hδ hδhi hε
  obtain ⟨T3,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨C,hC,max T2 (max T1 T3),hT24.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s hs ht
  have hN2 := (le_max_left T2 _).trans hN
  have hN1 := (le_max_left T1 T3).trans ((le_max_right T2 _).trans hN)
  have hN3 := (le_max_right T1 T3).trans ((le_max_right T2 _).trans hN)
  have hN4 := hT24.trans hN2
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN3 Δ hlo hhi
  have heps := hend N hN2 he Δ hlo hhi V hV hrect s hs ht
  have hconsume : ∀ {i : ℕ} (W : Fin i → Finset ℕ), i ≤ 3 →
      (∀ j p, p ∈ W j → p.Prime ∧ p.Coprime N ∧ (N : ℝ)^highEta ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      PhiEndpointPaid N δ ε s W → LowerSourcePaid N δ ε C s W := by
    intro i W hi hW hsize hp
    have hfinite := lower_on_actual_support W (show 2 ≤ N by omega) hη (fun j p hp => (hW j p hp).1) hsize hs
    have hb := hBV N hN1 i hi W hW
    dsimp [LowerSourcePaid]
    constructor <;> linarith [hp.2]
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hconsume _ (by norm_num)
    (fun j p hp => ⟨(hg.1 j p hp).1,(mem_convolutionWuWindows.mp hp).2.1,(hg.1 j p hp).2⟩)
    hg.2 heps.1,?_⟩
  intro U hw
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hconsume _ le_rfl
    (fun j p hp => ⟨(hig.1 j p hp).1,(mem_convolutionWuWindows.mp hp).2.1,(hig.1 j p hp).2⟩)
    hig.2 (heps.2 U hw)

end
end HighTheta
