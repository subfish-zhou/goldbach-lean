import HighThetaJoint
import MathlibNt.Wu2008DoubleSieve.PhiEndpoint

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- Finite reciprocal-mass payment from total support. No squared prefix,
no prime-count/li identification and no deletion of endpoint atoms. -/
theorem phi_endpoint_from_support {δ η ε : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (W : Fin i → Finset ℕ),
      (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
        0 ≤ wuBoxPhi N δ W s - wuBoxPhiLE N δ W s ∧
        wuBoxPhi N δ W s - wuBoxPhiLE N δ W s ≤
          ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  let c : ℝ := 2*liuUniversalProduct
  have hc : 0 < c := by dsimp [c]; have := liuUniversalProduct_pos; positivity
  obtain ⟨T1,hbudget⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 2 (show 0 < 1/(ε*c) by positivity) hη)
  refine ⟨max 4 T1,le_max_left _ _,?_⟩
  intro N hN he i W hW hsize s hs ht
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_right _ _).trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun d hd => boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
  have hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d s :=
    fun d hd' => cutoff_lower (show 2 ≤ N by omega) (hd d hd') hη
    (show 0 < s by linarith) ht (hsize d hd')
  have hfinite := wuBoxPhi_endpoint_le_mass W hN4 he
    (rpow_pos_of_pos hNr η) hd hcut
  have htheta := theta_from_actual_support W hN4 hδ hη hW hsize
  have hM : 0 ≤ boxConvolutionReciprocalMass W := by
    unfold boxConvolutionReciprocalMass
    exact sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine ⟨sub_nonneg.mpr (wuBoxPhiLE_le_strict N δ W s), ?_⟩
  calc
    _ ≤ (N : ℝ)/(N : ℝ)^η*boxConvolutionReciprocalMass W := hfinite
    _ ≤ (N : ℝ)/((1/(ε*c))*log N^2)*boxConvolutionReciprocalMass W :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hNr.le (by positivity) (hbudget N hN1)) hM
    _ = ε*(c*N/log N^2*boxConvolutionReciprocalMass W) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

/-- Both physical conventions and the exact weighted endpoint loss. -/
def PhiEndpointPaid {i : ℕ} (N : ℕ) (δ ε s : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  0 ≤ wuBoxPhi N δ W s - wuBoxPhiLE N δ W s ∧
    wuBoxPhi N δ W s - wuBoxPhiLE N δ W s ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) W

/-- Actual original and inserted Phi endpoints, sharing a single threshold. -/
theorem original_and_inserted_phi_endpoint {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
        PhiEndpointPaid N δ ε s (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          PhiEndpointPaid N δ ε s (convolutionWuWindows N Δ (Fin.cons U V)) := by
  obtain ⟨T1,hT14,hpay⟩ := phi_endpoint_from_support hδ.le
    (show 0 < highEta by norm_num [highEta]) hε
  obtain ⟨T2,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s hs ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hpay N hN1 he 2 _ (fun j p hp => (hg.1 j p hp).1) hg.2 s hs ht, ?_⟩
  intro U hw
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hpay N hN1 he 3 _ (fun j p hp => (hig.1 j p hp).1) hig.2 s hs ht

end
end HighTheta
