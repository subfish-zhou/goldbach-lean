import HighCrossTransport
import MathlibNt.Wu2008DoubleSieve.ReboxingSorted

namespace HighCross
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery Filter
open scoped Classical
noncomputable section

/-- Same-mother finite cross lower, before normalization to a universal h.
The inserted gains are actual signed-count candidates from HighCrossFinite. -/
def crossMain {i : ℕ} {β : Type*} [DecidableEq β]
    (N : ℕ) (δ ε ρ C t : ℝ) (W : Fin i → Finset ℕ)
    (B : Finset β) (P : β → Finset ℕ) (u v : β → ℝ) : ℝ :=
  convolutionRosserMain N W false (wuVariableRosserLevel N δ)
      (fun d => wuLocalCutoff N δ d t) - C*N/log (N : ℝ)^(18 : ℝ) -
    (∑ b ∈ B, rosserUpper N δ (u b) (Fin.cons (P b) W)) +
    ∑ b ∈ B, finiteGain N δ ε ρ (u b) (v b) (Fin.cons (P b) W)

/-- All arithmetic producers are constructed. Only the literal finite prime
cover and cutoff comparisons are premises; neither h/H nor an analytic
cross-lower estimate is assumed. This permits one feedback step, not all depths. -/
theorem original_cross_lower {δ ε ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ (B : Finset ℕ) (U u v : ℕ → ℝ),
      (∀ b ∈ B, ActualInsertion N δ Δ (U b) V) →
      (∀ b ∈ B, 2 ≤ u b ∧ u b ≤ v b ∧ v b ≤ 10) →
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ∀ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        ∃ b ∈ B, p ∈ primeWindow N (U b/Δ) (U b) ∧
          wuLocalCutoff N δ (d*p) (u b) ≤ (p : ℝ)) →
      let W := convolutionWuWindows N Δ V
      let P := fun b => primeWindow N (U b/Δ) (U b)
      crossMain N δ ε ρ C t W B P u v ≤ wuBoxPhi N δ W s ∧
        crossMain N δ ε ρ C t W B P u v -
          ε*boxTheta N ((N : ℝ)^(1/2-δ)) W ≤ wuBoxPhiLE N δ W s := by
  obtain ⟨T1,hT14,hup⟩ := original_and_inserted_improved_upper hδ hδhi hε hρ
  obtain ⟨C,hC,T2,_,hlo⟩ := original_and_inserted_lower_source hδ hδhi hε
  obtain ⟨T3,_,hend⟩ := original_and_inserted_phi_endpoint hδ hδhi hε
  obtain ⟨T4,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨C,hC,max T1 (max T2 (max T3 T4)),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hΔlo hΔhi V hV hrect s t hs hst ht B U u v hocc huv hcover
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_left T3 T4).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hN4 := (le_max_right T3 T4).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hNfour := hT14.trans hN1
  obtain ⟨hΔ,hΔbound⟩ := hsmall N hN4 Δ hΔlo hΔhi
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔbound hV hrect
  have ha := support_admission _ (show 2 ≤ N by omega)
    (show 0 < highEta by norm_num [highEta]) (fun j p hp => (hg.1 j p hp).1) hg.2
  have hupper : ∀ b ∈ B,
      wuBoxPhi N δ (Fin.cons (primeWindow N (U b/Δ) (U b)) (convolutionWuWindows N Δ V)) (u b) ≤
      rosserUpper N δ (u b) (Fin.cons (primeWindow N (U b/Δ) (U b)) (convolutionWuWindows N Δ V)) -
      finiteGain N δ ε ρ (u b) (v b) (Fin.cons (primeWindow N (U b/Δ) (U b)) (convolutionWuWindows N Δ V)) := by
    intro b hb
    have hu := (hup N hN1 he Δ hΔlo hΔhi V hV hrect (u b) (v b)
      (huv b hb).1 (huv b hb).2.1 (huv b hb).2.2).2 (U b) (hocc b hb)
    simpa only [convolutionWuWindows_cons] using hu
  have hl := (hlo N hN2 he Δ hΔlo hΔhi V hV hrect t (by linarith) ht).1
  have he' := (hend N hN3 he Δ hΔlo hΔhi V hV hrect s (by linarith) (hst.trans ht)).1
  exact ⟨cross_lower_from_counts _ B _ u _ _ (fun d hd => (ha.2 d hd).le)
      (by linarith) hst hcover hupper hl,
    cross_lower_closed _ B _ u _ _ (fun d hd => (ha.2 d hd).le)
      (by linarith) hst hcover hupper hl he'⟩

/-- The transported gain is a real finite sum, never an independent supremum. -/
theorem feedback_gain_nonneg {i : ℕ} {β : Type*} [DecidableEq β]
    (N : ℕ) (δ ε ρ : ℝ) (W : Fin i → Finset ℕ)
    (B : Finset β) (P : β → Finset ℕ) (u v : β → ℝ) :
    0 ≤ ∑ b ∈ B, finiteGain N δ ε ρ (u b) (v b) (Fin.cons (P b) W) :=
  sum_nonneg (fun b _ => finiteGain_nonneg N δ ε ρ (u b) (v b) _)

/-- Exact strict-gain witness criterion in the same actual finite mother.
No assertion that such a witness has been proved to exist is made. -/
theorem feedback_gain_pos_of_actual_gap {i : ℕ} {β : Type*} [DecidableEq β]
    (N : ℕ) (δ ε ρ : ℝ) (W : Fin i → Finset ℕ)
    (B : Finset β) (P : β → Finset ℕ) (u v : β → ℝ)
    (b : β) (hb : b ∈ B)
    (hgap :
      2 * (rosserUpper N δ (v b) (Fin.cons (P b) W) - rosserUpper N δ (u b) (Fin.cons (P b) W)) +
        liX N δ (u b) (v b) (Fin.cons (P b) W) * switchedDensity N δ ρ +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (Fin.cons (P b) W) +
        switchingLoss N δ (u b) (v b) (Fin.cons (P b) W) <
      wuOmega2Sum N δ (u b) (v b) (Fin.cons (P b) W)) :
    0 < ∑ c ∈ B, finiteGain N δ ε ρ (u c) (v c) (Fin.cons (P c) W) := by
  have hg := (finiteGain_pos_iff N δ ε ρ (u b) (v b) (Fin.cons (P b) W)).mpr hgap
  have hsum : finiteGain N δ ε ρ (u b) (v b) (Fin.cons (P b) W) ≤
      ∑ c ∈ B, finiteGain N δ ε ρ (u c) (v c) (Fin.cons (P c) W) :=
    single_le_sum (f := fun c => finiteGain N δ ε ρ (u c) (v c) (Fin.cons (P c) W))
      (fun c _ => finiteGain_nonneg N δ ε ρ (u c) (v c) _) hb
  exact hg.trans_le hsum

end
end HighCross
