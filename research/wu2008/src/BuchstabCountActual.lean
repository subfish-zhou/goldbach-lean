import BuchstabCountGrid

namespace BuchstabCount
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology
noncomputable section

/-- Every actually occupied cell pays its complete Phi with the strict
inserted H gain. The one threshold precedes all original endpoints and
both moving parameters, and no empty cell is presumed occupied. -/
theorem occupied_tail_paid {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 → ∀ r : ℕ,
      ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s) <
        reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 (r+1) →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) 3 -
        (1-1/10000)*InsertedGain.coverTheta N δ Δ V s r ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  obtain ⟨T0,hT04,hpaid⟩ := InsertedGain.inserted_initial_range hδ hδhi
  obtain ⟨T1,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s hs hsmax r hrhi
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN4 := hT04.trans hN0
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hVp : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hNr _).trans_le (hV l)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos hlog (-4 : ℝ)
    linarith only [hh,hlo]
  obtain ⟨_,hΔhi⟩ := hsmall N hN1 Δ hlo hhi
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ.le hΔhi hV hrect
  have hQ := (HighCross.support_admission _ (show 2 ≤ N by omega)
    (show 0 < highEta by norm_num [highEta]) (fun l p hp => (hg.1 l p hp).1) hg.2).2
  have hsplit := buchstab_occupied_exact (show 0 < N by omega) hΔ hVp
    (fun d hd => (hQ d hd).le) hs (show s ≤ 3 by linarith) hrhi
  have hsum :
      (∑ j ∈ InsertedGain.occupiedCells N δ Δ V s r,
        ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d 3) (wuLocalCutoff N δ d s) ∩
            HighOmega2.cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 j,
            (sourceSieveCount N (d*p) ((d*p)*N) (p : ℝ) : ℝ)) ≤
        (1-1/10000)*InsertedGain.coverTheta N δ Δ V s r := by
    rw [InsertedGain.coverTheta, mul_sum]
    apply sum_le_sum
    intro j hj
    obtain ⟨d,hd,p,hp,hcell⟩ := (mem_filter.mp hj).2
    have hactual := HighOmega2.occupied_cell hΔ hs (show s ≤ 3 by linarith)
      (by norm_num : (3 : ℝ) ≤ 10) hd (mem_inter.mpr ⟨hp,hcell⟩)
    exact (clipped_cell_le_phi N j δ Δ s V (by linarith)).trans
      (hpaid N hN0 he Δ hlo hhi V hV hrect _ hactual (29/10) (by norm_num) le_rfl).2
  linarith only [hsplit,hsum]

end
end BuchstabCount
