import HighBoxRecoveryActualBoxes

namespace HighBoxRecovery
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
noncomputable section

/-- Literal actual residual bounds; no prime-count/li substitution is hidden here. -/
def RemainderBounds {i : ℕ} (N : ℕ) (δ A C K s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  let Q := (N : ℝ)^(1/2-δ)
  omega3SieveR1 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤ C*N/log (N : ℝ)^A ∧
  omega3SieveR2 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤
    K*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2))

/-- One threshold, original two-prime boxes and every occupied inserted box.
The balanced theorem is consumed through the proved actual membership geometry. -/
theorem original_and_inserted_R1_R2 {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hA : 0 < A) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∃ T : ℕ, 4 ≤ T ∧
    ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
    1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
    ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
    ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      RemainderBounds N δ A C K s t (convolutionWuWindows N Δ V) ∧
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
        RemainderBounds N δ A C K s t (convolutionWuWindows N Δ (Fin.cons U V)) := by
  have hη : 0 < highEta := by norm_num [highEta]
  have hδhalf : δ < 1/2 := lt_of_le_of_lt hδhi (by norm_num [highEta])
  obtain ⟨C,hC,T1,hT14,hR1⟩ := R1_total_slack 3 hδ hη hA
  obtain ⟨K,hK,hR2⟩ := R2_total_slack 3 hδ hδhalf hη
  obtain ⟨T2,hΔsmall⟩ := eventually_atTop.mp delta_eventually_small
  let F : ℝ := (max 1 (1/highEta))^(3+2)
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨C,K*F,hC,mul_pos hK hF,max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  obtain ⟨hΔ,hΔhi⟩ := hΔsmall N hN2 Δ hlo hhi
  have hpay : ∀ (i : ℕ) (W : Fin i → Finset ℕ), i ≤ 3 →
      (∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^highEta ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      RemainderBounds N δ A C (K*F) s t W := by
    intro i W hik hW hsize
    exact ⟨hR1 N hN1 i hik W hW hsize s t hs hst ht _,
      hR2 N hN4 i hik W hW hsize s t hs hst ht⟩
  have hbase := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hpay 2 _ (by norm_num) hbase.1 hbase.2, ?_⟩
  intro U hw
  have hins := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hpay 3 _ le_rfl hins.1 hins.2

end
end HighBoxRecovery
