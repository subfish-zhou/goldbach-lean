import CoverMassPayment

namespace CoverMass
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- Sharp mass of the original occupied full insertion cover. No cell is
removed, no tuple symmetry is divided out, and the threshold is common to
all original boxes and symbolic terminals. The proof also admits odd N. -/
theorem original_cover_upper {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ j, V j)) Δ 3 r ≤
        ((N : ℝ)^(1/2-δ)/(∏ j, V j))^(1/s) →
      ((N : ℝ)^(1/2-δ)/(∏ j, V j))^(1/s) <
        reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ j, V j)) Δ 3 (r+1) →
      InsertedGain.coverTheta N δ Δ V s r ≤
        (log (2/(s-1))+ε)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := full_grid_kernel hε
  refine ⟨T,hT4,?_⟩
  intro N hN Δ hlo hhi V hV hrect s hs hs3 r hrlo hrhi
  have hN4 := hT4.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hΔ := (delta_log_bound (log_pos hNr) hlo hhi).1
  have hΔ0 : 0 < Δ := by linarith
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ)^(1/2-δ)
  let q := Q/(∏ j, V j)
  let P := primeWindow N (q^(1/3 : ℝ)) (reboxingAlpha q Δ 3 (r+2))
  let C := log (2/(s-1))+ε
  have hVp : ∀ j, 0 < V j := fun j => (rpow_pos_of_pos hN0 _).trans_le (hV j)
  have hQ0 : 0 < Q := rpow_pos_of_pos hN0 _
  have hqbase := (original_base_gap (show 2 ≤ N by omega) hδ.le hδhi hV hrect).1
  have hq : 1 < q := (one_lt_rpow hNr (show 0 < 10*highEta by norm_num [highEta])).trans_le hqbase
  have hq0 : 0 < q := by linarith
  have hg := fun d hd => HighO2Terminal.original_support (show 2 ≤ N by omega)
    hδ.le hδhi hΔ0 hV hrect (d := d) hd
  have hlevels := fun d hd => reboxing_support_level_bounds hQ0.le hΔ0 hVp (N := N) (d := d) hd
  have hf := fun d hd => hT N hN Δ hlo hhi d (hg d hd).1 (hg d hd).2.1 q (Q/d)
    hqbase (hlevels d hd).1 (hlevels d hd).2 s hs hs3 r hrlo hrhi
  have hPall {p : ℕ} (hp : p ∈ P) :
      p ∈ primeWindow 1 (q^(1/3 : ℝ)) (reboxingAlpha q Δ 3 (r+2)) := by
    obtain ⟨hpp,_,hpa,hpb⟩ := mem_primeWindow.mp hp
    exact mem_primeWindow.mpr ⟨hpp,Nat.coprime_one_right p,hpa,hpb⟩
  have hgap : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P, 1 < Q/((d : ℝ)*p) := by
    intro d hd p hp
    have hh := (hf d hd).2.2.1 p (hPall hp)
    have hD : 1 < Q/d := (hg d hd).2.2.2.2
    have hp0 : (0 : ℝ) < p := by linarith [hh.1]
    have hlog : 0 < log ((Q/d)/(p : ℝ)) := by
      rw [reboxing_log_denominator hD hp0]
      exact mul_pos (log_pos hD) (by linarith [hh.2])
    have hpos : 0 < (Q/d)/(p : ℝ) := div_pos (by linarith) hp0
    have hlt : 1 < (Q/d)/(p : ℝ) := by
      by_contra h
      have := log_nonpos hpos.le (le_of_not_gt h)
      linarith
    convert hlt using 1; ring
  have hcellsub : ∀ j ∈ range (r+2), cell N q Δ 3 j ⊆ P := by
    intro j hj p hp
    obtain ⟨hpp,hpN,hpl,hpu⟩ := mem_primeWindow.mp hp
    have hm := (reboxingAlpha_strictMono hq0 hΔ (t := (3 : ℝ))).monotone
    refine mem_primeWindow.mpr ⟨hpp,hpN,?_,?_⟩
    · have h0 := hm (show (0 : ℝ) ≤ (j : ℝ) by positivity)
      have h0' : q^(1/3 : ℝ) ≤ reboxingAlpha q Δ 3 (j : ℝ) := by
        simpa only [reboxingAlpha_zero] using h0
      exact h0'.trans hpl
    · have hjr : (j : ℝ)+1 ≤ (r : ℝ)+2 := by exact_mod_cast (show j+1 ≤ r+2 by have := mem_range.mp hj; omega)
      exact hpu.trans_le (hm hjr)
  have hcell0 : ∀ j ∈ range (r+2), 0 ≤ boxTheta N Q (Fin.cons (cell N q Δ 3 j) W) := by
    intro j hj
    exact inserted_theta_nonneg W _ hN4 (fun d hd => (hg d hd).1)
      (fun p hp => (mem_primeWindow.mp hp).1.pos)
      (fun d hd p hp => hgap d hd p (hcellsub j hj hp))
  have heq : ∀ j : ℕ,
      convolutionWuWindows N Δ (Fin.cons (reboxingAlpha q Δ 3 (j+1)) V) =
        Fin.cons (cell N q Δ 3 j) W := by
    intro j
    rw [convolutionWuWindows_cons]
    have hend : reboxingAlpha q Δ 3 (j+1)/Δ = reboxingAlpha q Δ 3 j := by
      rw [reboxingAlpha_step hΔ0,mul_div_cancel_right₀ _ hΔ0.ne']
    rw [hend]
    rfl
  have hcover : InsertedGain.coverTheta N δ Δ V s r ≤ boxTheta N Q (Fin.cons P W) := by
    calc
      _ = ∑ j ∈ InsertedGain.occupiedCells N δ Δ V s r, boxTheta N Q (Fin.cons (cell N q Δ 3 j) W) := by
        unfold InsertedGain.coverTheta
        apply sum_congr rfl
        intro j hj
        rw [heq]
      _ ≤ ∑ j ∈ range (r+2), boxTheta N Q (Fin.cons (cell N q Δ 3 j) W) := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact filter_subset _ _
        · intro j hj _
          exact hcell0 j hj
      _ = _ := by
        rw [theta_grid_exact W hq0 hΔ]
        simp only [reboxingAlpha_zero,Nat.cast_add,Nat.cast_ofNat]
        rfl
  apply hcover.trans
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N/(2*log N)).trans (box_trueLi_lower hN4)
  have hpoint : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ P, wuSingularSeries ((d*p)*N)/((Nat.totient (d*p) : ℝ)*log (Q/((d : ℝ)*p)))) ≤
      C*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d))) := by
    intro d hd
    have hD : 1 < Q/d := (hg d hd).2.2.2.2
    have ha : 0 ≤ wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d)) :=
      div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos (hg d hd).1 (by omega))).le
        (mul_nonneg (Nat.cast_nonneg _) (log_pos hD).le)
    have hatom := inserted_fibre_kernel P (show 0 < N by omega) (hg d hd).1 hD (by
      intro p hp
      have hh := (hf d hd).2.2.1 p (hPall hp)
      have hp2 : 2 < p := by exact_mod_cast (show (2 : ℝ) < p by linarith [hh.1])
      exact ⟨(mem_primeWindow.mp hp).1,hp2,(mem_primeWindow.mp hp).2.1,by linarith [hh.2]⟩)
    exact hatom.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hf d hd).2.2.2 ha)
  change boxTheta N Q (Fin.cons P W) ≤ C*boxTheta N Q W
  rw [boxTheta_cons]
  unfold boxTheta
  rw [mul_left_comm C]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4*logarithmicIntegral N)
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hh := mul_le_mul_of_nonneg_left (hpoint d hd) (Nat.cast_nonneg (convolutionCoeff W d))
  convert hh using 1; ring

end
end CoverMass
