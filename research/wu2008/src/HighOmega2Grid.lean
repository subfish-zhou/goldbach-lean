import HighOmega2Actual
import MathlibNt.Wu2008DoubleSieve.ReboxingParameter

namespace HighOmega2
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- The original source grid; no new real cut points are introduced. -/
def cell (N : ℕ) (q Δ t : ℝ) (j : ℕ) : Finset ℕ :=
  primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j+1))

/-- Every original prime lies in the source grid through r+2. The two extra
cells are forced by the Fin 2 product width and s≥2, not a chosen mesh. -/
theorem complete_cover {N r : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 0 < N) (hΔ : 1 < Δ) (hV : ∀ j, 0 < V j)
    (hs : 2 ≤ s) (hst : s ≤ t)
    (hr : ((N : ℝ)^(1/2-δ)/(∏ j, V j))^(1/s) <
      reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ j, V j)) Δ t (r+1)) :
    ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∃! j : ℕ, j < r+2 ∧ p ∈ cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t j := by
  let q := (N : ℝ)^(1/2-δ)/(∏ j, V j)
  have hQ : 0 < (N : ℝ)^(1/2-δ) := rpow_pos_of_pos (by exact_mod_cast hN) _
  have hq : 0 < q := div_pos hQ (prod_pos (fun j _ => hV j))
  have hΔ0 : 0 < Δ := by linarith
  intro d hd p hp
  obtain ⟨hpp,hpc,hplo,hphi⟩ := mem_primeWindow.mp hp
  have hlo := (reboxing_support_cutoff_bounds hQ.le hΔ0 hV (show 0 < t by linarith) hd).1
  have hhi := (reboxing_support_cutoff_bounds hQ.le hΔ0 hV (show 0 < s by linarith) hd).2
  have hwidth : Δ^((2 : ℝ)/s) ≤ Δ := by
    calc
      _ ≤ Δ^(1 : ℝ) := rpow_le_rpow_of_exponent_le hΔ.le ((div_le_one (by linarith)).mpr hs)
      _ = _ := rpow_one _
  have hupper : (p : ℝ) < reboxingAlpha q Δ t (r+2) := by
    calc
      _ < q^(1/s)*Δ^((2 : ℝ)/s) := hphi.trans_le hhi
      _ ≤ q^(1/s)*Δ := mul_le_mul_of_nonneg_left hwidth (rpow_nonneg hq.le _)
      _ < reboxingAlpha q Δ t (r+1)*Δ := mul_lt_mul_of_pos_right hr hΔ0
      _ = _ := by
        rw [← reboxingAlpha_step hΔ0]
        congr 1
        ring
  obtain ⟨j,hj,huniq⟩ := (reboxingAlpha_partition hq hΔ (r+2)).mp
    ⟨by simpa only [reboxingAlpha_zero] using hlo.trans hplo,
      by simpa only [Nat.cast_add,Nat.cast_ofNat] using hupper⟩
  refine ⟨j,⟨hj.1,mem_primeWindow.mpr ⟨hpp,hpc,hj.2.1,hj.2.2⟩⟩,?_⟩
  intro k hk
  have hk' := mem_primeWindow.mp hk.2
  exact huniq k ⟨hk.1,hk'.2.2.1,hk'.2.2.2⟩

/-- Exact signed partition for an already constructed finite unique cover. -/
private theorem sum_unique_cells {r : ℕ} (S : Finset ℕ) (P : ℕ → Finset ℕ)
    (h : ∀ p ∈ S, ∃! j : ℕ, j < r ∧ p ∈ P j) (f : ℕ → ℝ) :
    ∑ p ∈ S, f p = ∑ j ∈ range r, ∑ p ∈ S ∩ P j, f p := by
  have hp : ∀ p ∈ S, f p = ∑ j ∈ range r, if p ∈ P j then f p else 0 := by
    intro p hp
    obtain ⟨j,hj,hu⟩ := h p hp
    rw [sum_eq_single j]
    · simp [hj.2]
    · intro k hk hkj
      have hn : p ∉ P k := by
        intro hpk
        exact hkj (hu k ⟨mem_range.mp hk,hpk⟩)
      simp [hn]
    · intro hn
      exact False.elim (hn (mem_range.mpr hj.1))
  calc
    _ = ∑ p ∈ S, ∑ j ∈ range r, if p ∈ P j then f p else 0 := sum_congr rfl hp
    _ = ∑ j ∈ range r, ∑ p ∈ S, if p ∈ P j then f p else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      congr 1

/-- The complete actual Omega2, with every selected modulus and every
repeated prime label, equals the full grid of clipped fibres. -/
theorem omega2_grid_exact {N r : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 0 < N) (hΔ : 1 < Δ) (hV : ∀ j, 0 < V j)
    (hs : 2 ≤ s) (hst : s ≤ t)
    (hr : ((N : ℝ)^(1/2-δ)/(∏ j, V j))^(1/s) <
      reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ j, V j)) Δ t (r+1)) :
    let W := convolutionWuWindows N Δ V
    let q := (N : ℝ)^(1/2-δ)/(∏ j, V j)
    wuOmega2Sum N δ s t W =
      ∑ j ∈ range (r+2), ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∩ cell N q Δ t j,
          (sourceSieveCount N (d*p) ((d*p)*N) (wuLocalCutoff N δ d t) : ℝ) := by
  dsimp
  unfold wuOmega2Sum wuOmega2
  have hc := complete_cover hN hΔ hV hs hst hr
  calc
    _ = ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ∑ j ∈ range (r+2), ∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∩
          cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t j,
          (sourceSieveCount N (d*p) ((d*p)*N) (wuLocalCutoff N δ d t) : ℝ) := by
      apply sum_congr rfl
      intro d hd
      congr 1
      rw [← sum_unique_cells _ _ (hc d hd)]
      apply sum_congr rfl
      intro p hp
      rw [omega2_source_count_prime_modulus_eq N d (mem_primeWindow.mp hp).1 (mem_primeWindow.mp hp).2.2.1]
    _ = _ := by
      simp only [mul_sum]
      exact sum_comm

/-- Every nonempty clipped cell is an actual insertion, not an assumed
admissible one. The whole rectangle can therefore use the parent geometry. -/
theorem occupied_cell {N d p j : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hΔ : 1 < Δ) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) ∩
      cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t j) :
    ActualInsertion N δ Δ (reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t (j+1)) V := by
  obtain ⟨v,hv,heq⟩ := mem_image.mp hd
  have hp0 := (mem_inter.mp hp).1
  have hp1 := (mem_inter.mp hp).2
  refine ⟨v,p,s,t,Fintype.mem_piFinset.mp hv,hs,hst,ht,?_,?_⟩
  · simpa only [heq] using hp0
  · have hend : reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t (j+1) / Δ =
        reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t j := by
      rw [reboxingAlpha_step (show 0 < Δ by linarith),mul_div_cancel_right₀ _ (by linarith : Δ ≠ 0)]
    simpa only [hend,cell,Nat.cast_add,Nat.cast_one] using hp1

/-- Partitioning all cells aggregates their actual Theta exactly. There is
no factor equal to the number of cells in the error mass. -/
theorem theta_grid_exact {N r : ℕ} {Q q Δ t : ℝ} {i : ℕ}
    (W : Fin i → Finset ℕ) (hq : 0 < q) (hΔ : 1 < Δ) :
    (∑ j ∈ range r, boxTheta N Q (Fin.cons (cell N q Δ t j) W)) =
      boxTheta N Q (Fin.cons (primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)) W) := by
  simp_rw [boxTheta_cons]
  rw [← mul_sum]
  congr 1
  exact (reboxingAlpha_convolution_sum_partition hq hΔ N r W
    (fun d p => wuSingularSeries ((d*p)*N)/((Nat.totient (d*p) : ℝ)*log (Q/((d : ℝ)*p))))).symm

end
end HighOmega2
