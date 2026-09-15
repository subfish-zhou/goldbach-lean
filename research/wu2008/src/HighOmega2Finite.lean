import HighOmega2Theta

namespace HighOmega2
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

theorem cell_as_window (N j : ℕ) (q Δ t : ℝ) (hΔ : 0 < Δ) :
    cell N q Δ t j = primeWindow N (reboxingAlpha q Δ t (j+1)/Δ) (reboxingAlpha q Δ t (j+1)) := by
  simp only [cell,reboxingAlpha_step hΔ,mul_div_cancel_right₀ _ hΔ.ne']

/-- Every inner cell has the actual total-product geometry, including empty
cells, without putting occupancy into the theorem's inputs. -/
theorem interior_geometry {N r j : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδhi : δ ≤ 50*highEta) (hΔ : 1 < Δ) (hΔhi : Δ ≤ (N : ℝ)^highEta)
    (hV : ∀ l, (N : ℝ)^(100/1327 : ℝ) ≤ V l) (hrect : OriginalRectangles N V)
    (hs : 2 ≤ s) (ht : 3 ≤ t) (hst : s ≤ t) (ht5 : t ≤ 5)
    (hj : 1 ≤ j) (hjr : j < r)
    (hr : reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t r ≤
      ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s)) :
    ∀ m ∈ boxConvolutionSupport (Fin.cons (cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t j)
      (convolutionWuWindows N Δ V)), (m : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
  let q := (N : ℝ)^(1/2-δ)/(∏ l, V l)
  have hVp : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos
    (by exact_mod_cast (show 0 < N by omega)) _).trans_le (hV l)
  intro m hm
  obtain ⟨v,hv,hvm⟩ := mem_image.mp hm
  have hv' := Fintype.mem_piFinset.mp hv
  let d : ℕ := ∏ l : Fin 2, v l.succ
  have hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) :=
    mem_image.mpr ⟨fun l => v l.succ,Fintype.mem_piFinset.mpr (fun l => hv' l.succ),rfl⟩
  have hp : v 0 ∈ cell N q Δ t j := hv' 0
  have hwin := interior_window (show 0 < N by omega) hΔ hVp hs ht hj hjr hr d hd hp
  have hoc := occupied_cell hΔ hs hst (show t ≤ 10 by linarith) hd (mem_inter.mpr ⟨hwin,hp⟩)
  have hg := inserted_box_geometry hN hδhi hΔ.le hΔhi hV hrect hoc
  have hbox : convolutionWuWindows N Δ (Fin.cons (reboxingAlpha q Δ t (j+1)) V) =
      Fin.cons (cell N q Δ t j) (convolutionWuWindows N Δ V) := by
    rw [convolutionWuWindows_cons,← cell_as_window N j q Δ t (by linarith)]
  apply hg.2
  rw [hbox]
  exact mem_image.mpr ⟨v,hv,hvm⟩

/-- All internal inserted Phi counts contribute once, with their actual
cutoff, to the original Omega2. Neither a cover nor inside assumptions remain. -/
theorem interior_phi_lower {N r : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 0 < N) (hΔ : 1 < Δ) (hV : ∀ l, 0 < V l)
    (hq : 1 < (N : ℝ)^(1/2-δ)/(∏ l, V l))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) (hcondition : 2 ≤ t-t/s)
    (hr : reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t r ≤
      ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s))
    (hrhi : ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s) <
      reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ t (r+1)) :
    let q := (N : ℝ)^(1/2-δ)/(∏ l, V l)
    let W := convolutionWuWindows N Δ V
    (∑ j ∈ Ico 1 r, wuBoxPhi N δ (Fin.cons (cell N q Δ t j) W) (lowerParameter q Δ t j)) ≤
      wuOmega2Sum N δ s t W := by
  dsimp
  rw [omega2_grid_exact hN hΔ hV hs hst hrhi]
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg
    (show Ico 1 r ⊆ range (r+2) by intro j hj; simp only [mem_Ico,mem_range] at *; omega)
    (fun j _ _ => sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun p _ => by
      unfold sourceSieveCount
      positivity)))))
  apply sum_le_sum
  intro j hj
  obtain ⟨hj1,hjr⟩ := mem_Ico.mp hj
  have hu := lowerParameter_domain hq hΔ hs ht ht5 hcondition hjr hr
  rw [wuBoxPhi_cons]
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hin := interior_window hN hΔ hV hs ht hj1 hjr hr d hd
  rw [inter_eq_right.mpr hin]
  apply sum_le_sum
  intro p hp
  have hQ : 0 < (N : ℝ)^(1/2-δ) := rpow_pos_of_pos (by exact_mod_cast hN) _
  have hqD := (reboxing_support_level_bounds hQ.le (show 0 < Δ by linarith) hV hd).1
  have hcut := lowerParameter_cutoff hq hqD ht (show 0 < lowerParameter _ _ _ j by linarith [hu.1]) hp
  exact_mod_cast sourceSieveCount_antitone N (d*p) ((d*p)*N) hcut

/-- Actual AP errors are additive over the original disjoint source cells;
this is a single large prime convolution error, not r fixed error budgets. -/
theorem ap_grid_exact {N Q r : ℕ} {q Δ t : ℝ} {i : ℕ}
    (W : Fin i → Finset ℕ) (hq : 0 < q) (hΔ : 1 < Δ) :
    (∑ j ∈ range r, convolutionAPError N Q (Fin.cons (cell N q Δ t j) W)) =
      convolutionAPError N Q (Fin.cons (primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)) W) := by
  let F : ℕ → ℝ := fun d =>
    ∑ q ∈ (Icc 1 (Q / d)).filter (fun q => q.Coprime (d * N)),
      |AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.primeAPError N (d * q) N|
  have expand (P : Finset ℕ) : convolutionAPError N Q (Fin.cons P W) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ P, F (d * p) := by
    rw [convolutionAPError_eq_support_sum]
    exact boxConvolution_sum_cons P W F
  simp_rw [expand]
  exact (reboxingAlpha_convolution_sum_partition hq hΔ N r W (fun d p => F (d*p))).symm

/-- Nonnegative AP kernel permits removing cell zero only *after* the
complete absolute error is formed. Signed Rosser residuals are not restricted. -/
theorem ap_interior_le {N Q r : ℕ} {q Δ t : ℝ} {i : ℕ}
    (W : Fin i → Finset ℕ) (hq : 0 < q) (hΔ : 1 < Δ) :
    (∑ j ∈ Ico 1 r, convolutionAPError N Q (Fin.cons (cell N q Δ t j) W)) ≤
      convolutionAPError N Q (Fin.cons (primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)) W) := by
  rw [← ap_grid_exact W hq hΔ]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact mem_range.mpr (mem_Ico.mp hj).2
  · intro j _ _
    unfold convolutionAPError
    exact sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => abs_nonneg _)))

end
end HighOmega2
