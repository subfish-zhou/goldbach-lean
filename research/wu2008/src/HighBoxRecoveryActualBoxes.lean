import HighBoxRecoveryInsertionGeometry

namespace HighBoxRecovery
open Finset Real Wu2008DoubleSieve
open scoped Classical
noncomputable section

/-- The original two rectangles, with the unaltered alpha and beta. -/
def OriginalRectangles (N : ℕ) (V : Fin 2 → ℝ) : Prop :=
  (V 0 ≤ (N : ℝ)^(25/206 : ℝ) ∧ V 1 ≤ (N : ℝ)^(1/2-2*(25/206 : ℝ))) ∨
  (V 0 ≤ (N : ℝ)^(3*(100/1327 : ℝ)/2) ∧ V 1 ≤ (N : ℝ)^(1/2-3*(100/1327 : ℝ)))

/-- Occupancy by a real original tuple and a real Buchstab inserted prime.
No claim about a balanced profile is among these fields. -/
def ActualInsertion (N : ℕ) (δ Δ U : ℝ) (V : Fin 2 → ℝ) : Prop :=
  ∃ (v : Fin 2 → ℕ) (p : ℕ) (a b : ℝ),
    (∀ j, v j ∈ convolutionWuWindows N Δ V j) ∧
    2 ≤ a ∧ a ≤ b ∧ b ≤ 10 ∧
    p ∈ primeWindow N (wuLocalCutoff N δ (∏ j, v j) b)
      (wuLocalCutoff N δ (∏ j, v j) a) ∧
    p ∈ primeWindow N (U/Δ) U

/-- Shrinking a literal prime window costs one auxiliary exponent, uniformly. -/
theorem window_prime_lower {N p : ℕ} {Δ U : ℝ}
    (hN : 2 ≤ N) (hΔ : 1 ≤ Δ) (hΔhi : Δ ≤ (N : ℝ)^highEta)
    (hU : (N : ℝ)^(2*highEta) ≤ U) (hp : p ∈ primeWindow N (U/Δ) U) :
    p.Prime ∧ (N : ℝ)^highEta ≤ p := by
  refine ⟨(mem_primeWindow.mp hp).1, ?_⟩
  apply le_trans _ (mem_primeWindow.mp hp).2.2.1
  apply (le_div_iff₀ (show 0 < Δ by linarith)).mpr
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (N : ℝ)^highEta * (N : ℝ)^highEta := mul_le_mul_of_nonneg_left hΔhi (by positivity)
    _ = (N : ℝ)^(2*highEta) := by rw [← rpow_add hNr]; congr 1; ring
    _ ≤ U := hU

/-- Original high two-prime boxes meet the actual input of the R1/R2 producer. -/
theorem original_box_geometry {N : ℕ} {δ Δ : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδhi : δ ≤ 50*highEta)
    (hΔ : 1 ≤ Δ) (hΔhi : Δ ≤ (N : ℝ)^highEta)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hrect : OriginalRectangles N V) :
    (∀ j p, p ∈ convolutionWuWindows N Δ V j → p.Prime ∧ (N : ℝ)^highEta ≤ p) ∧
    (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hV0 : ∀ j, 0 ≤ V j := fun j => (rpow_nonneg (Nat.cast_nonneg N) _).trans (hV j)
  have hbase := original_rectangles_product hN hV0 hrect
  refine ⟨?_, ?_⟩
  · intro j p hp
    apply window_prime_lower hN hΔ hΔhi _ hp
    exact (rpow_le_rpow_of_exponent_le hN1 (by norm_num [highEta])).trans (hV j)
  · intro d hd
    apply (boxConvolutionSupport_le_product
      (fun j p hp => (mem_convolutionWuWindows.mp hp).2.2.2.le) hd).trans
    apply hbase.trans
    exact rpow_le_rpow_of_exponent_le hN1 (by
      have hηpos : 0 < highEta := by norm_num [highEta]
      linarith)

/-- Every occupied insertion box, not only a safe rectangular subinterval,
satisfies the full three-prime producer geometry. The original d-dependent
insertion interval is used literally and its complete Delta^4 loss is paid. -/
theorem inserted_box_geometry {N : ℕ} {δ Δ U : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδhi : δ ≤ 50*highEta)
    (hΔ : 1 ≤ Δ) (hΔhi : Δ ≤ (N : ℝ)^highEta)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hrect : OriginalRectangles N V)
    (hw : ActualInsertion N δ Δ U V) :
    (∀ j p, p ∈ convolutionWuWindows N Δ (Fin.cons U V) j →
      p.Prime ∧ (N : ℝ)^highEta ≤ p) ∧
    (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ (Fin.cons U V)),
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) := by
  obtain ⟨v,p,a,b,hv,ha,hab,hb,hp,hpU⟩ := hw
  let d : ℕ := ∏ j, v j
  let D : ℝ := ∏ j, V j
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hηpos : 0 < highEta := by norm_num [highEta]
  have hΔpos : 0 < Δ := by linarith
  have hVpos : ∀ j, 0 < V j := fun j => (rpow_pos_of_pos hNr _).trans_le (hV j)
  have hDpos : 0 < D := prod_pos (fun j _ => hVpos j)
  have hdpos : 0 < d := prod_pos (fun j _ => (mem_convolutionWuWindows.mp (hv j)).1.pos)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdD : (d : ℝ) ≤ D := by
    dsimp [d,D]
    push_cast
    exact prod_le_prod (fun j _ => Nat.cast_nonneg _) (fun j _ => (mem_convolutionWuWindows.mp (hv j)).2.2.2.le)
  have hbase : D ≤ (N : ℝ)^(1/2-100*highEta) :=
    original_rectangles_product hN (fun j => (hVpos j).le) hrect
  have hdsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*(5*highEta)) :=
    hdD.trans (hbase.trans (rpow_le_rpow_of_exponent_le hN1 (by linarith)))
  have hcut := cutoff_lower hN hdpos (show 0 < 5*highEta by positivity)
    (show 0 < b by linarith) hb hdsize
  have hpLow : (N : ℝ)^(5*highEta) ≤ p := hcut.trans (mem_primeWindow.mp hp).2.2.1
  have hULow : (N : ℝ)^(2*highEta) ≤ U :=
    (rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans
      (hpLow.trans (mem_primeWindow.mp hpU).2.2.2.le)
  have hR : 1 ≤ (N : ℝ)^(1/2-δ)/d := by
    apply (le_div_iff₀ hdr).mpr
    simp only [one_mul]
    exact hdD.trans (hbase.trans (rpow_le_rpow_of_exponent_le hN1 (by linarith)))
  have hInsert := inserted_prime_square hdpos hR ha (mem_primeWindow.mp hp).2.2.2.le
  have hlabel : D ≤ Δ^2*d := by
    have hvBound : ∀ j, V j ≤ Δ*(v j : ℝ) := by
      intro j
      have h := (div_le_iff₀ hΔpos).mp (mem_convolutionWuWindows.mp (hv j)).2.2.1
      simpa only [mul_comm] using h
    have hm := mul_le_mul (hvBound 0) (hvBound 1) (hVpos 1).le
      (mul_nonneg hΔpos.le (Nat.cast_nonneg (v 0)))
    dsimp [D,d]
    simp only [Fin.prod_univ_two, Nat.cast_mul]
    nlinarith
  have hUbox : U ≤ Δ*(p : ℝ) := by
    have h := (div_le_iff₀ hΔpos).mp (mem_primeWindow.mp hpU).2.2.1
    simpa only [mul_comm] using h
  have hprod := occupied_insertion_product hN hδhi hDpos
    ((rpow_nonneg hNr.le _).trans hULow) hΔ hΔhi hbase hlabel hInsert hUbox
  have hnewprod : (∏ j, Fin.cons U V j) ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
    simpa only [D, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_comm] using hprod
  refine ⟨?_, ?_⟩
  · intro j q hq
    apply window_prime_lower hN hΔ hΔhi _ hq
    refine Fin.cases hULow (fun j => ?_) j
    exact (rpow_le_rpow_of_exponent_le hN1 (by norm_num [highEta])).trans (hV j)
  · intro e he
    exact (boxConvolutionSupport_le_product
      (fun j q hq => (mem_convolutionWuWindows.mp hq).2.2.2.le) he).trans hnewprod

end
end HighBoxRecovery
