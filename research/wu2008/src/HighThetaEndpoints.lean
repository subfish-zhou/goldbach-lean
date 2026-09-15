import HighBoxRecoveryRelative

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- Endpoint bounds come from the literal original rectangles. -/
theorem original_endpoints {N : ℕ} {V : Fin 2 → ℝ} (hN : 2 ≤ N)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hrect : OriginalRectangles N V) :
    (∀ j, (N : ℝ)^highEta ≤ V j) ∧ (∀ j, V j ≤ N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  refine ⟨fun j => (rpow_le_rpow_of_exponent_le hN1 (by norm_num [highEta])).trans (hV j), ?_⟩
  have hpow : ∀ a : ℝ, a ≤ 1 → (N : ℝ)^a ≤ N := by
    intro a ha
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1 ha
  rcases hrect with h | h
  · intro j
    refine Fin.cases (h.1.trans (hpow _ (by norm_num))) (fun j => ?_) j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact h.2.trans (hpow _ (by norm_num))
  · intro j
    refine Fin.cases (h.1.trans (hpow _ (by norm_num))) (fun j => ?_) j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact h.2.trans (hpow _ (by norm_num))

/-- Occupied U inherits both bounds. Its upper bound is derived from the
actual quadratic cutoff, not postulated as a new input. -/
theorem inserted_endpoint {N : ℕ} {δ Δ U : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta)
    (hΔ : 1 ≤ Δ) (hΔhi : Δ ≤ (N : ℝ)^highEta)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hrect : OriginalRectangles N V)
    (hw : ActualInsertion N δ Δ U V) : (N : ℝ)^highEta ≤ U ∧ U ≤ N := by
  obtain ⟨v,p,a,b,hv,ha,hab,hb,hp,hpU⟩ := hw
  let d : ℕ := ∏ j, v j
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hη : 0 < highEta := by norm_num [highEta]
  have hΔpos : 0 < Δ := by linarith
  have hdpos : 0 < d := prod_pos (fun j _ => (mem_convolutionWuWindows.mp (hv j)).1.pos)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hdD : (d : ℝ) ≤ ∏ j, V j := by
    dsimp [d]
    push_cast
    exact prod_le_prod (fun j _ => Nat.cast_nonneg _) (fun j _ => (mem_convolutionWuWindows.mp (hv j)).2.2.2.le)
  have hbase := original_rectangles_product hN
    (fun j => (rpow_nonneg (Nat.cast_nonneg N) _).trans (hV j)) hrect
  have hdsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*(5*highEta)) :=
    hdD.trans (hbase.trans (rpow_le_rpow_of_exponent_le hN1 (by linarith)))
  have hcut := cutoff_lower hN hdpos (show 0 < 5*highEta by positivity)
    (show 0 < b by linarith) hb hdsize
  have hpLow : (N : ℝ)^(5*highEta) ≤ p := hcut.trans (mem_primeWindow.mp hp).2.2.1
  refine ⟨(rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans
    (hpLow.trans (mem_primeWindow.mp hpU).2.2.2.le), ?_⟩
  have hR : 1 ≤ (N : ℝ)^(1/2-δ)/d := by
    apply (le_div_iff₀ hdr).mpr
    simp only [one_mul]
    exact hdD.trans (hbase.trans (rpow_le_rpow_of_exponent_le hN1 (by linarith)))
  have hsquare := inserted_prime_square hdpos hR ha (mem_primeWindow.mp hp).2.2.2.le
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primeWindow.mp hp).1.one_le
  have hpQ : (p : ℝ) ≤ (N : ℝ)^(1/2-δ) := by
    have hsq : (p : ℝ)^2 ≤ (d : ℝ)*(p : ℝ)^2 := le_mul_of_one_le_left (sq_nonneg _) hd1
    nlinarith
  have hUbox : U ≤ Δ*(p : ℝ) := by
    have h := (div_le_iff₀ hΔpos).mp (mem_primeWindow.mp hpU).2.2.1
    simpa only [mul_comm] using h
  calc
    U ≤ Δ*(p : ℝ) := hUbox
    _ ≤ (N : ℝ)^highEta * (N : ℝ)^(1/2-δ) :=
      mul_le_mul hΔhi hpQ (Nat.cast_nonneg _) (by positivity)
    _ = (N : ℝ)^(highEta+(1/2-δ)) := (rpow_add hNr _ _).symm
    _ ≤ N := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1
        (show highEta+(1/2-δ) ≤ 1 by norm_num [highEta] at *; linarith)

/-- The complete inserted endpoint vector meets the true-Theta mass theorem. -/
theorem inserted_endpoints {N : ℕ} {δ Δ U : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta)
    (hΔ : 1 ≤ Δ) (hΔhi : Δ ≤ (N : ℝ)^highEta)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hrect : OriginalRectangles N V)
    (hw : ActualInsertion N δ Δ U V) :
    (∀ j : Fin 3, (N : ℝ)^highEta ≤ (Fin.cons U V : Fin 3 → ℝ) j) ∧
      (∀ j : Fin 3, (Fin.cons U V : Fin 3 → ℝ) j ≤ (N : ℝ)) := by
  have ho := original_endpoints hN hV hrect
  have hu := inserted_endpoint hN hδ hδhi hΔ hΔhi hV hrect hw
  exact ⟨fun j => Fin.cases hu.1 ho.1 j, fun j => Fin.cases hu.2 ho.2 j⟩

end
end HighTheta
