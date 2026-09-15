import PositiveHStrict
import Wu08G6HighCount

namespace HighConsumer
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- Closed endpoints are paid before the physical sieve count is used. -/
theorem original_closed_lower {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      (log (s-1)+(1/10000)*log (2/(s-1))-ε)*
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s := by
  obtain ⟨T1,_,h1⟩ := PositiveH.original_lower hδ hδhi (half_pos hε)
  obtain ⟨T2,_,h2⟩ := original_and_inserted_phi_endpoint hδ hδhi (half_pos hε)
  refine ⟨max 512 (max T1 T2),le_max_left _ _,?_⟩
  intro N hN he Δ hlo hhi V hV hr s hs hsmax
  obtain ⟨hθ,hp⟩ := h1 N (by omega) he Δ hlo hhi V hV hr s hs hsmax
  have hend := (h2 N (by omega) he Δ hlo hhi V hV hr s (by linarith) (by linarith)).1
  refine ⟨hθ,?_⟩
  dsimp [PhiEndpointPaid] at hend
  nlinarith only [hp,hend.2]

/-- The source argument differs from the original argument by fixed delta/alpha. -/
theorem source_parameter_exact (δ x y : ℝ) :
    truncatedSixthLowerS δ x y = QuarterTrim.u x y - δ/QuarterTrim.alpha := by
  unfold truncatedSixthLowerS truncatedSixthLowerC QuarterTrim.u
  change (1/2-δ-x-y)/QuarterTrim.alpha = _
  ring

/-- On the original high triangle no auxiliary division by x is introduced. -/
theorem high_source_bounds {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hr : truncatedSixthLowerRegion δ x y) (hy : 1/4 < y) :
    2 ≤ truncatedSixthLowerS δ x y ∧ truncatedSixthLowerS δ x y ≤ 29/10 := by
  refine ⟨(truncatedSixthLower_region_bounds hδ hr).2.2.2.1,?_⟩
  apply (div_le_iff₀ truncatedSixthLower_parameters.1).mpr
  have hx := hr.1
  norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerC] at hx ⊢
  linarith

/-- High sixth boxes satisfy the original second rectangle, not the old U_k ceiling. -/
theorem high_original_rectangles {N : ℕ} {δ x y : ℝ}
    (hN : 1 < N) (hδ : 0 ≤ δ)
    (hr : truncatedSixthLowerRegion δ x y) (hy : 1/4 < y) :
    OriginalRectangles N ![(N : ℝ)^x,(N : ℝ)^y] := by
  apply Or.inr
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  constructor
  · apply rpow_le_rpow_of_exponent_le hNR
    have hx := hr.2.2.2.2
    norm_num [truncatedSixthLowerC,truncatedSixthLowerAlpha] at hx ⊢
    linarith
  · exact rpow_le_rpow_of_exponent_le hNR hr.2.2.2.1

/-- Actual closed Phi followed by the literal original sixth sieve summand. -/
theorem high_box_count {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ x y : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      truncatedSixthLowerRegion δ x y → 1/4 < y →
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^x/Δ →
      (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^y/Δ →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 → s ≤ truncatedSixthLowerS δ x y →
      (log (s-1)+(1/10000)*log (2/(s-1))-ε)*
        boxTheta N ((N : ℝ)^(1/2-δ))
          (convolutionWuWindows N Δ ![(N : ℝ)^x,(N : ℝ)^y]) ≤
      ∑ b ∈ truncatedSixthLowerBoxPairs N Δ x y,
        (sieveCount N (b.1*b.2) N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨T,hT,hbound⟩ := original_closed_lower hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN he Δ x y hlo hhi hr hy hplo hqlo s hs hsmax hsource
  have hN1 : 1 < N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1.le
  have hV : ∀ j : Fin 2, (N : ℝ)^(100/1327 : ℝ) ≤ ![(N : ℝ)^x,(N : ℝ)^y] j := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact rpow_le_rpow_of_exponent_le hNR hr.1
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact rpow_le_rpow_of_exponent_le hNR
        (truncatedSixthLower_parameters.2.1.le.trans hr.2.2.1)
  have hc := (hbound N hN he Δ hlo hhi _ hV
    (high_original_rectangles hN1 hδ.le hr hy) s hs hsmax).2
  have hswap : s ≤ truncatedSixthLowerS δ y x := by
    convert hsource using 1
    unfold truncatedSixthLowerS
    congr 1
    ring
  have hphys := truncatedSixthLower_box_phi_le hN1 (show 0 < s by linarith) hqlo hplo hswap
  exact hc.trans ((wuBoxPhiLE_le_strict N δ _ s).trans hphys)

end
end HighConsumer
