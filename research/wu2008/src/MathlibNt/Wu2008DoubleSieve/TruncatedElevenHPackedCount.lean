import MathlibNt.Wu2008DoubleSieve.SingleUpperHAssembly
import MathlibNt.Wu2008DoubleSieve.TruncatedElevenClassicalCountLower

namespace Wu2008DoubleSieve.TruncatedElevenHPackedCount
open Finset Real SingleUpperCounts SingleUpperClassicalLimit SingleUpperHAssembly
open scoped Classical

/-- All other original payments, including the sixth gain exactly once. -/
noncomputable def otherCoefficient : ℝ :=
  24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
    truncatedSixthLowerF6lin + 47/481250 - 8*J9 -
    16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
    8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11

/-- Reassemble from actual positive and negative producers with U3/U4 still
literal. No previously assembled classical lower bound is subtracted. -/
theorem other_terms_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (otherCoefficient-ε)*truncatedSixthMassScale N -
        (U N (1/3) : ℝ) - (U N truncatedSixthLowerSigma : ℝ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  have heps : 0 < ε/6 := by positivity
  obtain ⟨TP,_,hP⟩ := first_second_fifth_sixth_actual_lower heps
  obtain ⟨T9,hT9,h9⟩ := TruncatedElevenSignedLower.original_ninth_upper heps
  obtain ⟨TS,_,hS⟩ := SeventhEighth.fixed_weighted_switching_epsilon heps
  obtain ⟨TF,_,hF⟩ := TruncatedFourPhysical.original_sums_upper heps
  obtain ⟨TC,_,hC⟩ := SeventhEighth.seventh_eighth_weighted_classical_upper heps
  obtain ⟨TD,_,hD⟩ := FourClassical.physical10_physical11_sum_classical_upper heps
  refine ⟨max TP (max T9 (max TS (max TF (max TC TD)))),
    hT9.trans ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro N hN he
  have hNP := (le_max_left TP (max T9 (max TS (max TF (max TC TD))))).trans hN
  have htail := (le_max_right TP (max T9 (max TS (max TF (max TC TD))))).trans hN
  have hN9 := (le_max_left T9 (max TS (max TF (max TC TD)))).trans htail
  have htail1 := (le_max_right T9 (max TS (max TF (max TC TD)))).trans htail
  have hNS := (le_max_left TS (max TF (max TC TD))).trans htail1
  have htail2 := (le_max_right TS (max TF (max TC TD))).trans htail1
  have hNF := (le_max_left TF (max TC TD)).trans htail2
  have htail3 := (le_max_right TF (max TC TD)).trans htail2
  have hNC := (le_max_left TC TD).trans htail3
  have hND := (le_max_right TC TD).trans htail3
  have hp := hP N hNP he
  have h9' := h9 N hN9 he
  have hs := hS N hNS he
  have hf := hF N hNF he
  have hc := hC N hNC he
  have hd := hD N hND he
  have hz : SeventhEighth.z N = (N : ℝ)^truncatedSixthLowerAlpha := rfl
  have hw : SeventhEighth.w N = (N : ℝ)^truncatedSixthLowerBeta := rfl
  have hu : SeventhEighth.u N = (N : ℝ)^truncatedSixthLowerSigma := rfl
  have hv : SeventhEighth.v N = (N : ℝ)^(1/3 : ℝ) := rfl
  rw [hz,hw,hu,hv] at hs
  push_cast at hs
  dsimp only at hf
  rw [TruncatedElevenSignedLower.fixed_expression_literal]
  unfold otherCoefficient truncatedSixthMassScale
  ring_nf at hp h9' hs hf hc hd ⊢
  linarith only [hp,h9',hs,hf,hc,hd]

/-- Actual finite signed mother consumption of the newly produced H packing. -/
theorem packed_signed_lower {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hε : 0 < ε) (Q : Finset ℝ)
    (hanchor : truncatedSixthLowerAlpha/2 ∈ Q)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      (otherCoefficient-ε)*truncatedSixthMassScale N - packed34 Q N δ η Δ ≤
        (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨TP,hTP,hP⟩ := other_terms_paid (half_pos hε)
  obtain ⟨TU,_,hU⟩ := actual_pair_upper hδ hδhi hη (half_pos hε) Q hanchor hQ
  refine ⟨max TP TU,hTP.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hΔlo hΔhi
  have hp := hP N ((le_max_left _ _).trans hN) he
  have hu := hU N ((le_max_right _ _).trans hN) he Δ hΔlo hΔhi
  linarith only [hp,hu]

/-- A genuine ordinary-P2 finite bound, still containing the coarse H packing.
This is not the unproved limiting integral coefficient. -/
theorem actual_packed_count_lower {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hε : 0 < ε) (Q : Finset ℝ)
    (hanchor : truncatedSixthLowerAlpha/2 ∈ Q)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      (otherCoefficient-ε)*truncatedSixthMassScale N - packed34 Q N δ η Δ ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨TP,hTP,hP⟩ := packed_signed_lower hδ hδhi hη (half_pos hε) Q hanchor hQ
  obtain ⟨TE,_,hE⟩ := TruncatedElevenClassicalCountLower.exceptional_power_error_paid (half_pos hε)
  obtain ⟨TC,_,hC⟩ := TruncatedElevenClassicalCountLower.fixed_cutoff_eventually_admissible
  refine ⟨max TP (max TE TC),hTP.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hΔlo hΔhi
  have hNP := (le_max_left TP (max TE TC)).trans hN
  have htail := (le_max_right TP (max TE TC)).trans hN
  have hNE := (le_max_left TE TC).trans htail
  have hNC := (le_max_right TE TC).trans htail
  have hp := hP N hNP he Δ hΔlo hΔhi
  have he' := hE N hNE
  have hf := truncatedSixth_fixed_le_count
    (by have := hTP.trans hNP; omega : 4 ≤ N) he (hC N hNC)
  unfold truncatedSixthMassScale at hp ⊢
  ring_nf at hp he' ⊢
  linarith only [hp,he',hf]

/-- A fully specified finite coarse family; no grid or source witness is supplied. -/
noncomputable def coarsePoint (δ : ℝ) (n j : ℕ) : ℝ :=
  truncatedSixthLowerAlpha/2 + ((j : ℝ)/(n+1)) *
    (((1/2-δ)/2)-truncatedSixthLowerAlpha/2)

noncomputable def coarseGrid (δ : ℝ) (n : ℕ) : Finset ℝ :=
  (range (n+1)).image (coarsePoint δ n)

theorem coarseGrid_anchor (δ : ℝ) (n : ℕ) :
    truncatedSixthLowerAlpha/2 ∈ coarseGrid δ n := by
  apply mem_image.mpr
  refine ⟨0,mem_range.mpr (Nat.zero_lt_succ n),?_⟩
  simp [coarsePoint]

theorem coarseGrid_bounds {δ : ℝ} (hδhi : δ ≤ 1/100) (n : ℕ) :
    ∀ q ∈ coarseGrid δ n, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2 := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hq
  have hden : (0 : ℝ) < n+1 := by positivity
  have hjr : (j : ℝ) ≤ n+1 := by exact_mod_cast (Nat.le_of_lt (mem_range.mp hj))
  have hratio0 : (0 : ℝ) ≤ (j : ℝ)/(n+1) := by positivity
  have hratio1 : (j : ℝ)/(n+1) ≤ 1 := (div_le_one hden).mpr hjr
  have hwidth : 0 ≤ ((1/2-δ)/2)-truncatedSixthLowerAlpha/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hm0 := mul_nonneg hratio0 hwidth
  have hm1 := mul_le_mul_of_nonneg_right hratio1 hwidth
  unfold coarsePoint
  constructor <;> linarith only [hm0,hm1]

/-- All coarse geometry, the arithmetic Delta, and the source admissibility are
internally produced. The remaining expression is deliberately finite. -/
theorem actual_canonical_count_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) (n : ℕ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (otherCoefficient-ε)*truncatedSixthMassScale N -
        packed34 (coarseGrid δ n) N δ ε (1+log (N : ℝ)^(-4 : ℝ)) ≤
        4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T,hT,h⟩ := actual_packed_count_lower hδ hδhi hε hε
    (coarseGrid δ n) (coarseGrid_anchor δ n) (coarseGrid_bounds hδhi n)
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hN4 : 4 ≤ N := by have := hT.trans hN; omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpower : 0 < log (N : ℝ)^(-4 : ℝ) := rpow_pos_of_pos hlog _
  exact h N hN he _ le_rfl (by linarith)

end Wu2008DoubleSieve.TruncatedElevenHPackedCount
