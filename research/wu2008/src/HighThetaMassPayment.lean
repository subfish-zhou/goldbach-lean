import HighThetaXBoundary

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- Generic absolute power/log payment on actual boxes of depth at most three.
Actual support is still required; this is not an all-depth insertion closure. -/
theorem power_log_relative (m : ℕ) {δ η ε C ρ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, i ≤ 3 → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin i → ℝ, (∀ j, (N : ℝ)^η ≤ V j) → (∀ j, V j ≤ N) →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      C*N*log N^m/(N : ℝ)^ρ ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let c : ℝ := 2*liuUniversalProduct*(1/12 : ℝ)^3
  have hc : 0 < c := by dsimp [c]; have := liuUniversalProduct_pos; positivity
  obtain ⟨T1,hmass⟩ := wu_boxConvolution_mass_bounds 3 hη
  obtain ⟨T2,hbudget⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget (m+17) (show 0 < C/(ε*c) by positivity) hρ)
  refine ⟨max 4 (max T1 T2),le_max_left _ _,?_⟩
  intro N hN i hi Δ hlo hhi V hV hVN hW hsize
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have htheta : c*N/log N^17 ≤ boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    have hm := (hmass N hN1 i hi Δ hlo hhi V hV hVN).1
    have hprod := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 2*liuUniversalProduct*N/log N^2 by have := liuUniversalProduct_pos; positivity)
    have ht := theta_from_actual_support _ hN4 hδ hη hW hsize
    calc
      _ = 2*liuUniversalProduct*N/log N^2 * ((1/12 : ℝ)^3/log N^(5*3)) := by dsimp [c]; ring
      _ ≤ _ := hprod.trans ht
  calc
    _ ≤ C*N*log N^m/((C/(ε*c))*log N^(m+17)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (hbudget N hN2)
    _ = ε*(c*N/log N^17) := by rw [pow_add]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

/-- Paid strict/closed X difference. All label and endpoint hypotheses are
proved by the actual geometry in the original/insertion terminal below. -/
theorem X_boundary_relative {δ η ε : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, i ≤ 3 → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin i → ℝ, (∀ j, (N : ℝ)^η ≤ V j) → (∀ j, V j ≤ N) →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j → p.Prime ∧ (N : ℝ)^η ≤ p) →
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let W := convolutionWuWindows N Δ V
      0 ≤ omega3SieveX N δ s t W-strictX N δ s t W ∧
      omega3SieveX N δ s t W-strictX N δ s t W ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  let F : ℝ := (max 1 (1/η))^(3+2)
  let C : ℝ := (1/log 2+1)*F
  have hC : 0 < C := by dsimp [C,F]; positivity
  obtain ⟨T1,hT14,hpay⟩ := power_log_relative 1 hδ hη hε hC hη
  obtain ⟨T2,hlogBudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN i hi Δ hlo hhi V hV hVN hW hsize s t hs hst ht W
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 1 ≤ log (N : ℝ) := hlogBudget N hN2
  have hpf : (N.primeFactors.card : ℝ) ≤ log N/log 2 :=
    (le_div_iff₀ (log_pos (by norm_num : (1 : ℝ)<2))).mpr
      (primeFactors_card_mul_log_two_le N (by omega))
  have hcoef : (N.primeFactors.card : ℝ)+1 ≤ (1/log 2+1)*log N := by
    calc
      _ ≤ log N/log 2+log N := by linarith
      _ = _ := by ring
  have hb := X_boundary_power (s := s) W hi (show 2 ≤ N by omega) hη hW hsize
    (show 0 < t by linarith) ht
  refine ⟨hb.1,?_⟩
  calc
    _ ≤ ((N.primeFactors.card : ℝ)+1)*F*(N : ℝ)^(1-η) := hb.2
    _ ≤ ((1/log 2+1)*log N)*F*(N : ℝ)^(1-η) := by gcongr
    _ = C*N*log N^1/(N : ℝ)^η := by
      rw [rpow_sub hNr, rpow_one]
      dsimp [C]
      ring
    _ ≤ _ := hpay N hN1 i hi Δ hlo hhi V hV hVN (fun j p hp => (hW j p hp).1) hsize

/-- True prime-count main masses, not li surrogates. -/
def XBoundaryPaid {i : ℕ} (N : ℕ) (δ ε s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  0 ≤ omega3SieveX N δ s t W-strictX N δ s t W ∧
    omega3SieveX N δ s t W-strictX N δ s t W ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) W

/-- Every actually occupied insertion shares the original mass threshold. -/
theorem original_and_inserted_X_boundary {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        XBoundaryPaid N δ ε s t (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          XBoundaryPaid N δ ε s t (convolutionWuWindows N Δ (Fin.cons U V)) := by
  obtain ⟨T1,hT14,hpay⟩ := X_boundary_relative hδ.le (show 0 < highEta by norm_num [highEta]) hε
  obtain ⟨T2,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have he := original_endpoints (show 2 ≤ N by omega) hV hrect
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hpay N hN1 2 (by norm_num) Δ hlo hhi V he.1 he.2 hg.1 hg.2 s t hs hst ht, ?_⟩
  intro U hw
  have hie := inserted_endpoints (show 2 ≤ N by omega) hδ.le hδhi hΔ hΔhi hV hrect hw
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hpay N hN1 3 le_rfl Δ hlo hhi (Fin.cons U V) hie.1 hie.2 hig.1 hig.2 s t hs hst ht

end
end HighTheta
