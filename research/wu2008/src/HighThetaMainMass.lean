import HighThetaTrueLi

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- Full prime-count to true-li mass payment on actually supported boxes. -/
theorem X_true_li_relative {δ η ε : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, i ≤ 3 → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin i → ℝ, (∀ j, (N : ℝ)^η ≤ V j) → (∀ j, V j ≤ N) →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j → p.Prime ∧ (N : ℝ)^η ≤ p) →
      (∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let W := convolutionWuWindows N Δ V
      |omega3SieveX N δ s t W-liX N δ s t W| ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  obtain ⟨C,hC,T1,hT14,hbound⟩ := X_true_li_log_saving 3 hη (show (0 : ℝ)<18 by norm_num)
  obtain ⟨T2,hmass⟩ := wu_boxConvolution_mass_bounds 3 hη
  let c : ℝ := 2*liuUniversalProduct*(1/12 : ℝ)^3
  have hc : 0 < c := by dsimp [c]; have := liuUniversalProduct_pos; positivity
  obtain ⟨T3,hbudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 1 (C/(ε*c)))))
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN i hi Δ hlo hhi V hV hVN hW hsize s t hs hst ht W
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN4 := hT14.trans hN1
  have hl : max 1 (C/(ε*c)) ≤ log (N : ℝ) := hbudget N hN3
  have hlog : 0 < log (N : ℝ) := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hl)
  have htheta : c*N/log N^17 ≤ boxTheta N ((N : ℝ)^(1/2-δ)) W := by
    have hm := (hmass N hN2 i hi Δ hlo hhi V hV hVN).1
    have hprod := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 2*liuUniversalProduct*N/log N^2 by have := liuUniversalProduct_pos; positivity)
    have hth := theta_from_actual_support W hN4 hδ hη (fun j p hp => (hW j p hp).1) hsize
    calc
      _ = 2*liuUniversalProduct*N/log N^2*((1/12 : ℝ)^3/log N^(5*3)) := by dsimp [c]; ring
      _ ≤ _ := hprod.trans hth
  have hb : C/log N ≤ ε*c := by
    apply (div_le_iff₀ hlog).mpr
    have hp := (div_le_iff₀ (show 0 < ε*c by positivity)).mp ((le_max_right _ _).trans hl)
    nlinarith
  calc
    _ ≤ C*N/log (N : ℝ)^(18 : ℝ) := hbound N hN1 i hi W hW hsize s t hs hst ht
    _ = (C/log N)*(N/log N^17) := by norm_num; ring
    _ ≤ (ε*c)*(N/log N^17) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = ε*(c*N/log N^17) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

/-- Both main-mass conventions have the same literal li centre. -/
def MainMassPaid {i : ℕ} (N : ℕ) (δ ε s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  |omega3SieveX N δ s t W-liX N δ s t W| ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) W ∧
  |strictX N δ s t W-liX N δ s t W| ≤ ε*boxTheta N ((N : ℝ)^(1/2-δ)) W

/-- One original/insertion threshold for genuine strict AND closed main masses. -/
theorem original_and_inserted_main_mass {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        MainMassPaid N δ ε s t (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          MainMassPaid N δ ε s t (convolutionWuWindows N Δ (Fin.cons U V)) := by
  have hε2 : 0 < ε/2 := half_pos hε
  obtain ⟨T1,hT14,hpay⟩ := X_true_li_relative hδ.le (show 0 < highEta by norm_num [highEta]) hε2
  obtain ⟨T2,_,hend⟩ := original_and_inserted_X_boundary hδ hδhi hε2
  obtain ⟨T3,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN4 := hT14.trans hN1
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN3 Δ hlo hhi
  have hends := hend N hN2 Δ hlo hhi V hV hrect s t hs hst ht
  have hcombine : ∀ {i : ℕ} (W : Fin i → Finset ℕ),
      |omega3SieveX N δ s t W-liX N δ s t W| ≤ ε/2*boxTheta N ((N : ℝ)^(1/2-δ)) W →
      XBoundaryPaid N δ (ε/2) s t W → MainMassPaid N δ ε s t W := by
    intro i W hx hb
    have hθ : 0 ≤ boxTheta N ((N : ℝ)^(1/2-δ)) W :=
      nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hx) hε2
    have hdiff : |strictX N δ s t W-omega3SieveX N δ s t W| ≤
        ε/2*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
      rw [abs_sub_comm, abs_of_nonneg hb.1]
      exact hb.2
    refine ⟨hx.trans (mul_le_mul_of_nonneg_right (by linarith) hθ),?_⟩
    have habs := abs_sub_le (strictX N δ s t W) (omega3SieveX N δ s t W) (liX N δ s t W)
    linarith
  have he := original_endpoints (show 2 ≤ N by omega) hV hrect
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hcombine _ (hpay N hN1 2 (by norm_num) Δ hlo hhi V he.1 he.2 hg.1 hg.2 s t hs hst ht) hends.1, ?_⟩
  intro U hw
  have hie := inserted_endpoints (show 2 ≤ N by omega) hδ.le hδhi hΔ hΔhi hV hrect hw
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hcombine _ (hpay N hN1 3 le_rfl Δ hlo hhi (Fin.cons U V) hie.1 hie.2 hig.1 hig.2 s t hs hst ht) (hends.2 U hw)

end
end HighTheta
