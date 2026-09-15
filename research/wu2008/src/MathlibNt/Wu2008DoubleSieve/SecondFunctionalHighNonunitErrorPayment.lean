import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitErrorInputs

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real Filter
open scoped Classical

/-- Both actual high-nonunit words pay R2 and Small from one epsilon budget.
The fixed threshold precedes N, the source box, all mother parameters and both
independent original/good choices. The stronger original CLOSED Small bound is
also exported; no global roughness or target-shaped payment hypothesis occurs. -/
theorem source_R2_small_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ good0 good1 : Bool,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      let D := ⌊Q⌋₊+1
      let Z := sqrt Q
      let L0 := r1Family N δ Δ V p false good0
      let L1 := r1Family N δ Δ V p true good1
      let E := L0.R2 D Z + L1.R2 D Z
      let S := closedSmall N δ p W false Z + closedSmall N δ p W true Z
      1 < D ∧ Z ≤ (D : ℝ) ∧ Z ≤ N ∧
      (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) ∧
      E ≤ (ε/2)*boxTheta N Q W ∧ S ≤ (ε/2)*boxTheta N Q W ∧
      E + S ≤ ε*boxTheta N Q W ∧
      E + (L0.small Z + L1.small Z) ≤ ε*boxTheta N Q W := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  let F := H^(k+5)
  let G := H^(k+6)
  let β := (1/2-δ)/2
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hH : 1 ≤ H := le_max_left _ _
  have hF : 0 < F := pow_pos (lt_of_lt_of_le zero_lt_one hH) _
  have hG : 0 < G := pow_pos (lt_of_lt_of_le zero_lt_one hH) _
  have hρ : 0 < 1-β := by dsimp [β]; linarith
  have heps : 0 < ε/2 := by positivity
  obtain ⟨C,hC,hEuler⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  obtain ⟨T0,hT04,hT0⟩ := source_error_inputs k hδ hδhi
  obtain ⟨T1,_,hT1⟩ := omega3_absolute_power_log_relative k 5 hδ hδhi heps
    (show 0 < 4*C*F/log 2 by positivity) hη
  obtain ⟨T2,_,hT2⟩ := omega3_absolute_power_log_relative k 0 hδ hδhi heps
    (show 0 < 2*G by positivity) hρ
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3,hT3⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  let T := max T0 (max T1 (max T2 T3))
  have hT4 : 4 ≤ T := hT04.trans (le_max_left _ _)
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb p hp good0 good1
  have hN0 : T0 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2' : T2 ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : T3 ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN4 : 4 ≤ N := hT4.trans hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog1 := hT3 N hN3
  have hgeom := omega3_source_sieve_geometry hN2 hδ hδhi
  have hpow := HighUnitSieve.source_small_power hN2 hδ hδhi
  have hin := hT0 N hN0 i Δ V hb p hp
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ)^(1/2-δ)
  let D := ⌊Q⌋₊+1
  let Z := sqrt Q
  let L0 := r1Family N δ Δ V p false good0
  let L1 := r1Family N δ Δ V p true good1
  have hmod : ∀ q ∈ omega3SieveModuli N D Z, q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hgeom.2.2.2.2.2.2.1
    dsimp only [D,Q] at hqd
    omega
  have hr0 := hEuler N (by omega) _ L0 D Z ((N : ℝ)^η) F
    hgeom.2.2.2.1 (rpow_pos_of_pos hNr _) hF.le hmod
    (hin.1 false good0).1 (hin.1 false good0).2
  have hr1 := hEuler N (by omega) _ L1 D Z ((N : ℝ)^η) F
    hgeom.2.2.2.1 (rpow_pos_of_pos hNr _) hF.le hmod
    (hin.1 true good1).1 (hin.1 true good1).2
  have hr : L0.R2 D Z + L1.R2 D Z ≤ (ε/2)*boxTheta N Q W := by
    calc
      _ ≤ 2*C*F*N*((1+log N)*log N^4/((N : ℝ)^η*log 2)) := by linarith
      _ ≤ 2*C*F*N*((2*log N)*log N^4/((N : ℝ)^η*log 2)) := by
        gcongr
        linarith
      _ = (4*C*F/log 2)*N*log N^5/(N : ℝ)^η := by ring
      _ ≤ _ := hT1 N hN1 i Δ V hb
  have hs : closedSmall N δ p W false Z + closedSmall N δ p W true Z ≤
      (ε/2)*boxTheta N Q W := by
    calc
      _ ≤ 2*G*Z := hin.2 Z hpow.2.2.2.1 hpow.2.2.2.2.1
      _ = (2*G)*N*log N^(0 : ℕ)/(N : ℝ)^(1-β) := hpow.2.2.2.2.2 (2*G)
      _ ≤ _ := hT2 N hN2' i Δ V hb
  have hs0 := r1Family_small_le_closedSmall (N := N) (δ := δ) (Δ := Δ) (V := V) p false good0 Z
  have hs1 := r1Family_small_le_closedSmall (N := N) (δ := δ) (Δ := Δ) (V := V) p true good1 Z
  refine ⟨hgeom.2.2.2.2.1, hgeom.2.2.2.2.2.1, hgeom.2.2.2.1, hmod,
    hr, hs, by linarith, ?_⟩
  change L0.R2 D Z + L1.R2 D Z + (L0.small Z + L1.small Z) ≤ ε*boxTheta N Q W
  linarith

end Wu2008DoubleSieve.HighNonunit
