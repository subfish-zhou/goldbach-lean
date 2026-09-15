import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeErrorInputs
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real Filter
open scoped Classical

/-- Four original families pay R2 and closed Small from one epsilon budget.
Every restriction is chosen after the common threshold and keeps the original data.
No monotonicity of signed R1 is used. -/
theorem source_R2_small_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      let D := ⌊Q⌋₊+1
      let Z := sqrt Q
      let L := sourceFamily N δ Δ V p
      let E := ∑ j : Fin 4, (L j).R2 D Z
      let S := ∑ j : Fin 4, closedSmall N δ p W j Z
      1 < D ∧ Z ≤ (D : ℝ) ∧ Z ≤ N ∧
      (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) ∧
      E ≤ (ε/2)*boxTheta N Q W ∧ S ≤ (ε/2)*boxTheta N Q W ∧
      E + S ≤ ε*boxTheta N Q W ∧
      E + (∑ j : Fin 4, (L j).small Z) ≤ ε*boxTheta N Q W ∧
      ∀ P : Fin 4 → Gamma16Profile → Prop,
        let LP := fun j => (L j).restrictLabels (P j)
        (∑ j : Fin 4, (LP j).R2 D Z) ≤ (ε/2)*boxTheta N Q W ∧
        (∑ j : Fin 4, (LP j).small Z) ≤ (ε/2)*boxTheta N Q W ∧
        (∑ j : Fin 4, (LP j).R2 D Z) + (∑ j : Fin 4, (LP j).small Z) ≤
          ε*boxTheta N Q W := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  let F := H^(k+3)
  let G := H^(k+4)
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
    (show 0 < 8*C*F/log 2 by positivity) hη
  obtain ⟨T2,_,hT2⟩ := omega3_absolute_power_log_relative k 0 hδ hδhi heps
    (show 0 < 4*G by positivity) hρ
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3,hT3⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  let T := max T0 (max T1 (max T2 T3))
  have hT4 : 4 ≤ T := hT04.trans (le_max_left _ _)
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb p hp
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
  let L := sourceFamily N δ Δ V p
  have hmod : ∀ q ∈ omega3SieveModuli N D Z, q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hgeom.2.2.2.2.2.2.1
    dsimp only [D,Q] at hqd
    omega
  have hrj (j : Fin 4) := hEuler N (by omega) _ (L j) D Z ((N : ℝ)^η) F
    hgeom.2.2.2.1 (rpow_pos_of_pos hNr _) hF.le hmod
    (hin.1 j).1 (hin.1 j).2
  have hr : (∑ j : Fin 4, (L j).R2 D Z) ≤ (ε/2)*boxTheta N Q W := by
    calc
      _ ≤ ∑ _j : Fin 4, C*F*N*((1+log N)*log N^4/((N : ℝ)^η*log 2)) :=
        sum_le_sum (fun j _ => hrj j)
      _ = 4*C*F*N*((1+log N)*log N^4/((N : ℝ)^η*log 2)) := by simp; ring
      _ ≤ 4*C*F*N*((2*log N)*log N^4/((N : ℝ)^η*log 2)) := by
        gcongr
        linarith
      _ = (8*C*F/log 2)*N*log N^5/(N : ℝ)^η := by ring
      _ ≤ _ := hT1 N hN1 i Δ V hb
  have hs : (∑ j : Fin 4, closedSmall N δ p W j Z) ≤
      (ε/2)*boxTheta N Q W := by
    calc
      _ ≤ 4*G*Z := hin.2 Z hpow.2.2.2.1
      _ = (4*G)*N*log N^(0 : ℕ)/(N : ℝ)^(1-β) := hpow.2.2.2.2.2 (4*G)
      _ ≤ _ := hT2 N hN2' i Δ V hb
  have hsc : (∑ j : Fin 4, (L j).small Z) ≤
      ∑ j : Fin 4, closedSmall N δ p W j Z :=
    sum_le_sum (fun j _ => source_small_le_closed N δ Δ V p j Z)
  refine ⟨hgeom.2.2.2.2.1, hgeom.2.2.2.2.2.1, hgeom.2.2.2.1, hmod,
    hr, hs, by linarith, by linarith, ?_⟩
  intro P
  have hrP : (∑ j : Fin 4, ((L j).restrictLabels (P j)).R2 D Z) ≤
      ∑ j : Fin 4, (L j).R2 D Z :=
    sum_le_sum (fun j _ => (L j).restrictLabels_R2_le (P j) D Z)
  have hsP : (∑ j : Fin 4, ((L j).restrictLabels (P j)).small Z) ≤
      ∑ j : Fin 4, (L j).small Z :=
    sum_le_sum (fun j _ => (L j).restrictLabels_small_le (P j) Z)
  exact ⟨hrP.trans hr, (hsP.trans hsc).trans hs, by dsimp only; linarith⟩

/-- A consumer-facing arbitrary four-label restriction at the same source scales. -/
theorem source_restricted_R2_small_payment (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ P : Fin 4 → Gamma16Profile → Prop,
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      let D := ⌊Q⌋₊+1
      let Z := sqrt Q
      let L := fun j => (sourceFamily N δ Δ V p j).restrictLabels (P j)
      1 < D ∧ Z ≤ (D : ℝ) ∧ Z ≤ N ∧
      (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) ∧
      (∑ j : Fin 4, (L j).R2 D Z) ≤ (ε/2)*boxTheta N Q W ∧
      (∑ j : Fin 4, (L j).small Z) ≤ (ε/2)*boxTheta N Q W ∧
      (∑ j : Fin 4, (L j).R2 D Z) + (∑ j : Fin 4, (L j).small Z) ≤
        ε*boxTheta N Q W := by
  obtain ⟨T,hT,h⟩ := source_R2_small_payment k hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp P
  have h' := h N hN i Δ V hb p hp
  exact ⟨h'.1,h'.2.1,h'.2.2.1,h'.2.2.2.1,h'.2.2.2.2.2.2.2.2 P⟩

end Wu2008DoubleSieve.FourPrimeNonunit
