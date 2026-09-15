import Wu18938Campaign.M1.Confirmed.RelativeR1
import Wu18938Campaign.M1.Confirmed.RelativeErrors
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit Finset Real
open scoped Classical

theorem roughBox_restricted_prime_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      ∀ P : Profile → Prop,
      let G := (sourceFamily N δ Δ V p high).restrictLabels P
      G.primeMass ≤ G.mass *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have heps : 0 < ε / 3 := by positivity
  obtain ⟨T0, hT04, hR1⟩ := roughBox_nonunit_subfamily_R1 m hη hδ heps
  obtain ⟨T1, _, hR2⟩ := roughBox_R2_relative m hη hδ hδhi heps
  obtain ⟨T2, _, hsmall⟩ := roughBox_small_relative m hη hδ hδhi heps
  obtain ⟨T3, _, hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 (max T1 (max T2 T3)), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb p hp high P G
  let L := sourceFamily N δ Δ V p high
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let D := ⌊Q⌋₊ + 1
  let Z := sqrt Q
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hf := G.prime_upper_finite he D Z hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hr1 := hR1 N (by omega) i Δ V hb p hp high G
    (filter_subset _ _) (fun _ => ⟨rfl, rfl⟩) Z
  have hr2 := (L.restrictLabels_R2_le P D Z).trans (hR2 N (by omega) i Δ V hb p hp high)
  have hs := (L.restrictLabels_small_le P Z).trans
    (hsmall N (by omega) i Δ V hb p hp high)
  have hx : 0 ≤ G.mass :=
    sum_nonneg (fun x hx => mul_nonneg (G.weight_nonneg x hx) (Nat.cast_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (hden N (by omega) he) hx
  change G.mass * ordinaryRosserMainSum true N 1 D Z ≤ _ at hm
  dsimp only [G, L, Q, D, Z] at *
  nlinarith only [hf, hr1, hr2, hs, hm]

theorem roughBox_gamma_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V)
          (if high then 21 else 20) ≤
        actualUnit N δ p (convolutionWuWindows N Δ V) high +
          (sourceFamily N δ Δ V p high).mass *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
              wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, ht⟩ := roughBox_restricted_prime_density m hη hδ hδhi hρ hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb p hp high
  have hd := ht N hN he i Δ V hb p hp high (fun _ => True)
  have hid : (sourceFamily N δ Δ V p high).restrictLabels (fun _ => True) =
      sourceFamily N δ Δ V p high := by
    unfold LabelledPhysical.Family.restrictLabels
    simp only [filter_true]
  rw [hid] at hd
  have hf := roughBox_gamma_le_unit_family hb (hT4.trans hN) he p high
  linarith only [hd, hf]

end Wu18938Campaign.M1.Confirmed
