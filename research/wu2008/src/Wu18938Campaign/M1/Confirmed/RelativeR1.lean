import Wu18938Campaign.M1.Confirmed.HighNonunit
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledCoprimeOutputFinite
import MathlibNt.Wu2008DoubleSieve.Omega3SourceSieveFactor

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit Finset Real Filter
open scoped Classical Topology

theorem roughBox_R1_relative (m : ℕ) {η δ ε κ F : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) (hκ : 0 < κ) (hF : 0 ≤ F) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ (α : Type*) (L : LabelledPhysical.Family α N),
      (∀ c ∈ L.labels, (N : ℝ) ^ κ ≤ L.cofactor c ∧
        (L.cofactor c : ℝ) ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ c ∈ L.labels, 1 ≤ L.weight c) →
      (∀ e, (∑ c ∈ L.layerFibre e, L.weight c) ≤ F) → ∀ Z : ℝ,
      L.R1 (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, T1, hT1, hd⟩ := LabelledPhysical.Family.R1_log_saving (5 * m + 3 : ℕ)
    κ F (by positivity) hκ hF hδ
  obtain ⟨c, hc, T2, _, hTheta⟩ := roughBox_theta_lower m hη hδ
  obtain ⟨T3, hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * c))))
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb α L hp hw hf Z
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 _).trans ((le_max_right T1 _).trans hN)
  have hlog := log_pos (by exact_mod_cast
    (show 1 < N by have := hT1.trans hN1; omega) : (1 : ℝ) < N)
  have hr := hd N hN1 α L hp hw hf Z
  rw [rpow_natCast] at hr
  have htheta := hTheta N hN2 i Δ V hb
  have hbudget : C / log (N : ℝ) ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp (hlogT N hN3)
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C * N / log (N : ℝ) ^ (5 * m + 3) := hr
    _ = (C / log (N : ℝ)) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by
      rw [show 5 * m + 3 = (5 * m + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / log (N : ℝ) ^ (5 * m + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htheta hε.le

theorem roughBox_nonunit_subfamily_R1 (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      ∀ G : LabelledPhysical.Family Profile N,
      G.labels ⊆ (sourceFamily N δ Δ V p high).labels →
      (∀ x, G.weight x = (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) ∧
        G.cofactor x = cofactor x) → ∀ Z : ℝ,
      G.R1 (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, ht⟩ := roughBox_R1_relative m hη hδ hε
    (show 0 < η / 10 by positivity)
    (show 0 ≤ (max 1 (1 / (η / 10))) ^ (m + 5) by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp high G hsub hdata Z
  have hN2 : 2 ≤ N := by omega
  apply ht N hN i Δ V hb Profile G
  · intro x hx
    have hg := roughBox_physical_geometry hb hN2 hη hδ p hp high (hsub hx)
    rw [(hdata x).2]
    exact ⟨hg.power_lower, hg.power_upper⟩
  · intro x hx
    rw [(hdata x).1]
    exact_mod_cast actual_coefficient_pos (mem_filter.mp (hsub hx)).1
  · intro e
    have hs : G.layerFibre e ⊆
        (sourceFamily N δ Δ V p high).labels.filter (fun x => cofactor x = e) := by
      intro x hx
      obtain ⟨hx, he⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hsub hx, (hdata x).2.symm.trans he⟩
    calc
      _ = ∑ x ∈ G.layerFibre e, (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) :=
        sum_congr rfl (fun x _ => (hdata x).1)
      _ ≤ ∑ x ∈ (sourceFamily N δ Δ V p high).labels.filter (fun x => cofactor x = e),
          (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ _ := roughBox_family_fibre hb hN2 hη hδ p hp high e

theorem roughBox_gamma_upper_without_R1 (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      let D := ⌊Q⌋₊ + 1
      let Z := sqrt Q
      let L := sourceFamily N δ Δ V p high
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V)
          (if high then 21 else 20) ≤
        actualUnit N δ p (convolutionWuWindows N Δ V) high +
          L.coprimePart.mass * ordinaryRosserMainSum true N 1 D Z +
          ε * boxTheta N Q (convolutionWuWindows N Δ V) +
          L.coprimePart.R2 D Z + L.coprimePart.small Z +
          ∑ b ∈ N.primeFactors, L.weightAt b := by
  obtain ⟨T, hT4, ht⟩ := roughBox_nonunit_subfamily_R1 m hη hδ hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb p hp high Q D Z L
  have hN4 : 4 ≤ N := hT4.trans hN
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  have hf := L.prime_upper_coprime_finite_sum (by omega) he D Z
    hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hr := ht N hN i Δ V hb p hp high L.coprimePart
    (filter_subset _ _) (fun _ => ⟨rfl, rfl⟩) Z
  have hs := roughBox_gamma_le_unit_family hb hN4 he p high
  dsimp only [Q, D, Z, L] at *
  linarith only [hf, hr, hs]

end Wu18938Campaign.M1.Confirmed
