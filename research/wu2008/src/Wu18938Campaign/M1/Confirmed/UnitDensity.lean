import Wu18938Campaign.M1.Confirmed.UnitCarrier

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Unit

open Wu2008DoubleSieve HighUnitSieve SecondFunctionalUnitPrimeFibre Finset Real Filter
open scoped Classical Topology

theorem physicalFamily_density (m n : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (hb : RoughBox m η δ N i Δ V)
        (hN2 : 2 ≤ N)
        (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
        (j : Fin n) (b : ℕ → ℝ),
      let L := physicalFamily hb hN2 hη hδ P j b
      L.primeMass ≤ L.mass *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let B := (max 1 (1 / (η / 10))) ^ (m + n)
  let G := (max 1 (1 / (η / 10))) ^ (m + n + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have heps : 0 < ε / 3 := by positivity
  obtain ⟨T0, hT04, hr1⟩ :=
    roughBox_R1_relative m hη hδ heps (show 0 < η / 10 by positivity) hB.le
  obtain ⟨C, hC, hEuler⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  obtain ⟨T1, _, hr2⟩ := roughBox_absolute_power_relative m 5 hη hδ heps
    (show 0 < 2 * C * B / log 2 by positivity) (show 0 < η / 10 by positivity)
  obtain ⟨T2, _, hsmall⟩ := roughBox_absolute_power_relative m 0 hη hδ heps hG
    (show 0 < 1 - (1 / 2 - δ) / 2 by linarith)
  obtain ⟨T3, _, hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  obtain ⟨T4, hlog⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 (max T1 (max T2 (max T3 T4))), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb hN2 P j b L
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let D := ⌊Q⌋₊ + 1
  let Z := sqrt Q
  have hg := omega3_source_sieve_geometry hN2 hδ hδhi
  have hf := L.prime_upper_finite he D Z hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hR1 : L.R1 D Z ≤ ε / 3 *
      boxTheta N Q (convolutionWuWindows N Δ V) := by
    apply hr1 N (by omega) i Δ V hb _ L
    · intro c hc
      have h := profile_geometry hb hN2 hη hδ P j b hc
      exact ⟨h.power_lower, h.power_upper⟩
    · intro c hc
      change (1 : ℝ) ≤ (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)
      exact_mod_cast coefficient_pos hc
    · exact physicalFamily_fibre hb hN2 hη hδ P j b
  have hmod : ∀ q ∈ omega3SieveModuli N D Z, q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    dsimp only [D, Q] at hqd
    omega
  have hEuler' := hEuler N (by omega) _ L D Z ((N : ℝ) ^ (η / 10)) B
    hg.2.2.2.1 (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _) hB.le hmod
    (fun c hc q hq hqc _ =>
      profile_rough hb hN2 hη hδ c (mem_family.mp hc).1 q hq hqc)
    (physicalFamily_fibre hb hN2 hη hδ P j b)
  have hlog1 := hlog N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  have hR2 : L.R2 D Z ≤ ε / 3 * boxTheta N Q (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ C * B * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ (η / 10) * log 2)) := hEuler'
      _ ≤ C * B * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ (η / 10) * log 2)) := by
        gcongr
        linarith
      _ = (2 * C * B / log 2) * N * log N ^ 5 / (N : ℝ) ^ (η / 10) := by ring
      _ ≤ _ := hr2 N (by omega) i Δ V hb
  have hpow := source_small_power hN2 hδ hδhi
  have hS : L.small Z ≤ ε / 3 * boxTheta N Q (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ G * Z := physicalFamily_small hb hN2 hη hδ P j b
        (sqrt_nonneg Q) hpow.2.2.2.2.1
      _ = G * N * log N ^ (0 : ℕ) /
          (N : ℝ) ^ (1 - (1 / 2 - δ) / 2) := hpow.2.2.2.2.2 G
      _ ≤ _ := hsmall N (by omega) i Δ V hb
  have hm := mul_le_mul_of_nonneg_left (hden N (by omega) he)
    (show 0 ≤ L.mass from sum_nonneg
      (fun c hc => mul_nonneg (L.weight_nonneg c hc) (Nat.cast_nonneg _)))
  change L.mass * ordinaryRosserMainSum true N 1 D Z ≤ _ at hm
  linarith only [hf, hR1, hR2, hS, hm]

end Wu18938Campaign.M1.Confirmed.Unit

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighUnitSieve HighUnitPrimeOutput HighUnitSource Finset Real
open scoped Classical

theorem roughBox_unit_pair_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      HighNonunit.actualUnit N δ p (convolutionWuWindows N Δ V) false +
        HighNonunit.actualUnit N δ p (convolutionWuWindows N Δ V) true ≤
        (HighUnit.boxedSigma20 N δ (convolutionWuWindows N Δ V)
            (fun _ => 1 / p.kappa2) (fun _ => 1 / p.kappa3) (fun _ => 1 / p.s) +
          HighUnit.boxedSigma21 N δ (convolutionWuWindows N Δ V)
            (fun _ => 1 / p.kappa3) (fun _ => 1 / p.s)) *
          (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
            wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, h20⟩ := Unit.physicalFamily_density m 4 hη hδ hδhi hρ (half_pos hε)
  obtain ⟨T1, _, h21⟩ := Unit.physicalFamily_density m 5 hη hδ hδhi hρ (half_pos hε)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb p hp hs
  have hN2 : 2 ≤ N := by omega
  let W := convolutionWuWindows N Δ V
  let R := fun d : ℕ => (N : ℝ) ^ (1 / 2 - δ) / d
  let a2 := fun _ : ℕ => 1 / p.kappa2
  let a3 := fun _ : ℕ => 1 / p.kappa3
  let b := fun _ : ℕ => 1 / p.s
  have hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d := fun _ hd => hb.support_pos hd
  have hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d :=
    fun _ hd => (hb.support_geometry hN2 hη hδ hd).2.2.1
  have hu20 := h20 N (by omega) he i Δ V hb hN2
    (fun d => HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d)) (Fin.last 3) b
  have hu21 := h21 N (by omega) he i Δ V hb hN2
    (fun d => HighUnit.primePrefix21 (R d) (a3 d) (b d)) (Fin.last 4) b
  dsimp only at hu20 hu21
  rw [Unit.physicalFamily_mass, Unit.physicalFamily_primeMass] at hu20 hu21
  have he20 : envelope20 N W R a2 a3 b =
      outputMass N W (family20 N W R a2 a3 b) (Fin.last 3) b :=
    envelope20_interval W R a2 a3 b hdpos hR
  have he21 : envelope21 N W R a3 b =
      outputMass N W (family21 N W R a3 b) (Fin.last 4) b :=
    envelope21_interval W R a3 b hdpos hR
  have hm20 : HighUnit.boxedSigma20 N δ W a2 a3 b =
      intervalMass N W (family20 N W R a2 a3 b) (Fin.last 3) b :=
    boxedSigma20_interval W a2 a3 b hdpos hR
  have hm21 : HighUnit.boxedSigma21 N δ W a3 b =
      intervalMass N W (family21 N W R a3 b) (Fin.last 4) b :=
    boxedSigma21_interval W a3 b hdpos hR
  change outputMass N W (family20 N W R a2 a3 b) (Fin.last 3) b ≤
    intervalMass N W (family20 N W R a2 a3 b) (Fin.last 3) b * _ + _ at hu20
  change outputMass N W (family21 N W R a3 b) (Fin.last 4) b ≤
    intervalMass N W (family21 N W R a3 b) (Fin.last 4) b * _ + _ at hu21
  rw [← he20, ← hm20] at hu20
  rw [← he21, ← hm21] at hu21
  obtain ⟨h2, h3, hbs⟩ := parameter_outer_bounds hp hs
  have hs20 := HighUnitPrimeOutput.source_le20 (N := N) (a0 := fun _ => 1 / p.S)
    (a1 := fun _ => 1 / p.kappa1) (a2 := a2) (a3 := a3) (b := b)
    hdpos hR (fun _ _ => h2) (fun _ _ => hbs)
  have hs21 := HighUnitPrimeOutput.source_le21 (N := N) (a0 := fun _ => 1 / p.S)
    (a1 := fun _ => 1 / p.kappa1) (a2 := a2) (a3 := a3) (b := b)
    hdpos hR (fun _ _ => h3) (fun _ _ => hbs)
  change HighNonunit.actualUnit N δ p W false ≤ _ at hs20
  change HighNonunit.actualUnit N δ p W true ≤ _ at hs21
  dsimp only [W, R, a2, a3, b] at hu20 hu21 hs20 hs21
  nlinarith only [hu20, hu21, hs20, hs21]

end Wu18938Campaign.M1.Confirmed
