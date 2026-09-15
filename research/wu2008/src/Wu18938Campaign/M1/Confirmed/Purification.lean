import Wu18938Campaign.M1.Confirmed.Density
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughPurification

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit Finset Real Filter
open scoped Classical Topology

theorem roughBox_bad_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      (sourceFamily N δ Δ V p high).noncoprimePart.primeMass ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let B := (max 1 (1 / (η / 10))) ^ (m + 6)
  obtain ⟨T, hT, ht⟩ := roughBox_absolute_power_relative m 1 hη hδ hε
    (show 0 < B / log 2 by dsimp [B]; positivity) (by norm_num : (0 : ℝ) < 1)
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb p hp high
  have hN2 : 2 ≤ N := by omega
  have hf := (sourceFamily N δ Δ V p high).noncoprimePart_primeMass_le_log
    (by omega) (show 0 ≤ B by dsimp [B]; positivity)
    (fun ell _ => roughBox_weightAt hb hN2 hη hδ p hp high ell)
  have heq : (B / log 2) * N * log N ^ 1 / (N : ℝ) ^ (1 : ℝ) =
      B * log N / log 2 := by
    rw [rpow_one, pow_one]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  have hh := ht N hN i Δ V hb
  rw [heq] at hh
  exact hf.trans hh

theorem roughBox_square_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      (sourceFamily N δ Δ V p high).squareRawMass ((N : ℝ) ^ (η / 10)) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let B := (max 1 (1 / (η / 10))) ^ (m + 5)
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨T0, hT04, hpay⟩ := roughBox_absolute_power_relative m 1 hη hδ hε
    (show 0 < 4 * B by positivity) (show 0 < η / 10 by positivity)
  obtain ⟨T1, hpow⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 0 (by norm_num : (0 : ℝ) < 2)
      (show 0 < η / 10 by positivity))
  obtain ⟨T2, hlog⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp high
  have hN2 : 2 ≤ N := by omega
  let Y := (N : ℝ) ^ (η / 10)
  have hY : 2 ≤ Y := by simpa only [pow_zero, mul_one] using hpow N (by omega)
  have hY0 : 0 < Y := by linarith
  have hY1 : 0 < Y - 1 := by linarith
  have hlog1 := hlog N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  have hs := (sourceFamily N δ Δ V p high).squareRawMass_le hY hB.le
    (roughBox_family_fibre hb hN2 hη hδ p hp high)
  have hd : 1 / (Y - 1) ≤ 2 / Y := by
    apply (div_le_div_iff₀ hY1 hY0).mpr
    linarith
  calc
    _ ≤ B * N * (1 + log N) / (Y - 1) := hs
    _ = (B * N * (1 + log N)) * (1 / (Y - 1)) := by ring
    _ ≤ (B * N * (1 + log N)) * (2 / Y) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (B * N * (2 * log N)) * (2 / Y) := by gcongr; linarith
    _ = (4 * B) * N * log N ^ 1 / (N : ℝ) ^ (η / 10) := by dsimp only [Y]; ring
    _ ≤ _ := hpay N (by omega) i Δ V hb

theorem roughBox_primeMass_rough (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      (sourceFamily N δ Δ V p high).primeMass ≤
        (roughFamily N δ Δ V p high).primeMass +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, hsq⟩ := roughBox_square_relative m hη hδ (half_pos hε)
  obtain ⟨T1, _, hbad⟩ := roughBox_bad_relative m hη hδ (half_pos hε)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp high
  have hN2 : 2 ≤ N := by omega
  let L := sourceFamily N δ Δ V p high
  have hf := L.primeMass_le_restrict_add_square_add_bad profileRough
    ((N : ℝ) ^ (η / 10)) (by
      intro x hx hc hn
      have hi := profile_data (mem_filter.mp hx).1
      exact masked_good_nonrough_square hi.2.2.2.2.1 hc hn
        (roughBox_relative_roughness hb hN2 hη hδ p hp high (mem_filter.mp hx).1))
  have hs := hsq N (by omega) i Δ V hb p hp high
  have he := hbad N (by omega) i Δ V hb p hp high
  change L.primeMass ≤ (roughFamily N δ Δ V p high).primeMass + _ + _ at hf
  linarith only [hf, hs, he]

theorem roughBox_gamma_rough_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V)
          (if high then 21 else 20) ≤
        actualUnit N δ p (convolutionWuWindows N Δ V) high +
          (roughFamily N δ Δ V p high).mass *
            (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
              wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, hpur⟩ := roughBox_primeMass_rough m hη hδ (half_pos hε)
  obtain ⟨T1, _, hden⟩ :=
    roughBox_restricted_prime_density m hη hδ hδhi hρ (half_pos hε)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb p hp high
  have hf := roughBox_gamma_le_unit_family hb (by omega) he p high
  have hp' := hpur N (by omega) i Δ V hb p hp high
  have hd := hden N (by omega) he i Δ V hb p hp high profileRough
  change (roughFamily N δ Δ V p high).primeMass ≤
    (roughFamily N δ Δ V p high).mass * _ + _ at hd
  linarith only [hf, hp', hd]

end Wu18938Campaign.M1.Confirmed
