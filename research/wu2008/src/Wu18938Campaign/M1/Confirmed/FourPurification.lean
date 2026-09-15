import Wu18938Campaign.M1.Confirmed.FourDensity

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Four

open Wu2008DoubleSieve FourPrimeNonunit Finset Real Filter
open scoped Classical Topology

theorem bad_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).noncoprimePart.primeMass ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let B := (max 1 (1 / (η / 10))) ^ (m + 4)
  obtain ⟨T, hT, ht⟩ := roughBox_absolute_power_relative m 1 hη hδ he
    (show 0 < B / log 2 by dsimp [B]; positivity) (by norm_num : (0 : ℝ) < 1)
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb p hp j
  have hf := (sourceFamily N δ Δ V p j).noncoprimePart_primeMass_le_log
    (by omega) (show 0 ≤ B by dsimp [B]; positivity) (by
      intro ell hell
      rw [sourceFamily_weightAt_prime V p j (Nat.prime_of_mem_primeFactors hell)]
      exact fixed_output hb (by omega) hη hδ p hp j ell)
  have heq : (B / log 2) * N * log N ^ 1 / (N : ℝ) ^ (1 : ℝ) =
      B * log N / log 2 := by
    rw [rpow_one, pow_one]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  have hh := ht N hN i Δ V hb
  rw [heq] at hh
  exact hf.trans hh

theorem square_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).squareRawMass ((N : ℝ) ^ (η / 10)) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let B := (max 1 (1 / (η / 10))) ^ (m + 3)
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨T0, hT04, hpay⟩ := roughBox_absolute_power_relative m 1 hη hδ he
    (show 0 < 4 * B by positivity) (show 0 < η / 10 by positivity)
  obtain ⟨T1, hpow⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 0 (by norm_num : (0 : ℝ) < 2)
      (show 0 < η / 10 by positivity))
  obtain ⟨T2, hlog⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp j
  let Y := (N : ℝ) ^ (η / 10)
  have hY : 2 ≤ Y := by simpa only [pow_zero, mul_one] using hpow N (by omega)
  have hY0 : 0 < Y := by linarith
  have hY1 : 0 < Y - 1 := by linarith
  have hlog1 := hlog N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  have hs := (sourceFamily N δ Δ V p j).squareRawMass_le hY hB.le
    (family_fibre hb (by omega) hη hδ p hp j)
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

theorem primeMass_rough (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).primeMass ≤
        (roughFamily N δ Δ V p j).primeMass +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, hsq⟩ := square_relative m hη hδ (half_pos he)
  obtain ⟨T1, _, hbad⟩ := bad_relative m hη hδ (half_pos he)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp j
  let L := sourceFamily N δ Δ V p j
  have hf := L.primeMass_le_restrict_add_square_add_bad profileRough
    ((N : ℝ) ^ (η / 10)) (by
      intro x hx hc hn
      exact masked_good_nonrough_square (sourceFamily_mask N δ Δ V p j hx).2 hc hn
        (relative_roughness hb (by omega) hη hδ p hp j hx))
  have hs := hsq N (by omega) i Δ V hb p hp j
  have herr := hbad N (by omega) i Δ V hb p hp j
  change L.primeMass ≤ (roughFamily N δ Δ V p j).primeMass + _ + _ at hf
  linarith only [hf, hs, herr]

theorem rough_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      (sourceFamily N δ Δ V p j).primeMass ≤ (roughFamily N δ Δ V p j).mass *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0, hT04, hpur⟩ := primeMass_rough m hη hδ (half_pos he)
  obtain ⟨T1, _, hden⟩ := restricted_density m hη hδ hδhi hρ (half_pos he)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb p hp j
  have hp' := hpur N (by omega) i Δ V hb p hp j
  have hd := hden N (by omega) heven i Δ V hb p hp j profileRough
  change (roughFamily N δ Δ V p j).primeMass ≤ (roughFamily N δ Δ V p j).mass * _ + _ at hd
  linarith only [hp', hd]

end Wu18938Campaign.M1.Confirmed.Four
