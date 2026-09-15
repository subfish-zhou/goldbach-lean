import Wu18938Campaign.M1.Confirmed.FixedOutput
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitErrorPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit Finset Real Filter
open scoped Classical Topology

theorem roughBox_absolute_power_relative (m j : ℕ) {η δ ε C ρ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
        C * N * log N ^ j / (N : ℝ) ^ ρ ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨c, hc, T1, _, hT1⟩ := roughBox_theta_lower m hη hδ
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget (j + (5 * m + 2))
      (show 0 < C / (ε * c) by positivity) hρ)
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hN i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ C * N * log N ^ j /
        ((C / (ε * c)) * log N ^ (j + (5 * m + 2))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (hT2 N hN2)
    _ = ε * (c * (N : ℝ) / log N ^ (5 * m + 2)) := by
      rw [pow_add]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hT1 N hN1 i Δ V hb) hε.le

theorem roughBox_R2_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      (sourceFamily N δ Δ V p high).R2 (⌊Q⌋₊ + 1) (sqrt Q) ≤
        ε * boxTheta N Q (convolutionWuWindows N Δ V) := by
  let B := (max 1 (1 / (η / 10))) ^ (m + 5)
  have hB : 0 < B := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  obtain ⟨C, hC, hEuler⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  obtain ⟨T0, hT04, hpay⟩ := roughBox_absolute_power_relative m 5 hη hδ hε
    (show 0 < 2 * C * B / log 2 by positivity)
    (show 0 < η / 10 by positivity)
  obtain ⟨T1, hlog⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp high Q
  have hN2 : 2 ≤ N := by omega
  have hg := omega3_source_sieve_geometry hN2 hδ hδhi
  have hlog1 := hlog N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  let L := sourceFamily N δ Δ V p high
  have hmod : ∀ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q), q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    dsimp only [Q] at hqd
    omega
  have hr := hEuler N (by omega) Profile L (⌊Q⌋₊ + 1) (sqrt Q)
    ((N : ℝ) ^ (η / 10)) B hg.2.2.2.1
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _) hB.le hmod
    (fun x hx => roughBox_relative_roughness hb hN2 hη hδ p hp high (mem_filter.mp hx).1)
    (roughBox_family_fibre hb hN2 hη hδ p hp high)
  calc
    _ ≤ C * B * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ (η / 10) * log 2)) := hr
    _ ≤ C * B * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ (η / 10) * log 2)) := by
      gcongr
      linarith
    _ = (2 * C * B / log 2) * N * log N ^ 5 / (N : ℝ) ^ (η / 10) := by ring
    _ ≤ _ := hpay N (by omega) i Δ V hb

theorem roughBox_small_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      (sourceFamily N δ Δ V p high).small (sqrt Q) ≤
        ε * boxTheta N Q (convolutionWuWindows N Δ V) := by
  let B := (max 1 (1 / (η / 10))) ^ (m + 6)
  have hB : 0 < B := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  obtain ⟨T, hT4, hpay⟩ := roughBox_absolute_power_relative m 0 hη hδ hε
    (show 0 < 2 * B by positivity)
    (show 0 < 1 - (1 / 2 - δ) / 2 by linarith)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp high Q
  have hN2 : 2 ≤ N := by omega
  let Z := sqrt Q
  have hpow := HighUnitSieve.source_small_power hN2 hδ hδhi
  have hZ1 : (1 : ℝ) ≤ Z := one_le_sqrt.mpr (one_le_rpow
    (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith : 0 ≤ 1 / 2 - δ))
  calc
    _ ≤ B * (Z + 1) := roughBox_small_finite hb hN2 hη hδ p hp high (sqrt_nonneg _)
    _ ≤ (2 * B) * Z := by nlinarith only [hZ1, hB]
    _ = (2 * B) * N * log N ^ (0 : ℕ) /
        (N : ℝ) ^ (1 - (1 / 2 - δ) / 2) := hpow.2.2.2.2.2 _
    _ ≤ _ := hpay N hN i Δ V hb

end Wu18938Campaign.M1.Confirmed
