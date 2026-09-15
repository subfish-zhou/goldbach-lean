import Wu18938Campaign.M4.HighNonunitR1
import Wu18938Campaign.M4.LabelledOutput
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRelativeRoughness
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitErrorPayment
import MathlibNt.Wu2008DoubleSieve.HighSixOmega3Remainders

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real Filter
open scoped Classical Topology

theorem original_nonunit_family_fibre {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool) (e : ℕ) :
    let L := originalNonunitFamily j N δ high
    (∑ x ∈ L.labels.filter (fun x => L.cofactor x = e), L.weight x) ≤ (40 : ℝ) ^ 6 := by
  let L := originalNonunitFamily j N δ high
  have hs : L.labels.filter (fun x => L.cofactor x = e) ⊆
      (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high).filter
        (fun x => cofactor x = e) := by
    intro x hx
    obtain ⟨hx, he⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1, he⟩
  calc
    _ ≤ ∑ x ∈ (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high).filter
        (fun x => cofactor x = e), (convolutionCoeff (windows j N) x.1 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ (40 : ℝ) ^ (1 + arity high) := original_nonunit_fixed_cofactor j hN hd hh high e
    _ ≤ 40 ^ 6 := pow_le_pow_right₀ (by norm_num) (by cases high <;> simp [arity])

theorem original_nonunit_weightAt {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (high : Bool) (ell : ℕ) :
    (originalNonunitFamily j N δ high).weightAt ell ≤ (40 : ℝ) ^ 7 := by
  have h := labelled_output_from_cofactor (originalNonunitFamily j N δ high)
    (by omega) (by norm_num : (0 : ℝ) < 1 / 40) (by positivity : (0 : ℝ) ≤ 40 ^ 6)
    (fun x hx => (original_nonunit_geometry j hN hd hh high hx).lower_large)
    (original_nonunit_family_fibre j hN hd hh high) ell
  norm_num at h
  exact h.trans_eq (by norm_num)

theorem original_nonunit_R2_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ high : Bool,
      let Q := (N : ℝ) ^ (1 / 2 - δ)
      (originalNonunitFamily j N δ high).R2 (⌊Q⌋₊ + 1) (sqrt Q) ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨C, hC, hEuler⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  obtain ⟨T0, hT04, hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 5 heps
    (show 0 < 2 * C * (40 : ℝ) ^ 6 / log 2 by positivity)
    (show (0 : ℝ) < 1 / 40 by norm_num)
  obtain ⟨T1, hlog⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN j high Q
  have hN2 : 2 ≤ N := by omega
  have hg := omega3_source_sieve_geometry hN2 hd (show δ < 1 / 2 by linarith)
  have hlog1 := hlog N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  let L := originalNonunitFamily j N δ high
  have hmod : ∀ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) (sqrt Q), q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    dsimp only [Q] at hqd
    omega
  have hr := hEuler N (by omega) Profile L (⌊Q⌋₊ + 1) (sqrt Q)
    ((N : ℝ) ^ (1 / 40 : ℝ)) (40 ^ 6) hg.2.2.2.1
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _) (by positivity) hmod
    (fun x hx => original_nonunit_relative j hN2 hd hh high (mem_filter.mp hx).1)
    (original_nonunit_family_fibre j hN2 hd hh high)
  calc
    _ ≤ C * (40 : ℝ) ^ 6 * N *
        ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ (1 / 40 : ℝ) * log 2)) := hr
    _ ≤ C * (40 : ℝ) ^ 6 * N *
        ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ (1 / 40 : ℝ) * log 2)) := by
      gcongr
      linarith
    _ = (2 * C * (40 : ℝ) ^ 6 / log 2) * N * log N ^ 5 /
        (N : ℝ) ^ (1 / 40 : ℝ) := by ring
    _ ≤ _ := hp N (by omega)

theorem original_nonunit_small_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ high : Bool,
      (originalNonunitFamily j N δ high).small (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT, hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 0 heps
    (show (0 : ℝ) < 2 * 40 ^ 7 by positivity)
    (show 0 < 1 - (1 / 2 - δ) / 2 by linarith)
  refine ⟨T, hT, ?_⟩
  intro N hN j high
  have hN2 : 2 ≤ N := by omega
  let Z := sqrt ((N : ℝ) ^ (1 / 2 - δ))
  have hpow := HighUnitSieve.source_small_power hN2 hd (show δ < 1 / 2 by linarith)
  have hZ1 : (1 : ℝ) ≤ Z := one_le_sqrt.mpr (one_le_rpow
    (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith : 0 ≤ 1 / 2 - δ))
  have hs := labelled_small_from_output (Z := Z) (originalNonunitFamily j N δ high)
    (by positivity : (0 : ℝ) ≤ 40 ^ 7) (sqrt_nonneg _)
    (fun ell _ => original_nonunit_weightAt j hN2 hd hh high ell)
  calc
    _ ≤ (40 : ℝ) ^ 7 * (Z + 1) := hs
    _ ≤ (2 * (40 : ℝ) ^ 7) * Z := by nlinarith only [hZ1]
    _ = (2 * (40 : ℝ) ^ 7) * N * log N ^ (0 : ℕ) /
        (N : ℝ) ^ (1 - (1 / 2 - δ) / 2) := hpow.2.2.2.2.2 _
    _ ≤ _ := hp N hN

theorem original_nonunit_bad_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ high : Bool,
      (originalNonunitFamily j N δ high).noncoprimePart.primeMass ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT, hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 1 heps
    (show (0 : ℝ) < 40 ^ 7 / log 2 by positivity) (show (0 : ℝ) < 1 by norm_num)
  refine ⟨T, hT, ?_⟩
  intro N hN j high
  have hN2 : 2 ≤ N := by omega
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hb := (originalNonunitFamily j N δ high).noncoprimePart_primeMass_le_log
    (by omega) (by positivity : (0 : ℝ) ≤ 40 ^ 7)
    (fun ell _ => original_nonunit_weightAt j hN2 hd hh high ell)
  calc
    _ ≤ (40 : ℝ) ^ 7 * log N / log 2 := hb
    _ = ((40 : ℝ) ^ 7 / log 2) * N * log N ^ 1 / (N : ℝ) ^ (1 : ℝ) := by
      rw [rpow_one, pow_one]
      field_simp
    _ ≤ _ := hp N hN

end Wu18938Campaign.M4
