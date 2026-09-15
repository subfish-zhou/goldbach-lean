import Wu18938Campaign.M1.Confirmed.ClassicalLeaves

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real Filter
open scoped Classical Topology

theorem labelled_small_bound {α : Type*} {N : ℕ} (L : LabelledPhysical.Family α N)
    {G Z : ℝ} (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hout : ∀ ell : ℕ, ell.Prime → L.weightAt ell ≤ G) :
    L.small Z ≤ G * (Z + 1) := by
  let S := (range (N + 1)).filter (fun (ell : ℕ) => ell.Prime ∧ (ell : ℝ) < Z)
  have he : L.small Z = ∑ ell ∈ S, L.weightAt ell := by
    have h := L.output_test (fun ell => if ell.Prime ∧ (ell : ℝ) < Z then 1 else 0)
    simpa only [LabelledPhysical.Family.small, S, sum_filter, card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum,
      mul_ite, mul_one, mul_zero] using h.symm
  have hsub : S ⊆ range (⌊Z⌋₊ + 1) := by
    intro ell hell
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hZ).mpr
      (mem_filter.mp hell).2.2.le))
  calc
    _ = ∑ ell ∈ S, L.weightAt ell := he
    _ ≤ ∑ _ell ∈ S, G := sum_le_sum (fun ell hell => hout ell (mem_filter.mp hell).2.1)
    _ = G * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ G * ((⌊Z⌋₊ + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left
      (by exact_mod_cast (show S.card ≤ ⌊Z⌋₊ + 1 by simpa using card_le_card hsub)) hG
    _ ≤ _ := by
      push_cast
      exact mul_le_mul_of_nonneg_left (add_le_add (Nat.floor_le hZ) le_rfl) hG

theorem roughBox_labelled_density (m : ℕ) {η δ κ F G ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hκ : 0 < κ) (hF : 0 < F) (hG : 0 < G) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ (α : Type) (L : LabelledPhysical.Family α N),
      (∀ x ∈ L.labels, (N : ℝ) ^ κ ≤ L.cofactor x ∧
        (L.cofactor x : ℝ) ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ x ∈ L.labels, 1 ≤ L.weight x) →
      (∀ e, (∑ x ∈ L.layerFibre e, L.weight x) ≤ F) →
      (∀ x ∈ L.labels, ∀ q : ℕ, q.Prime → q ∣ L.cofactor x → q.Coprime N →
        (N : ℝ) ^ κ ≤ (q : ℝ)) →
      (∀ ell : ℕ, ell.Prime → L.weightAt ell ≤ G) →
      L.primeMass ≤ L.mass *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have he3 : 0 < ε / 3 := by positivity
  obtain ⟨T0, hT04, hR1⟩ := roughBox_R1_relative m hη hδ he3 hκ hF.le
  obtain ⟨C, hC, hEuler⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  obtain ⟨T1, _, hpayR2⟩ := roughBox_absolute_power_relative m 5 hη hδ he3
    (show 0 < 2 * C * F / log 2 by positivity) hκ
  obtain ⟨T2, _, hpaysmall⟩ := roughBox_absolute_power_relative m 0 hη hδ he3
    (show 0 < 2 * G by positivity) (show 0 < 1 - (1 / 2 - δ) / 2 by linarith)
  obtain ⟨T3, _, hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  obtain ⟨T4, hlogT⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 (max T1 (max T2 (max T3 T4))), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb α L hgeom hweight hfibre hrough hout
  have hN2 : 2 ≤ N := by omega
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let D := ⌊Q⌋₊ + 1
  let Z := sqrt Q
  have hg := omega3_source_sieve_geometry hN2 hδ hδhi
  have hlog1 := hlogT N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  have hmod : ∀ q ∈ omega3SieveModuli N D Z, q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    dsimp only [D, Q] at hqd
    omega
  have hr := hEuler N (by omega) α L D Z ((N : ℝ) ^ κ) F hg.2.2.2.1
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _) hF.le hmod hrough hfibre
  have hr2 : L.R2 D Z ≤ (ε / 3) *
      boxTheta N Q (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ C * F * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ κ * log 2)) := hr
      _ ≤ C * F * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ κ * log 2)) := by
        gcongr
        linarith
      _ = (2 * C * F / log 2) * N * log N ^ 5 / (N : ℝ) ^ κ := by ring
      _ ≤ _ := hpayR2 N (by omega) i Δ V hb
  have hpow := HighUnitSieve.source_small_power hN2 hδ hδhi
  have hZ1 : (1 : ℝ) ≤ Z := one_le_sqrt.mpr (one_le_rpow
    (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith : 0 ≤ 1 / 2 - δ))
  have hs : L.small Z ≤ (ε / 3) * boxTheta N Q (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ G * (Z + 1) := labelled_small_bound L hG.le (sqrt_nonneg _) hout
      _ ≤ (2 * G) * Z := by nlinarith only [hZ1, hG]
      _ = (2 * G) * N * log N ^ (0 : ℕ) /
          (N : ℝ) ^ (1 - (1 / 2 - δ) / 2) := hpow.2.2.2.2.2 _
      _ ≤ _ := hpaysmall N (by omega) i Δ V hb
  have hf := L.prime_upper_finite heven D Z hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hr1 := hR1 N (by omega) i Δ V hb α L hgeom hweight hfibre Z
  have hx : 0 ≤ L.mass := sum_nonneg
    (fun x hx => mul_nonneg (L.weight_nonneg x hx) (Nat.cast_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (hden N (by omega) heven) hx
  change L.mass * ordinaryRosserMainSum true N 1 D Z ≤ _ at hm
  dsimp only [Q, D, Z] at *
  nlinarith only [hf, hr1, hr2, hs, hm]

end Wu18938Campaign.M1.Confirmed
