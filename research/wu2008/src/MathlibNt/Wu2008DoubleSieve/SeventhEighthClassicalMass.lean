import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalDistribution
import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalGeometry
import MathlibNt.Wu2008DoubleSieve.NinthMainMassPNT

/-!
# Actual seventh/eighth profile mass and sharp global-scale PNT transfer

The mass contains all prime r in [b,(N-1)/(ab)], not only prime outputs.
The factor 1/(1-t-v) is derived from log(N/(ab)); it occurs only once.
This is the sharp PNT predecessor of triangular quadrature, not its conclusion.
-/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Set Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

noncomputable def classicalProfile (N : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  omega3ProfilePrimes N ((p.2 : ℝ) - 1) (ninthProfileUpper N (ninthPairProduct p))
noncomputable def classicalMass (N : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ S, ((classicalProfile N p).card : ℝ)
noncomputable def classicalPairSum (N : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ S,
    (1 / (1 - ninthMainCoordinate N p.1 - ninthMainCoordinate N p.2)) /
      ((p.1 : ℝ) * p.2)

theorem classicalProfile_card_le_primePi {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    ((classicalProfile N p).card : ℝ) ≤ primePi ((N : ℝ) / ninthPairProduct p) := by
  obtain ⟨ha, hb, _, _, hs, _⟩ := hS p hp
  have hN : 0 < N := by omega
  have hm : 0 < ninthPairProduct p := Nat.mul_pos ha.pos hb.pos
  have hm0 : (0 : ℝ) < ninthPairProduct p := by exact_mod_cast hm
  have hsub : classicalProfile N p ⊆
      (Finset.Icc 0 ⌊(N : ℝ) / ninthPairProduct p⌋₊).filter Nat.Prime := by
    intro r hr
    obtain ⟨_, hrp, _, hru⟩ := mem_filter.mp hr
    have hsize := (ninthProfileUpper_nat_iff hN hm).mp hru
    have hsR : (ninthPairProduct p : ℝ) * r ≤ N := by exact_mod_cast hsize.le
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor
      ((le_div_iff₀ hm0).mpr (by simpa only [mul_comm] using hsR))⟩, hrp⟩
  calc
    _ ≤ (((Finset.Icc 0 ⌊(N : ℝ) / ninthPairProduct p⌋₊).filter Nat.Prime).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = _ := by
      rw [primePi_eq_sum_indicator]
      simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem classicalPair_prefix_lower {N : ℕ} (hN : 1 < N) {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) :
    (N : ℝ) ^ alpha ≤ (N : ℝ) / ninthPairProduct p := by
  obtain ⟨ha, hb, _⟩ := hS p hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < ninthPairProduct p := by exact_mod_cast Nat.mul_pos ha.pos hb.pos
  apply (le_div_iff₀ hm0).mpr
  calc
    (N : ℝ) ^ alpha * ninthPairProduct p ≤
        (N : ℝ) ^ alpha * (N : ℝ) ^ (1 - alpha) :=
      mul_le_mul_of_nonneg_left (classicalPair_balanced hN hS hp).2 (rpow_nonneg hN0.le _)
    _ = N := by rw [← rpow_add hN0, add_sub_cancel, rpow_one]

/-- The actual accepted PNT envelope supplies the uniform estimate. -/
theorem classicalProfile_sharp_prefix_uniform {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset (ℕ × ℕ), ClassicalPairGeometry N S →
      ∀ p ∈ S, ((classicalProfile N p).card : ℝ) ≤
        (1 + τ) * ((N : ℝ) / ninthPairProduct p / log ((N : ℝ) / ninthPairProduct p)) := by
  have hwTop : Tendsto (fun N : ℕ => (N : ℝ) ^ alpha) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [alpha] : 0 < alpha)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hwTop.eventually (eventually_ge_atTop primeErrorStart),
    hwTop.eventually (eventually_ge_atTop (2 : ℝ)),
    (tendsto_primeErrorEnvelope.comp hwTop).eventually (gt_mem_nhds hτ)]
    with N hN hstart htwo henv
  intro S hS p hp
  have hx := classicalPair_prefix_lower (by omega) hS hp
  have hx2 := htwo.trans hx
  have hx0 : 0 < (N : ℝ) / ninthPairProduct p := by linarith
  have hlog : 0 < log ((N : ℝ) / ninthPairProduct p) := log_pos (by linarith)
  have hpnt := primePi_error_le hstart hx
  have he := (le_abs_self _).trans hpnt
  have herr := mul_le_mul_of_nonneg_right henv.le (div_nonneg hx0.le hlog.le)
  have hprefix := classicalProfile_card_le_primePi hS hp
  dsimp only [Function.comp_apply] at herr
  nlinarith

/-- Exact normalization at the original N scale, with no extra reciprocal. -/
theorem classical_pair_prefix_normalization {N a b : ℕ} (hN : 1 < N)
    (ha : a.Prime) (hb : b.Prime) :
    (N : ℝ) / (a * b : ℕ) / log ((N : ℝ) / (a * b : ℕ)) =
      ((N : ℝ) / log N) *
        ((1 / (1 - ninthMainCoordinate N a - ninthMainCoordinate N b)) /
          ((a : ℝ) * b)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.pos
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.pos
  have he : log ((N : ℝ) / (a * b : ℕ)) =
      log N * (1 - ninthMainCoordinate N a - ninthMainCoordinate N b) := by
    simp only [Nat.cast_mul]
    rw [log_div hN0.ne' (mul_pos ha0 hb0).ne', log_mul ha0.ne' hb0.ne']
    unfold ninthMainCoordinate
    field_simp
    ring
  rw [he]
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- No PNT, distribution or target mass bound is assumed by the caller. -/
theorem classicalMass_sharp_pair_bound {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset (ℕ × ℕ), ClassicalPairGeometry N S →
      classicalMass N S ≤ (1 + τ) * ((N : ℝ) / log N) * classicalPairSum N S := by
  filter_upwards [classicalProfile_sharp_prefix_uniform hτ,
    eventually_ge_atTop (2 : ℕ)] with N hpnt hN
  intro S hS
  unfold classicalMass
  calc
    _ ≤ ∑ p ∈ S, (1 + τ) * ((N : ℝ) / log N) *
        ((1 / (1 - ninthMainCoordinate N p.1 - ninthMainCoordinate N p.2)) /
          ((p.1 : ℝ) * p.2)) := by
      apply sum_le_sum
      intro p hp
      have h := hpnt S hS p hp
      obtain ⟨ha, hb, _⟩ := hS p hp
      change _ ≤ (1 + τ) * ((N : ℝ) / (p.1 * p.2 : ℕ) /
        log ((N : ℝ) / (p.1 * p.2 : ℕ))) at h
      rw [classical_pair_prefix_normalization (by omega) ha hb] at h
      simpa only [mul_assoc] using h
    _ = _ := by rw [← mul_sum]; rfl

/-- Common threshold for the actual two profile masses. -/
theorem seventh_eighth_mass_sharp_pair_bound {τ : ℝ} (hτ : 0 < τ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      classicalMass N (seventhPairs N) ≤
        (1 + τ) * ((N : ℝ) / log N) * classicalPairSum N (seventhPairs N) ∧
      classicalMass N (eighthPairs N) ≤
        (1 + τ) * ((N : ℝ) / log N) * classicalPairSum N (eighthPairs N) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (classicalMass_sharp_pair_bound hτ)
  refine ⟨max T 512, le_max_right _ _, ?_⟩
  intro N hN
  have h512 := (le_max_right T 512).trans hN
  have h := hT N ((le_max_left T 512).trans hN)
  exact ⟨h _ (seventh_classicalPairGeometry h512), h _ (eighth_classicalPairGeometry h512)⟩

end Wu2008DoubleSieve.SeventhEighth
