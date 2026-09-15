import MathlibNt.SieveTheory.LiLiuPrereqWFProgressionAdapter
import MathlibNt.SieveTheory.LiLiuPrereqWFTagCardinalityExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform envelopes for the actual transport costs

The family-size factor is the cardinality of the actual signed tags, bounded
by the proved source estimate, not by a cardinality assumption. The remaining
envelopes involve only the consumer scale and the positive power saving.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open scoped Classical

namespace TransportAbsorption

theorem log_nat_le {T N : ℕ} (hTN : T ≤ N) :
    Real.log (T : ℝ) ≤ Real.log (N : ℝ) := by
  by_cases hT : T = 0
  · simpa [hT] using Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT)
      (by exact_mod_cast hTN)

theorem floor_log_bound {Q : ℝ} {N : ℕ} (hQ : Q ≤ N)
    (hN : 1 ≤ Real.log (N : ℝ)) :
    0 ≤ 1 + Real.log (⌊Q⌋₊ : ℝ) ∧
      1 + Real.log (⌊Q⌋₊ : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have hf : ⌊Q⌋₊ ≤ N := Nat.floor_le_of_le hQ
  have hl := log_nat_le hf
  constructor
  · linarith [Real.log_natCast_nonneg ⌊Q⌋₊]
  · linarith

/-- A fixed multiple of any real logarithmic power is eventually smaller
than any positive power. The constant may in particular be exponential in ε⁻³. -/
theorem eventually_log_power_budget (C A : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in Filter.atTop, C * Real.log x ^ A ≤ x ^ s := by
  have h := ((isLittleO_log_rpow_rpow_atTop A hs).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have habs : C * Real.log x ^ A ≤ |C * Real.log x ^ A| := le_abs_self _
  simpa only [Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hx0 s)] using habs.trans hx

end TransportAbsorption

/-- A consumer-scale envelope with the actual J already paid. It is uniform
in the side, prime carrier, and labelling; no primality premise is needed. -/
theorem fullModulusTransportCost_le_power_envelope (upper : Bool) (P : Finset ℕ)
    {D ε σ : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8) (N : ℕ)
    (hN : 1 ≤ Real.log (N : ℝ)) (hQ : D ^ (1 + ε + ε ^ 9) ≤ N)
    (hpower : (N : ℝ) ^ σ ≤ D ^ (ε ^ 2))
    {X : ℝ} (hX0 : 0 ≤ X) (hXN : X ≤ N) :
    fullModulusTransportCost upper P D ε label N X ≤
      32 * Real.exp (8 * (ε⁻¹) ^ 3) * N * Real.log (N : ℝ) ^ 2 /
        (N : ℝ) ^ σ := by
  have hN0 : (0 : ℝ) < N := by
    by_contra hn
    have hz : N = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg N))
    norm_num [hz] at hN
  have hden := Real.rpow_pos_of_pos hN0 σ
  have hlog := TransportAbsorption.floor_log_bound hQ hN
  have hJ := (signedTags_card_lt_exp_source upper P label hD hε hεsmall).le
  have hsquare := pow_le_pow_left₀ hlog.1 hlog.2 2
  have hdiv : 4 / D ^ (ε ^ 2) ≤ 4 / (N : ℝ) ^ σ :=
    div_le_div_of_nonneg_left (by norm_num) hden hpower
  unfold fullModulusTransportCost
  rw [abs_of_nonneg hX0]
  calc
    _ ≤ Real.exp (8 * (ε⁻¹) ^ 3) *
        (((N : ℝ) + N) * ((4 / (N : ℝ) ^ σ) *
          (2 * Real.log (N : ℝ)) ^ 2)) := by
      gcongr
    _ = _ := by ring

/-- With the exact mass `X = #I`, the prime correction is at most J log⁴ N.
The estimate concerns the actual cost, not a distribution discrepancy. -/
theorem primeProgressionTransportCost_le_power_envelope (upper : Bool) (P : Finset ℕ)
    {D ε σ : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8) (I : Finset ℕ) (N : ℕ)
    (hI : ∀ p ∈ I, p < N) (hN : 1 ≤ Real.log (N : ℝ))
    (hQ : D ^ (1 + ε + ε ^ 9) ≤ N)
    (hpower : (N : ℝ) ^ σ ≤ D ^ (ε ^ 2)) :
    primeProgressionTransportCost upper P D ε label I N I.card ≤
      32 * Real.exp (8 * (ε⁻¹) ^ 3) * N * Real.log (N : ℝ) ^ 2 /
        (N : ℝ) ^ σ +
      16 * Real.exp (8 * (ε⁻¹) ^ 3) * Real.log (N : ℝ) ^ 4 := by
  have hcard : I.card ≤ N := by
    simpa using Finset.card_le_card
      (show I ⊆ Finset.range N from fun p hp => Finset.mem_range.mpr (hI p hp))
  have hfull := fullModulusTransportCost_le_power_envelope upper P label hD hε hεsmall
    N hN hQ hpower (Nat.cast_nonneg I.card) (by exact_mod_cast hcard)
  have hJ := (signedTags_card_lt_exp_source upper P label hD hε hεsmall).le
  have hlog := TransportAbsorption.floor_log_bound hQ hN
  have hHN : PrimeSquareMass.harmonicSum N ≤ 2 * Real.log (N : ℝ) := by
    linarith [PrimeSquareMass.harmonicSum_le_one_add_log N]
  have hHT : PrimeSquareMass.harmonicSum ⌊D ^ (1 + ε + ε ^ 9)⌋₊ ≤
      2 * Real.log (N : ℝ) :=
    (PrimeSquareMass.harmonicSum_le_one_add_log _).trans hlog.2
  unfold primeProgressionTransportCost
  simp only [sub_self, abs_zero, zero_add]
  refine add_le_add hfull ?_
  calc
    _ ≤ Real.exp (8 * (ε⁻¹) ^ 3) *
        ((2 * Real.log (N : ℝ)) ^ 2 * (2 * Real.log (N : ℝ)) ^ 2) := by
      gcongr
      all_goals exact PrimeSquareMass.harmonicSum_nonneg _
    _ = _ := by ring

#check fullModulusTransportCost_le_power_envelope
#print axioms fullModulusTransportCost_le_power_envelope
#check primeProgressionTransportCost_le_power_envelope
#print axioms primeProgressionTransportCost_le_power_envelope

end MathlibNt.SieveTheory.LiLiuPrereqWF
