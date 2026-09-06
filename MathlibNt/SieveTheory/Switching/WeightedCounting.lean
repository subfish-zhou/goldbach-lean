import MathlibNt.SieveTheory.Switching.MainTerm

/-!
# Weighted counting bridges and prime-power penalties

Corrected good and bad candidates give an exact counting bridge. Explicit
Mertens bounds, Jurkat--Richert integral coefficients, and proper-prime-power
estimates reduce positivity to stated uniform analytic inputs.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- The historical lower-sieve candidates transfer safely to the corrected
candidate set once the unit boundary is removed.  This is a finite inclusion:
it carries no historical switching or Omega estimate. -/
theorem chenWCandidate_mem_corrected_of_two_le {N p : ℕ}
    (hp : p ∈ chenWCandidates N) (hcomp : 2 ≤ N - p) :
    p ∈ correctedChenCandidates N := by
  simp only [chenWCandidates, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hp_lt, hp_prime, hsmall, -⟩ := hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp_lt, hp_prime, hcomp, ?_⟩
  intro r hr_prime hr_lt
  let z := Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ))
  by_cases hz_small : z ≤ 2
  · have hmax : max 2 z = 2 := max_eq_left hz_small
    have hr_lt_two : r < 2 := by
      simpa only [correctedChenZ, z, hmax] using hr_lt
    exfalso
    exact (not_lt_of_ge hr_prime.two_le) hr_lt_two
  · have hz_two : 2 < z := by omega
    have hmax : max 2 z = z := max_eq_right (by omega)
    apply hsmall r hr_prime
    have hr_lt_z : r < z := by
      simpa only [correctedChenZ, z, hmax] using hr_lt
    omega

/-- Historical lower-sieve candidates away from the unit boundary. -/
noncomputable def chenWNonUnitCandidates (N : ℕ) : Finset ℕ :=
  (chenWCandidates N).filter (fun p => 2 ≤ N - p)

/-- The non-unit historical lower-sieve fibre is contained in the corrected
candidate set. -/
theorem chenWNonUnitCandidates_subset_correctedChenCandidates (N : ℕ) :
    chenWNonUnitCandidates N ⊆ correctedChenCandidates N := by
  intro p hp
  exact chenWCandidate_mem_corrected_of_two_le
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

/-- The historical W-count differs from a corrected-candidate lower bound by
at most its explicitly isolated unit fibre. -/
theorem chenWCandidates_card_le_correctedChenCandidates_card_add_one (N : ℕ) :
    (chenWCandidates N).card ≤ (correctedChenCandidates N).card + 1 := by
  have hcover : chenWCandidates N ⊆ chenWNonUnitCandidates N ∪ chenUnitCandidates N := by
    intro p hp
    have hp_range : p < N := by
      simpa only [chenWCandidates, Finset.mem_filter, Finset.mem_range] using
        (Finset.mem_filter.mp hp).1
    have hcomp_pos : 0 < N - p := by omega
    by_cases hunit : N - p = 1
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hunit⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  calc
    (chenWCandidates N).card ≤ (chenWNonUnitCandidates N ∪ chenUnitCandidates N).card :=
      Finset.card_le_card hcover
    _ ≤ (chenWNonUnitCandidates N).card + (chenUnitCandidates N).card :=
      Finset.card_union_le _ _
    _ ≤ (correctedChenCandidates N).card + 1 :=
      Nat.add_le_add
        (Finset.card_le_card (chenWNonUnitCandidates_subset_correctedChenCandidates N))
        (chenUnitCandidates_card_le_one N)

/-- Corrected candidates that already give a prime-plus-at-most-two-almost-
prime representation. -/
noncomputable def correctedChenGoodCandidates (N : ℕ) : Finset ℕ :=
  (correctedChenCandidates N).filter
    (fun p => Nat.IsAtMostAlmostPrime 2 (N - p))

/-- The bad fibre of the corrected candidate set.  The planned replacement
Omega must supply a multiplicity-correct penalty for every member of this
set. -/
noncomputable def correctedChenBadCandidates (N : ℕ) : Finset ℕ :=
  (correctedChenCandidates N).filter
    (fun p => ¬ Nat.IsAtMostAlmostPrime 2 (N - p))

/-- The explicit penalty attached to a corrected candidate.  It records both
prime-factor multiplicities in the medium interval and canonical
medium/large/large triple witnesses. -/
noncomputable def correctedChenPenalty (N p : ℕ) : ℝ :=
  primePowerSum (N - p) (correctedChenZ N) (correctedChenY N) +
    tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)

/-- The replacement switching sum associated with the corrected candidates.
Unlike the historical `chenOmega`, its factor multiplicity is explicit.  No
analytic upper bound or counting bridge is claimed for it yet. -/
noncomputable def correctedChenOmega (N : ℕ) : ℝ :=
  (correctedChenCandidates N).sum (correctedChenPenalty N)

/-- Final positivity reduction from the lower-bound identity: if the main term `X·V(N)` is strictly greater than
`errSum(1) + Ω/2`, the corrected count is positive.

This is the complete lower-bound reduction for `CorrectedChenAnalyticPositivity`: the three analytic inputs
(the Mertens lower bound for `V(N)`, control of `errSum`, and the Ω upper bound)
are ultimately used only to establish this explicit real inequality. -/
theorem correctedChenPositivity_of_mainTerm_beats_error (N : ℕ)
    (hV : (correctedChenBoundingSieve N).errSum (fun _ => 1) +
        correctedChenOmega N / 2 <
      (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N) :
    0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 := by
  have hlow := correctedChenCandidates_card_ge_X_mul_sieveProduct_sub_errSum N
  linarith

/-- The corrected penalty is exactly the amount subtracted by the existing
Chen weight.  This gives a concrete interpretation to the future `/ 2` in a
switching bridge. -/
theorem chenWeight_eq_one_sub_correctedChenPenalty (N p : ℕ) :
    chenWeight (N - p) (correctedChenZ N) (correctedChenY N) =
      1 - correctedChenPenalty N p / 2 := by
  unfold chenWeight correctedChenPenalty
  ring

/-- A bad corrected candidate has penalty at least two, provided the cutoff
parameters cover its complementary number below the cube scale.  This is the
finite multiplicity fact that will justify `/ 2` in the replacement switching
bridge. -/
theorem correctedChenBad_penalty_ge_two {N p : ℕ}
    (hp : p ∈ correctedChenBadCandidates N)
    (hzy : correctedChenZ N < correctedChenY N)
    (hcube : (N - p : ℝ) < (correctedChenY N : ℝ) ^ 3) :
    (2 : ℝ) ≤ correctedChenPenalty N p := by
  rcases Finset.mem_filter.mp hp with ⟨hcandidate, hbad⟩
  simp only [correctedChenCandidates, Finset.mem_filter, Finset.mem_range] at hcandidate
  obtain ⟨hp_lt, _, hq_two, hcoprime⟩ := hcandidate
  have hcube' : ((N - p : ℕ) : ℝ) < (correctedChenY N : ℝ) ^ 3 := by
    rw [Nat.cast_sub (by omega : p ≤ N)]
    exact hcube
  have hz : 2 ≤ correctedChenZ N := by
    simp only [correctedChenZ]
    exact le_max_left _ _
  by_contra hpen
  have hpen_lt : correctedChenPenalty N p < 2 := by linarith
  have hweight :
      0 < chenWeight (N - p) (correctedChenZ N) (correctedChenY N) := by
    rw [chenWeight_eq_one_sub_correctedChenPenalty]
    linarith
  rcases chenWeight_pos_implies_semiprime (N - p)
      (correctedChenZ N) (correctedChenY N) hz hzy (by omega) hcube' hcoprime hweight with
    hunit | hprime | ⟨a, b, ha, hb, -, -, hproduct⟩
  · omega
  · exact hbad (hprime.isAlmostPrime_one.isAtMost (by decide : (1 : ℕ) ≤ 2))
  · apply hbad
    rw [hproduct]
    exact ha.mul_isAlmostPrime_two hb |>.isAtMost (by decide : (2 : ℕ) ≤ 2)

/-- The corrected finite switching bridge, conditional only on the elementary
cutoff facts needed by the weight lemma.  Its `/ 2` is justified by the
explicit bad-fibre penalty, not by the obsolete historical Omega count. -/
theorem corrected_counting_bridge (N : ℕ)
    (hzy : correctedChenZ N < correctedChenY N)
    (hcube : ∀ p ∈ correctedChenCandidates N,
      (N - p : ℝ) < (correctedChenY N : ℝ) ^ 3) :
    ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
      ((correctedChenGoodCandidates N).card : ℝ) := by
  let C := correctedChenCandidates N
  let G := correctedChenGoodCandidates N
  let B := correctedChenBadCandidates N
  have hpoint : ∀ p ∈ C,
      chenWeight (N - p) (correctedChenZ N) (correctedChenY N) ≤
        if p ∈ G then 1 else 0 := by
    intro p hp
    by_cases hgood : p ∈ G
    · simp only [hgood, ite_true]
      rw [chenWeight_eq_one_sub_correctedChenPenalty]
      have hpen : 0 ≤ correctedChenPenalty N p := by
        unfold correctedChenPenalty primePowerSum tripleFactorCount
        apply add_nonneg
        · exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
        · exact Nat.cast_nonneg _
      linarith
    · simp only [hgood, ite_false]
      have hbad : p ∈ B := by
        apply Finset.mem_filter.mpr
        refine ⟨hp, ?_⟩
        intro halmost
        apply hgood
        exact Finset.mem_filter.mpr ⟨hp, halmost⟩
      have hpen : (2 : ℝ) ≤ correctedChenPenalty N p := by
        simpa only [B, C] using correctedChenBad_penalty_ge_two hbad hzy (hcube p hp)
      rw [chenWeight_eq_one_sub_correctedChenPenalty]
      linarith
  have hsum := Finset.sum_le_sum (fun p hp => hpoint p hp)
  have hfilter : C.filter (fun p => p ∈ G) = G := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      exact hp.2
    · intro hp
      exact ⟨Finset.filter_subset _ _ hp, hp⟩
  have hgood_sum : C.sum (fun p => if p ∈ G then (1 : ℝ) else 0) = G.card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hweight_sum :
      C.sum (fun p => chenWeight (N - p) (correctedChenZ N) (correctedChenY N)) =
        (C.card : ℝ) - correctedChenOmega N / 2 := by
    simp only [chenWeight_eq_one_sub_correctedChenPenalty]
    rw [Finset.sum_sub_distrib]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    simp [C, correctedChenOmega]
  rw [hweight_sum] at hsum
  simpa only [hgood_sum] using hsum

/-- Every corrected candidate lies in exactly one of the good and bad fibres.
This is the finite partition on which the replacement counting bridge will be
built. -/
theorem mem_correctedChenGood_or_bad {N p : ℕ}
    (hp : p ∈ correctedChenCandidates N) :
    p ∈ correctedChenGoodCandidates N ∨ p ∈ correctedChenBadCandidates N := by
  by_cases hgood : Nat.IsAtMostAlmostPrime 2 (N - p)
  · exact Or.inl <| Finset.mem_filter.mpr ⟨hp, hgood⟩
  · exact Or.inr <| Finset.mem_filter.mpr ⟨hp, hgood⟩

/-- Corrected good candidates are genuine good representations in the public
Chen statement. -/
theorem correctedChenGoodCandidates_subset_goodRepresentations (N : ℕ) :
    correctedChenGoodCandidates N ⊆ chenGoodRepresentations N := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hcandidate, halmost⟩
  simp only [correctedChenCandidates, Finset.mem_filter, Finset.mem_range] at hcandidate
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range]
  exact ⟨hcandidate.1, hcandidate.2.1, hcandidate.2.2.1, halmost⟩

/-- The two elementary scale facts required by the corrected finite switching
bridge.  Keeping them as a named predicate cleanly separates rounding/cutoff
analysis from the purely finite multiplicity argument. -/
def CorrectedChenCutoffValid (N : ℕ) : Prop :=
  correctedChenZ N < correctedChenY N ∧
    (N : ℝ) ≤ (correctedChenY N : ℝ) ^ 3

/-- Ceiling rounding alone supplies the cube-scale half of the corrected
cutoff predicate, for every natural input. -/
theorem correctedChen_cube_scale (N : ℕ) :
    (N : ℝ) ≤ (correctedChenY N : ℝ) ^ 3 := by
  have hceil : (N : ℝ) ^ (1 / 3 : ℝ) ≤ (correctedChenY N : ℝ) := by
    simpa only [correctedChenY] using Nat.le_ceil ((N : ℝ) ^ (1 / 3 : ℝ))
  have hbase : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    (N : ℝ) = ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    _ ≤ (correctedChenY N : ℝ) ^ 3 := pow_le_pow_left₀ hbase hceil 3

/-- Apart from the harmless `max 2`, the lower cutoff is strictly below the
upper cutoff as soon as the base exceeds one. -/
theorem correctedChen_floorZ_lt_y {N : ℕ} (hN : 1 < (N : ℝ)) :
    Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) < correctedChenY N := by
  have hpow : (N : ℝ) ^ (1 / 10 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hN
    norm_num
  simpa only [correctedChenY] using
    Nat.floor_lt_ceil_of_lt_of_pos hpow
      (Real.rpow_pos_of_pos (by linarith : 0 < (N : ℝ)) _)

/-- The corrected cutoff predicate follows from a single concrete lower-root
condition.  The remaining threshold task is therefore the elementary claim
`2 < N^(1/3)`, rather than any switching-counting statement. -/
theorem correctedChen_cutoffValid_of_root_gt_two {N : ℕ}
    (hroot : (2 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ)) :
    CorrectedChenCutoffValid N := by
  have hN : 1 < (N : ℝ) := by
    have hroot_pos : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := by linarith
    by_contra h
    have hN_nonpos : (N : ℝ) ≤ 1 := le_of_not_gt h
    have hpow_le : (N : ℝ) ^ (1 / 3 : ℝ) ≤ 1 :=
      Real.rpow_le_one (Nat.cast_nonneg N) hN_nonpos (by norm_num)
    linarith
  refine ⟨?_, correctedChen_cube_scale N⟩
  unfold correctedChenZ
  apply max_lt
  · simpa only [correctedChenY] using (Nat.lt_ceil.mpr hroot)
  · exact correctedChen_floorZ_lt_y hN

/-- The remaining lower-root condition is already valid from the concrete
threshold `N ≥ 9`.  Consequently the corrected finite counting bridge has no
unproved cutoff side condition in the range relevant to Chen's theorem. -/
theorem correctedChen_cutoffValid_of_nine_le {N : ℕ} (hN : 9 ≤ N) :
    CorrectedChenCutoffValid N := by
  apply correctedChen_cutoffValid_of_root_gt_two
  have hbase : (8 : ℝ) < N := by exact_mod_cast (show 8 < N by omega)
  have hpow := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 8) hbase
    (by norm_num : (0 : ℝ) < 1 / 3)
  have h8root : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    calc
      (8 : ℝ) ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by norm_num
      _ = ((2 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        congr 1
        exact (Real.rpow_natCast 2 3).symm
      _ = (2 : ℝ) ^ ((3 : ℝ) * (1 / 3 : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = 2 := by norm_num
  linarith

/-- The global cube-scale part of `CorrectedChenCutoffValid` supplies the
strict complementary bound for every corrected candidate, because its prime
component is positive. -/
theorem correctedChen_candidate_complement_lt_cube {N p : ℕ}
    (hscale : (N : ℝ) ≤ (correctedChenY N : ℝ) ^ 3)
    (hp : p ∈ correctedChenCandidates N) :
    (N - p : ℝ) < (correctedChenY N : ℝ) ^ 3 := by
  simp only [correctedChenCandidates, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hp_lt, hp_prime, -, -⟩ := hp
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
  linarith

/-- The corrected bridge in the public Chen representation space.  It is a
fully kernel-checked replacement for the refuted historical counting bridge,
conditional only on the cutoff predicate whose eventual validity remains an
explicit analytic/rounding task. -/
theorem corrected_counting_bridge_public {N : ℕ}
    (hcutoff : CorrectedChenCutoffValid N) :
    ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
      ((chenGoodRepresentations N).card : ℝ) := by
  have hbridge :
      ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
        ((correctedChenGoodCandidates N).card : ℝ) :=
    corrected_counting_bridge N hcutoff.1
      (fun p hp => correctedChen_candidate_complement_lt_cube hcutoff.2 hp)
  exact hbridge.trans (by
    exact_mod_cast Finset.card_le_card
      (correctedChenGoodCandidates_subset_goodRepresentations N))

/-- The corrected finite bridge in the public representation space, with its
cutoffs discharged for every `N ≥ 9`. -/
theorem corrected_counting_bridge_public_of_nine_le {N : ℕ} (hN : 9 ≤ N) :
    ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
      ((chenGoodRepresentations N).card : ℝ) :=
  corrected_counting_bridge_public (correctedChen_cutoffValid_of_nine_le hN)

/-- A positive corrected sieve difference already yields a genuine Chen
representation.  All finite switching, rounding, and boundary-fibre work is
internal to this theorem; the only future input is an analytic proof that its
left-hand side is positive. -/
theorem corrected_key_inequality_implies_chen_at {N : ℕ} (hN : 9 ≤ N)
    (hkey : 0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2) :
    ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
      Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  have hpos : 0 < ((chenGoodRepresentations N).card : ℝ) :=
    lt_of_lt_of_le hkey (corrected_counting_bridge_public_of_nine_le hN)
  have hcard : 0 < (chenGoodRepresentations N).card := by exact_mod_cast hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpprime, hq2, hqalmost⟩ := hp
  exact ⟨p, N - p, hpprime, hq2, hqalmost, by omega⟩

/-- The corrected analytic target implies Chen's theorem at the conventional
threshold.  This replaces the historical `ChenCountingBridge` assumption by
a single honest analytic positivity obligation for the new objects. -/
theorem corrected_key_inequality_implies_chen
    (hkey : ∀ N : ℕ, Even N → 1000 ≤ N →
      0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  refine ⟨1000, ?_⟩
  intro N hN_large hN_even
  exact corrected_key_inequality_implies_chen_at (by omega) (hkey N hN_even hN_large)

/-- The sole active analytic obligation for the corrected Chen development.
It deliberately speaks only about the new candidate and penalty objects; no
constant or bound from the refuted historical switching model is imported. -/
def CorrectedChenAnalyticPositivity : Prop :=
  ∀ N : ℕ, Even N → 1000 ≤ N →
    0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2
/-! ## Positivity from the uniform main-term lower bound -/

/-- Mertens lower bound with explicit constant `1/3`: `∃ M₀, ∀ m ≥ M₀, 2 ≤ m →
`(1/3)/log m ≤ primeProduct m`.

This follows from the precise Mertens estimate `|pp - e^{-γ}/log m| ≤ C/log²m` and `e^{-γ} > 1/3`,
which follows from `γ < 2/3` and `e < 3`. -/
theorem primeProduct_lower_explicit :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → 2 ≤ m →
      (1 / 3 : ℝ) / log (m : ℝ) ≤ MertensTheorem.primeProduct m := by
  obtain ⟨C, hC, hb⟩ := AnalyticNumberTheory.Mertens.primeProduct_mertens_nat
  have hγ : eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hδ : (1 / 3 : ℝ) < Real.exp (-eulerMascheroniConstant) := by
    have hmono : Real.exp (-(2 / 3 : ℝ)) < Real.exp (-eulerMascheroniConstant) :=
      Real.exp_lt_exp.mpr (by linarith)
    have he23 : Real.exp ((2 / 3 : ℝ)) < 3 := by
      exact lt_trans (Real.exp_lt_exp.mpr (by norm_num)) Real.exp_one_lt_three
    have h13 : (1 / 3 : ℝ) < Real.exp (-(2 / 3 : ℝ)) := by
      rw [Real.exp_neg]
      have h3inv : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := by norm_num
      rw [h3inv]
      exact (inv_lt_inv₀ (by norm_num : 0 < (3 : ℝ)) (Real.exp_pos _)).mpr he23
    exact lt_trans h13 hmono
  let δ : ℝ := Real.exp (-eulerMascheroniConstant) - (1 / 3 : ℝ)
  have hδpos : 0 < δ := sub_pos.mpr hδ
  let T : ℝ := C / δ
  let M₀ : ℕ := Nat.ceil (Real.exp T) + 1
  refine ⟨M₀, ?_⟩
  intro m hm h2m
  have hlog : 0 < log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hT : T < log (m : ℝ) := by
    have hce : Real.exp T ≤ (Nat.ceil (Real.exp T) : ℝ) := Nat.le_ceil (Real.exp T)
    have hcm : (Nat.ceil (Real.exp T) : ℝ) < (m : ℝ) := by
      have h1 : (Nat.ceil (Real.exp T) + 1 : ℕ) ≤ m := hm
      have h1r : ((Nat.ceil (Real.exp T) + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
      have hlt : (Nat.ceil (Real.exp T) : ℝ) < ((Nat.ceil (Real.exp T) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_self (Nat.ceil (Real.exp T)))
      exact lt_of_lt_of_le hlt h1r
    have hstrict : Real.exp T < (m : ℝ) := lt_of_le_of_lt hce hcm
    have hloglt : Real.log (Real.exp T) < log (m : ℝ) :=
      Real.log_lt_log (Real.exp_pos T) hstrict
    rwa [Real.log_exp] at hloglt
  have hCδ : C / log (m : ℝ) < δ := by
    have hposT : 0 < T := by
      dsimp [T]
      exact div_pos hC hδpos
    have hinvT : (1 / log (m : ℝ)) < 1 / T := by
      exact one_div_lt_one_div_of_lt hposT hT
    calc
      C / log (m : ℝ) = C * (1 / log (m : ℝ)) := by field_simp [hlog.ne']
      _ < C * (1 / T) := mul_lt_mul_of_pos_left hinvT hC
      _ = δ := by
        dsimp [T]
        field_simp [hδpos.ne', hC.ne']
  have hb' := hb m h2m
  have hlow : Real.exp (-eulerMascheroniConstant) / log (m : ℝ) - C / (log (m : ℝ)) ^ 2 ≤
      MertensTheorem.primeProduct m := by
    change Real.exp (-eulerMascheroniConstant) / log (m : ℝ) - C / (log (m : ℝ)) ^ 2 ≤
      AnalyticNumberTheory.Mertens.primeProduct m
    have habs1 := (abs_le.mp hb').1
    nlinarith
  have hstep : C / (log (m : ℝ)) ^ 2 <
      (Real.exp (-eulerMascheroniConstant) - 1 / 3) / log (m : ℝ) := by
    have hc2 : C / (log (m : ℝ)) ^ 2 = (C / log (m : ℝ)) / log (m : ℝ) := by field_simp [hlog.ne']
    rw [hc2]
    exact div_lt_div_of_pos_right hCδ hlog
  have hgoal : (1 / 3 : ℝ) / log (m : ℝ) <
      Real.exp (-eulerMascheroniConstant) / log (m : ℝ) - C / (log (m : ℝ)) ^ 2 := by
    have hrew : (Real.exp (-eulerMascheroniConstant) - 1 / 3) / log (m : ℝ) =
        Real.exp (-eulerMascheroniConstant) / log (m : ℝ) - (1 / 3) / log (m : ℝ) := by
      field_simp [hlog.ne']
    have hstep' : C / (log (m : ℝ)) ^ 2 <
        Real.exp (-eulerMascheroniConstant) / log (m : ℝ) - (1 / 3) / log (m : ℝ) := by
      rwa [hrew] at hstep
    nlinarith
  exact le_of_lt (lt_of_lt_of_le hgoal hlow)

/-- Sharp upper parameter estimate: `log(z-1) ≤ (1/10)·log N`. -/
theorem correctedChenZ_log_le_logN_div_ten {N : ℕ} (hN : 2 ≤ N) :
    log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ (1 / 10 : ℝ) * log (N : ℝ) := by
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _
  have hzle : (correctedChenZ N - 1 : ℕ) ≤ Nat.floor x := by
    unfold correctedChenZ
    by_cases hf : 2 ≤ Nat.floor x
    · rw [max_eq_right hf]
      exact Nat.sub_le _ _
    · have hx1 : 1 ≤ x := by
        dsimp [x]
        exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
      rw [max_eq_left (by omega : Nat.floor x ≤ 2)]
      have hfl : (1 : ℕ) ≤ Nat.floor x := by
        exact Nat.le_floor (by simpa [x] using hx1)
      change (1 : ℕ) ≤ Nat.floor x
      exact hfl
  have hlogz : 0 < ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    have hz2 : 2 ≤ correctedChenZ N := by
      unfold correctedChenZ
      exact le_max_left _ _
    have hpos : 0 < correctedChenZ N - 1 := by omega
    exact_mod_cast hpos
  have hfl0 : 0 < Nat.floor x := by
    have hz2 : 2 ≤ correctedChenZ N := by
      unfold correctedChenZ
      exact le_max_left _ _
    have h1 : (1 : ℕ) ≤ correctedChenZ N - 1 := by omega
    have : (1 : ℕ) ≤ Nat.floor x := le_trans h1 hzle
    exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) this
  calc
    log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ log ((Nat.floor x : ℕ) : ℝ) := by
      exact Real.log_le_log hlogz (by exact_mod_cast hzle)
    _ ≤ log x := by
      exact Real.log_le_log (by exact_mod_cast hfl0) (Nat.floor_le hx0)
    _ = (1 / 10 : ℝ) * log (N : ℝ) := by
      dsimp [x]
      rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < N))]

/-- General parameter estimate: for `N ≥ (k+1)^10`, `k ≤ z-1` (z = ⌈N^{1/10}⌉). -/
theorem correctedChenZ_sub_one_ge_of_N_ge {k N : ℕ} (hk : 2 ≤ k) (hN : (k + 1) ^ 10 ≤ N) :
    k ≤ correctedChenZ N - 1 := by
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have hk1 : (k + 1 : ℕ) ≤ Nat.floor x := by
    have hk1r : ((k + 1 : ℕ) : ℝ) ≤ x := by
      dsimp [x]
      have hpow : ((k + 1 : ℕ) : ℝ) ^ (10 : ℝ) ≤ (N : ℝ) := by
        have hnat : ((k + 1 : ℕ) : ℝ) ^ 10 ≤ (N : ℝ) := by
          exact_mod_cast hN
        simpa [Real.rpow_natCast] using hnat
      have hstep := Real.rpow_le_rpow (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (10 : ℝ)) hpow
        (by norm_num : 0 ≤ (1 / 10 : ℝ))
      have hrew : ((((k + 1 : ℕ) : ℝ) ^ (10 : ℝ)) ^ (1 / 10 : ℝ)) = ((k + 1 : ℕ) : ℝ) := by
        rw [← Real.rpow_mul (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ))]
        norm_num
      rwa [hrew] at hstep
    exact Nat.le_floor hk1r
  have hz : correctedChenZ N = Nat.floor x := by
    unfold correctedChenZ
    change max 2 (Nat.floor x) = Nat.floor x
    exact max_eq_right (le_trans (by omega : (2 : ℕ) ≤ k + 1) hk1)
  rw [hz]
  omega

theorem tendsto_correctedChenZ_sub_one_atTop :
    Filter.Tendsto (fun N : ℕ => correctedChenZ N - 1)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro k
  filter_upwards
      [Filter.eventually_ge_atTop ((max 2 k + 1) ^ 10)] with N hN
  exact le_trans (le_max_right 2 k)
    (correctedChenZ_sub_one_ge_of_N_ge (le_max_left 2 k) hN)

/-- The explicit ten-factor majorant for the large-prime tail tends to one. -/
theorem tendsto_correctedChenSingularSeriesTailMajorant :
    Filter.Tendsto
      (fun N : ℕ =>
        (1 + 1 / ((correctedChenZ N - 1 : ℕ) : ℝ)) ^ (10 : ℕ))
      Filter.atTop (nhds 1) := by
  have hz : Filter.Tendsto
      (fun N : ℕ => ((correctedChenZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_correctedChenZ_sub_one_atTop
  have hinv : Filter.Tendsto
      (fun N : ℕ => 1 / ((correctedChenZ N - 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    rw [show
      (fun N : ℕ => 1 / ((correctedChenZ N - 1 : ℕ) : ℝ)) =
        (fun r : ℝ => r⁻¹) ∘
          (fun N : ℕ => ((correctedChenZ N - 1 : ℕ) : ℝ)) by
      funext N
      simp only [Function.comp_apply, one_div]]
    exact tendsto_inv_atTop_zero.comp hz
  simpa using (hinv.const_add 1).pow 10

/-- Uniform comparison at the varying corrected Chen cutoff.  The genuine Liu
series is bounded by half the sieve-normalized truncation, up to any prescribed
multiplicative margin.  No fixed-source convergence statement is used. -/
theorem eventually_two_mul_liuSingularSeries_le_truncated
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      2 * SingularSeries.liuSingularSeries N ≤
        (1 + η) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) := by
  have hmajorant : ∀ᶠ N : ℕ in Filter.atTop,
      (1 + 1 / ((correctedChenZ N - 1 : ℕ) : ℝ)) ^ (10 : ℕ) ≤ 1 + η :=
    tendsto_correctedChenSingularSeriesTailMajorant.eventually
      (Iic_mem_nhds (by linarith))
  filter_upwards
      [hmajorant, Filter.eventually_ge_atTop (2 ^ 110 + 1)] with
      N hmajorantN hN
  intro hEven
  have hNbig : 2 ^ 110 < N := by omega
  have hN2 : 2 ≤ N := by omega
  have hz3 : 3 ≤ correctedChenZ N := chenZ_ge_three N hNbig
  have hz1 : 1 ≤ correctedChenZ N := by omega
  have hzleN : correctedChenZ N ≤ N + 1 :=
    chenZ_le_N_add_one N hN2
  have hsplit :=
    singularSeries_eq_trunc_mul_tail N hN2 hz1 hzleN
  have htail :=
    chenZ_tail_prod_le_vanishing N hz3
  have hcount :
      ((Finset.Ico (correctedChenZ N) (N + 1)).filter
        (fun p => p.Prime ∧ p ∣ N)).card ≤ 10 :=
    chenZ_tail_prime_count_le N N hNbig (by omega) le_rfl
  have hbase1 :
      1 ≤ 1 + 1 / ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    have hnonneg :
        0 ≤ 1 / ((correctedChenZ N - 1 : ℕ) : ℝ) := by positivity
    linarith
  have htail10 :
      ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime).prod
          (fun p => SingularSeries.localFactor p N) ≤
        (1 + 1 / ((correctedChenZ N - 1 : ℕ) : ℝ)) ^ (10 : ℕ) :=
    htail.trans (pow_le_pow_right₀ hbase1 hcount)
  have htruncpos :
      0 < SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) :=
    SingularSeries.singularSeriesTruncated_pos N (correctedChenZ N - 1)
      (by omega)
  calc
    2 * SingularSeries.liuSingularSeries N ≤
        SingularSeries.singularSeries N :=
      SingularSeries.two_mul_liuSingularSeries_le_singularSeries
        N hEven hN2
    _ = SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) *
        ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime).prod
          (fun p => SingularSeries.localFactor p N) := hsplit
    _ ≤ SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) *
        (1 + 1 / ((correctedChenZ N - 1 : ℕ) : ℝ)) ^ (10 : ℕ) :=
      mul_le_mul_of_nonneg_left htail10 htruncpos.le
    _ ≤ SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) *
        (1 + η) :=
      mul_le_mul_of_nonneg_left hmajorantN htruncpos.le
    _ = (1 + η) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) := by
      rw [singularSeriesTruncated_eq_ant]
      ring

/-- **Uniform main-term lower bound in singular-series units**: `(10/3)·𝔖_trunc·N/log²N ≤ X·V(N)`.

Combine the exact identity `X·V = X·𝔖·primeProduct(z-1)`, the Mertens lower bound
`primeProduct ≥ (1/3)/log(z-1)`, and the parameter upper bound `log(z-1) ≤ (1/10)·log N`. -/
theorem CorrectedChenMainTermLower_singularSeries_units :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (10 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
        (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N := by
  obtain ⟨M₀, hpp⟩ := primeProduct_lower_explicit
  let N₀ : ℕ := max ((M₀ + 3) ^ 10) 59049
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  have hN2 : 2 ≤ N := by
    dsimp [N₀] at hN
    omega
  have hz : 2 ≤ correctedChenZ N - 1 := correctedChenZ_sub_one_ge_two_of_large (by
    dsimp [N₀] at hN
    omega)
  have hM : M₀ ≤ correctedChenZ N - 1 := by
    have hk := correctedChenZ_sub_one_ge_of_N_ge (k := M₀ + 2) (by omega : 2 ≤ M₀ + 2) (by
      have hle : (M₀ + 3) ^ 10 ≤ N := by
        dsimp [N₀] at hN
        omega
      -- Goal: ((M₀+2)+1)^10 ≤ N, that is, (M₀+3)^10 ≤ N.
      simpa [show (M₀ + 2) + 1 = M₀ + 3 by omega] using hle)
    omega
  have hlogz : 0 < log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) < (correctedChenZ N - 1 : ℕ) := by exact_mod_cast (by omega : 1 < correctedChenZ N - 1)
    exact Real.log_pos this
  have hlogN : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hparam := correctedChenZ_log_le_logN_div_ten hN2
  have hpp' : (1 / 3 : ℝ) / log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤
      MertensTheorem.primeProduct (correctedChenZ N - 1) := hpp (correctedChenZ N - 1) hM hz
  have hparam10 : (10 : ℝ) / log (N : ℝ) ≤ 1 / log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    have hrew : log (N : ℝ) / 10 = (1 / 10 : ℝ) * log (N : ℝ) := by ring
    have hzle : log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ log (N : ℝ) / 10 := by
      rw [hrew]
      exact hparam
    have hrew2 : (10 : ℝ) / log (N : ℝ) = 1 / (log (N : ℝ) / 10) := by
      field_simp [hlogN.ne']
    rw [hrew2]
    exact one_div_le_one_div_of_le hlogz hzle
  have h10' : (10 / 3 : ℝ) / log (N : ℝ) ≤ (1 / 3 : ℝ) / log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hlogN hlogz]
    have h10z : (10 : ℝ) * log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ log (N : ℝ) := by
      nlinarith [hparam]
    nlinarith
  have h𝔖pos : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N (correctedChenZ N - 1) (by omega)
  have hseam := correctedChenSieveProduct_eq_singularSeries_mul_primeProduct N hEven
  have hX : 0 ≤ (N : ℝ) / log (N : ℝ) := div_nonneg (by positivity) (le_of_lt hlogN)
  calc
    (10 / 3 : ℝ) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2
        = (N : ℝ) / log (N : ℝ) *
            (AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              ((10 / 3 : ℝ) / log (N : ℝ))) := by
          field_simp [hlogN.ne']
    _ ≤ (N : ℝ) / log (N : ℝ) *
            (AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              ((1 / 3 : ℝ) / log ((correctedChenZ N - 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h10' (le_of_lt h𝔖pos)) hX
    _ ≤ (N : ℝ) / log (N : ℝ) *
            (AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              MertensTheorem.primeProduct (correctedChenZ N - 1)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpp' (le_of_lt h𝔖pos)) hX
    _ = (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N := by
          rw [← hseam]
          rfl

/-- **Ω upper-bound target**: uniformly, `correctedChenOmega ≤ cΩ·𝔖_trunc·N/log²N`,
with `(10/3) > cΩ/2`, so the main-term coefficient strictly exceeds the Ω/2 coefficient. -/
def CorrectedChenOmegaUpperBound : Prop :=
  ∃ cΩ : ℝ, (10 / 3 : ℝ) > cΩ / 2 ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N →
      correctedChenOmega N ≤
        cΩ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2

/-- Compatibility with the classical constant: the main-term coefficient `10/3` strictly exceeds
half the classical Ω upper-bound coefficient, `3.9404/2`. Thus the numerical condition in
`CorrectedChenOmegaUpperBound` permits `cΩ = 3.9404`, the classical constant of Chen 1973. -/
theorem omega_upper_bound_compatible_with_39404 :
    (10 / 3 : ℝ) > 3.9404 / 2 := by
  norm_num

/-- An Ω upper bound with the classical constant `3.9404`, satisfying the main-term coefficient condition, can be used directly.
This theorem makes the instantiation condition for `CorrectedChenOmegaUpperBound` explicit: it suffices to prove
`∃ N₀, ∀ N ≥ N₀ Even, correctedChenOmega N ≤ 3.9404·𝔖_trunc·N/log²N`. -/
theorem CorrectedChenOmegaUpperBound_of_39404
    (hbound : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      correctedChenOmega N ≤
        3.9404 * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2) :
    CorrectedChenOmegaUpperBound := by
  rcases hbound with ⟨N₀, hN₀⟩
  exact ⟨3.9404, omega_upper_bound_compatible_with_39404, N₀, hN₀⟩


/-- **Final assembly**: the proved uniform main-term lower bound, an Ω upper-bound input, and
weighted Pan control of `errSum` imply positivity of the corrected count for sufficiently large even numbers. -/
theorem CorrectedChenPositivity_large_of_inputs
    (hPan : ChenWeightedPanInput) (hΩ : CorrectedChenOmegaUpperBound) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 := by
  obtain ⟨N₀main, hmain⟩ := CorrectedChenMainTermLower_singularSeries_units
  obtain ⟨cΩ, hnum, N₀Ω, hΩ'⟩ := hΩ
  rcases hPan 3 (by norm_num : 0 < (3 : ℝ)) with ⟨C, hC, hbound⟩
  have hErr : ∀ N : ℕ, 1000 ≤ N → Even N →
      (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤ C * (N : ℝ) / (log (N : ℝ)) ^ 3 := by
    intro N hN hEven
    exact le_trans (correctedChenErrSum_le_weightedPanInput N) (by
      simpa [Real.rpow_natCast] using hbound N hN hEven)
  let d : ℝ := (10 / 3 : ℝ) - cΩ / 2
  have hd : 0 < d := sub_pos.mpr hnum
  let T : ℝ := 2 * C / d
  let M : ℕ := Nat.ceil (Real.exp T) + 1
  let N₀ : ℕ := max (max N₀main N₀Ω) (max (max 1000 M) 59049)
  refine ⟨N₀, ?_⟩
  intro N hN_large hN_even
  have hNmain : N₀main ≤ N := by
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN_large
  have hNΩ : N₀Ω ≤ N := by
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN_large
  have hN1000 : 1000 ≤ N := by
    exact le_trans (le_trans (le_trans (le_max_left 1000 M) (le_max_left _ _))
      (le_max_right _ _)) hN_large
  have hNM : M ≤ N := by
    exact le_trans (le_trans (le_trans (le_max_right 1000 M) (le_max_left _ _))
      (le_max_right _ _)) hN_large
  have hN59049 : 59049 ≤ N := by
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN_large
  have hlogN : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hT : T < log (N : ℝ) := by
    have hce : Real.exp T ≤ (Nat.ceil (Real.exp T) : ℝ) := Nat.le_ceil (Real.exp T)
    have hcm : (Nat.ceil (Real.exp T) : ℝ) < (N : ℝ) := by
      have h1 : (Nat.ceil (Real.exp T) + 1 : ℕ) ≤ N := hNM
      have h1r : ((Nat.ceil (Real.exp T) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      have hlt : (Nat.ceil (Real.exp T) : ℝ) < ((Nat.ceil (Real.exp T) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_self (Nat.ceil (Real.exp T)))
      exact lt_of_lt_of_le hlt h1r
    have hstrict : Real.exp T < (N : ℝ) := lt_of_le_of_lt hce hcm
    have hloglt : Real.log (Real.exp T) < log (N : ℝ) :=
      Real.log_lt_log (Real.exp_pos T) hstrict
    rwa [Real.log_exp] at hloglt
  have hCdiv : C / log (N : ℝ) < d / 2 := by
    have hT' : (2 * C) / d < log (N : ℝ) := by
      simpa [T] using hT
    have hmul := mul_lt_mul_of_pos_right hT' hd
    -- (2C/d)·d = 2C < d·log N
    have hcross : C * 2 < d * log (N : ℝ) := by
      field_simp [hd.ne'] at hmul ⊢
      nlinarith
    -- C/log N < d/2 ⟺ 2C < d·log N
    rw [div_lt_iff₀ hlogN]
    have hrew2 : (d / 2) * log (N : ℝ) = (d * log (N : ℝ)) / 2 := by ring
    rw [hrew2, lt_div_iff₀ (by norm_num : 0 < (2 : ℝ))]
    exact hcross
  have hz : 2 ≤ correctedChenZ N - 1 := correctedChenZ_sub_one_ge_two_of_large hN59049
  have h𝔖 : (1 / 2 : ℝ) ≤
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
    singularSeriesTruncated_ge_half hz
  have h𝔖pos : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N (correctedChenZ N - 1) (by omega)
  have hmainN := hmain N hNmain hN_even
  have hΩN := hΩ' N hNΩ hN_even
  have herrN := hErr N hN1000 hN_even
  have hV : (correctedChenBoundingSieve N).errSum (fun _ => 1) + correctedChenOmega N / 2 <
      (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N := by
    have hO : correctedChenOmega N / 2 ≤
        (cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := by
      have hΩ2 : correctedChenOmega N ≤
          cΩ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 := hΩN
      have hdiv2 : correctedChenOmega N / 2 ≤
          (cΩ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2) / 2 := by
        exact div_le_div_of_nonneg_right hΩ2 (by norm_num : 0 ≤ (2 : ℝ))
      have hrew : (cΩ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2) / 2 =
          (cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 := by
        field_simp
      rwa [hrew] at hdiv2
    have hsum : C * (N : ℝ) / (log (N : ℝ)) ^ 3 +
          (cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 <
        (10 / 3 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 := by
      -- C/log N < d/2 ≤ d·𝔖 ⇒ C·X/logN < d·𝔖·X
      have hd𝔖 : d / 2 ≤ d * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) := by
        have hmul := mul_le_mul_of_nonneg_left h𝔖 (le_of_lt hd)
        have hrew : d * (1 / 2 : ℝ) = d / 2 := by ring
        rwa [hrew] at hmul
      have hC𝔖 : C / log (N : ℝ) <
          d * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
        lt_of_lt_of_le hCdiv hd𝔖
      have hX2 : 0 < (N : ℝ) / (log (N : ℝ)) ^ 2 := by positivity
      have hstrict : C * (N : ℝ) / (log (N : ℝ)) ^ 3 <
          d * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 := by
        have hmul := mul_lt_mul_of_pos_right hC𝔖 hX2
        have hrewL : C * (N : ℝ) / (log (N : ℝ)) ^ 3 =
            (C / log (N : ℝ)) * ((N : ℝ) / (log (N : ℝ)) ^ 2) := by
          field_simp [hlogN.ne']
        have hrewR : d * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2 =
            (d * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)) *
              ((N : ℝ) / (log (N : ℝ)) ^ 2) := by
          field_simp [hlogN.ne']
        rw [hrewL, hrewR]
        exact hmul
      have hadd : C * (N : ℝ) / (log (N : ℝ)) ^ 3 +
            (cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2 <
          d * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2 +
            (cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2 := by
          simpa [add_comm] using (add_lt_add_right hstrict
            ((cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2))
      have hrew : d * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2 +
            (cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2 =
          (10 / 3 : ℝ) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
              (N : ℝ) / (log (N : ℝ)) ^ 2 := by
        dsimp [d]
        ring_nf
      rwa [hrew] at hadd
    have hle : (correctedChenBoundingSieve N).errSum (fun _ => 1) + correctedChenOmega N / 2 ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ 3 +
          (cΩ / 2) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            (N : ℝ) / (log (N : ℝ)) ^ 2 := by
      exact add_le_add herrN hO
    exact lt_of_lt_of_le (lt_of_le_of_lt hle hsum) hmainN
  exact correctedChenPositivity_of_mainTerm_beats_error N hV

/-- **Chen's theorem conditional on two analytic inputs**: pass from `CorrectedChenPositivity_large_of_inputs`
through `corrected_key_inequality_implies_chen_at` to the final `∃ N₀` form. -/
theorem corrected_chens_theorem_of_inputs
    (hPan : ChenWeightedPanInput) (hΩ : CorrectedChenOmegaUpperBound) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  obtain ⟨N₀', hpos⟩ := CorrectedChenPositivity_large_of_inputs hPan hΩ
  refine ⟨max N₀' 1000, ?_⟩
  intro N hN hEven
  exact corrected_key_inequality_implies_chen_at (N := N) (by omega) (hpos N (by omega) hEven)

/-

## The finite core of the Ω upper bound

The penalty `correctedChenOmega` splits into prime-power and triple-factor parts. The prime-power part
reduces to the finite count "multiplicity ≤ number of prime powers", the first step needed
for any switching-sieve Ω upper bound, complementary to the Selberg main-term identities. -/

/-- Prime-power part: `primePowerSum n z y` equals the sum of the multiplicities of primes in `[z, y)`
dividing `n`; the filter condition `∃ k ≥ 1, exactDiv q k n` is equivalent to `q ∣ n`. -/
theorem primePowerSum_eq_sum_factorization_of_dvd {n z y : ℕ} (hn : n ≠ 0) :
    primePowerSum n z y =
      (∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n),
        (n.factorization q : ℝ)) := by
  unfold primePowerSum
  have hfilter : (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧
      ∃ k : ℕ, 1 ≤ k ∧ exactDiv q k n) =
      (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n) := by
    apply Finset.filter_congr
    intro q hq
    constructor
    · intro h
      rcases h with ⟨hp, hz, hk⟩
      rcases hk with ⟨k, hk1, hkdiv⟩
      exact ⟨hp, hz, dvd_trans (by simpa using (pow_dvd_pow q (by omega : 1 ≤ k))) hkdiv.1⟩
    · intro h
      rcases h with ⟨hp, hz, hdvd⟩
      refine ⟨hp, hz, ?_⟩
      let a : ℕ := n.factorization q
      have hpow : q ^ a ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mpr le_rfl
      have hnot : ¬ q ^ (a + 1) ∣ n := by
        intro hbad
        have : a + 1 ≤ a := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp hbad
        omega
      have h1le : 1 ≤ a := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp (by simpa using hdvd)
      exact ⟨a, h1le, hpow, hnot⟩
  rw [hfilter]

/-- Multiplicity is at most the number of prime powers: `n.factorization q ≤ #{k : q^(k+1) ∣ n}`. -/
theorem factorization_le_card_pow_dvd {n q : ℕ} (hq : q.Prime) (hn : n ≠ 0) :
    n.factorization q ≤
      ((Finset.range (n + 1)).filter (fun k => q ^ (k + 1) ∣ n)).card := by
  let a : ℕ := n.factorization q
  have hle_a_n : a ≤ n := by
    by_cases ha : a = 0
    · simp [ha]
    · have hpow : q ^ a ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization hq hn).mpr le_rfl
      have hq2 : 2 ≤ q := hq.two_le
      have hlt : a < q ^ a := lt_of_lt_of_le Nat.lt_two_pow_self
        (pow_le_pow_left₀ (by norm_num) hq2 a)
      exact le_trans (le_of_lt hlt) (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpow)
  have hsubset : (Finset.range a) ⊆ (Finset.range (n + 1)).filter
      (fun k => q ^ (k + 1) ∣ n) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hk' : k < a := Finset.mem_range.mp hk
      have : k < n := lt_of_lt_of_le hk' hle_a_n
      omega
    · exact (Nat.Prime.pow_dvd_iff_le_factorization hq hn).mpr (by
        have : k + 1 ≤ a := by
          have hk' : k < a := Finset.mem_range.mp hk
          omega
        exact this)
  have hcard : (Finset.range a).card = a := Finset.card_range a
  have hle := Finset.card_le_card hsubset
  rwa [hcard] at hle

/-- Uniform finite upper bound for the prime-power part: `primePowerSum n z y ≤ Σ_{q ∈ [z,y)} Σ_k [q^(k+1) | n]`. -/
theorem primePowerSum_le_powerCount (n z y : ℕ) :
    primePowerSum n z y ≤
      ∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q),
        ∑ k ∈ Finset.range (n + 1), if q ^ (k + 1) ∣ n then (1 : ℝ) else 0 := by
  by_cases hn : n = 0
  · subst n
    unfold primePowerSum
    simp [exactDiv]
  · have hident := primePowerSum_eq_sum_factorization_of_dvd (n := n) (z := z) (y := y) hn
    rw [hident]
    have hper : ∀ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q),
        (n.factorization q : ℝ) ≤
          ∑ k ∈ Finset.range (n + 1), if q ^ (k + 1) ∣ n then (1 : ℝ) else 0 := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqr, hqp⟩
      have hcard := factorization_le_card_pow_dvd hqp.1 hn
      have hsum_eq : (∑ k ∈ Finset.range (n + 1), if q ^ (k + 1) ∣ n then (1 : ℝ) else 0) =
          ((Finset.range (n + 1)).filter (fun k => q ^ (k + 1) ∣ n)).card := by
        rw [Finset.sum_boole]
      have hle1 : (n.factorization q : ℝ) ≤
          ((Finset.range (n + 1)).filter (fun k => q ^ (k + 1) ∣ n)).card := by
        exact_mod_cast hcard
      exact le_trans hle1 (by rw [hsum_eq])
    calc
      (∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n),
          (n.factorization q : ℝ))
          ≤ ∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q),
              ∑ k ∈ Finset.range (n + 1), if q ^ (k + 1) ∣ n then (1 : ℝ) else 0 := by
            have hsub : (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n) ⊆
                (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q) := by
              intro q hq
              rcases Finset.mem_filter.mp hq with ⟨hq1, hq2⟩
              exact Finset.mem_filter.mpr ⟨hq1, hq2.1, hq2.2.1⟩
            have hle0 : (∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n),
                  (n.factorization q : ℝ)) ≤
                ∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q),
                  (n.factorization q : ℝ) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot => by positivity)
            exact le_trans hle0 (Finset.sum_le_sum hper)

/-- The prime-power part of the corrected Chen penalty. -/
noncomputable def correctedChenPrimePowerPenalty (N : ℕ) : ℝ :=
  (correctedChenCandidates N).sum
    (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N))

/-- The strict ordered-triple part of the corrected Chen penalty. -/
noncomputable def correctedChenTriplePenalty (N : ℕ) : ℝ :=
  (correctedChenCandidates N).sum
    (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N))

/-- The inner Buchstab integral occurring in both terms of Chen's equations
(26)--(27). -/
noncomputable def jurkatRichertInnerIntegral (u : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..u - 1, Real.log (t - 1) / t

/-- Chen's exact integral `J` from equation (26):
`∫₃⁴ du/u ∫₂ᵘ⁻¹ log(t-1)/t dt`. -/
noncomputable def jurkatRichertJ : ℝ :=
  ∫ u in (3 : ℝ)..4, jurkatRichertInnerIntegral u / u

/-- The inner Buchstab integral is nonnegative on the range used by Chen. -/
theorem jurkatRichertInnerIntegral_nonneg {u : ℝ} (hu3 : 3 ≤ u) :
    0 ≤ jurkatRichertInnerIntegral u := by
  unfold jurkatRichertInnerIntegral
  apply intervalIntegral.integral_nonneg (by linarith)
  intro t ht
  have htPos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hlog : 0 ≤ Real.log (t - 1) :=
    Real.log_nonneg (by linarith [ht.1])
  exact div_nonneg hlog htPos.le

/-- Chen's base Buchstab integral is nonnegative. -/
theorem jurkatRichertJ_nonneg : 0 ≤ jurkatRichertJ := by
  unfold jurkatRichertJ
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  rcases hu with ⟨hu3, _⟩
  exact div_nonneg (jurkatRichertInnerIntegral_nonneg hu3) (by linarith)

/-- Chen's exact integral `K` from equations (26)--(27), after the paper's
change of variables `u = 5 - 10α`:
`∫₃⁴ 10/[u(5-u)] du ∫₂ᵘ⁻¹ log(t-1)/t dt`. -/
noncomputable def jurkatRichertK : ℝ :=
  ∫ u in (3 : ℝ)..4,
    10 / (u * (5 - u)) * jurkatRichertInnerIntegral u

/-- Chen's varying-level Buchstab integral is nonnegative. -/
theorem jurkatRichertK_nonneg : 0 ≤ jurkatRichertK := by
  unfold jurkatRichertK
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  exact mul_nonneg
    (div_nonneg (by norm_num) (mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])))
    (jurkatRichertInnerIntegral_nonneg hu.1)

/-- A strengthened version of the elementary logarithm majorant used in Chen's
estimate of the inner Buchstab integral. -/
private lemma jurkatRichert_log_upper_bound {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    Real.log x ≤
      (x - 1) / 2 + (x - 1) / (1 + x) - (x + 1) * (x - 1) ^ 2 / 1000 := by
  let q : ℝ → ℝ := fun t => t ^ 2 - 3 * t + 3 - (t - 1) ^ 3 / 2
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog : Real.log x = ∫ t in (1 : ℝ)..x, 1 / t := by
    rw [integral_one_div_of_pos (by norm_num) hxpos]
    norm_num
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    change t ≠ 0
    rw [Set.uIcc_of_le hx1] at ht
    linarith [ht.1]
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hqint : IntervalIntegrable q volume 1 x := hqcont.intervalIntegrable _ _
  have hmono : (∫ t in (1 : ℝ)..x, 1 / t) ≤ ∫ t in (1 : ℝ)..x, q t := by
    apply intervalIntegral.integral_mono_on hx1 hinv hqint
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have ht2 : t ≤ 2 := le_trans ht.2 hx2
    have hprod : 0 ≤ (t - 1) ^ 3 * (2 - t) :=
      mul_nonneg (pow_nonneg (sub_nonneg.mpr ht.1) _) (sub_nonneg.mpr ht2)
    dsimp [q]
    rw [div_le_iff₀ htpos]
    nlinarith
  let Q : ℝ → ℝ :=
    fun t => t ^ 3 / 3 - 3 * t ^ 2 / 2 + 3 * t - (t - 1) ^ 4 / 8
  have hQ : ∀ t : ℝ, HasDerivAt Q (q t) t := by
    intro t
    dsimp [Q, q]
    have h := (((((hasDerivAt_id t).pow 3).div_const 3).sub
        ((((hasDerivAt_id t).pow 2).const_mul 3).div_const 2)).add
          ((hasDerivAt_id t).const_mul 3)).sub
            ((((hasDerivAt_id t).sub_const 1).pow 4).div_const 8)
    convert h using 1
    all_goals try rfl
    all_goals simp only [id_eq]
    all_goals ring
  have hqeval : (∫ t in (1 : ℝ)..x, q t) = Q x - Q 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t) hqint
  rw [hlog]
  calc
    (∫ t in (1 : ℝ)..x, 1 / t) ≤ ∫ t in (1 : ℝ)..x, q t := hmono
    _ = Q x - Q 1 := hqeval
    _ ≤ (x - 1) / 2 + (x - 1) / (1 + x) -
        (x + 1) * (x - 1) ^ 2 / 1000 := by
      dsimp [Q]
      have hxden : 0 < 1 + x := by linarith
      have hy2 : (x - 1) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (x - 1),
          mul_self_le_mul_self (sub_nonneg.mpr hx1) (by linarith : x - 1 ≤ 1)]
      have hy3 : 0 ≤ (x - 1) ^ 3 := pow_nonneg (sub_nonneg.mpr hx1) _
      have hp :
          0 ≤ 375 * (x - 1) ^ 3 - 253 * (x - 1) ^ 2 - 512 * (x - 1) + 1488 := by
        nlinarith
      have hid :
          ((x - 1) / 2 + (x - 1) / (1 + x) -
                (x + 1) * (x - 1) ^ 2 / 1000) -
              (x ^ 3 / 3 - 3 * x ^ 2 / 2 + 3 * x - (x - 1) ^ 4 / 8 -
                (1 ^ 3 / 3 - 3 * 1 ^ 2 / 2 + 3 * 1 - (1 - 1) ^ 4 / 8)) =
            (x - 1) ^ 2 *
                (375 * (x - 1) ^ 3 - 253 * (x - 1) ^ 2 -
                  512 * (x - 1) + 1488) /
              (3000 * (x + 1)) := by
        field_simp
        ring
      rw [← sub_nonneg, hid]
      positivity

/-- The strengthened logarithm majorant saves a cubic term in Chen's estimate
of the inner integral. -/
private lemma jurkatRichert_innerIntegral_le {u : ℝ} (hu3 : 3 ≤ u) (hu4 : u ≤ 4) :
    jurkatRichertInnerIntegral u ≤
      (u - 3 + 4 / (u - 1) - 2) / 2 - (u - 3) ^ 3 / 3000 := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  let g : ℝ → ℝ := fun t => 1 / 2 - 2 / t ^ 2 - (t - 2) ^ 2 / 1000
  have hbounds : 2 ≤ u - 1 := by linarith
  have hf : IntervalIntegrable f volume 2 (u - 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t - 1 ≠ 0
      rw [Set.uIcc_of_le hbounds] at ht
      linarith [ht.1]
    · exact continuousOn_id
    · intro t ht
      change t ≠ 0
      rw [Set.uIcc_of_le hbounds] at ht
      linarith [ht.1]
  have hg : IntervalIntegrable g volume 2 (u - 1) := by
    apply ContinuousOn.intervalIntegrable
    dsimp [g]
    apply (continuousOn_const.sub (ContinuousOn.div continuousOn_const
      (continuousOn_id.pow 2) ?_)).sub
      ((continuousOn_id.sub continuousOn_const).pow 2 |>.div_const 1000)
    intro t ht
    change t ^ 2 ≠ 0
    rw [Set.uIcc_of_le hbounds] at ht
    exact pow_ne_zero _ (by linarith [ht.1])
  have hmono : (∫ t in (2 : ℝ)..u - 1, f t) ≤ ∫ t in (2 : ℝ)..u - 1, g t := by
    apply intervalIntegral.integral_mono_on hbounds hf hg
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have ht3 : t ≤ 3 := by linarith [ht.2]
    have htpos : 0 < t := by linarith
    have hlog := jurkatRichert_log_upper_bound (x := t - 1) (by linarith) (by linarith)
    dsimp [f, g]
    apply (div_le_iff₀ htpos).2
    calc
      Real.log (t - 1) ≤
          (t - 1 - 1) / 2 + (t - 1 - 1) / (1 + (t - 1)) -
            (t - 1 + 1) * (t - 1 - 1) ^ 2 / 1000 := hlog
      _ = (1 / 2 - 2 / t ^ 2 - (t - 2) ^ 2 / 1000) * t := by
        have htne : t ≠ 0 := ne_of_gt htpos
        field_simp [htne]
        ring
  let G : ℝ → ℝ := fun t => t / 2 + 2 / t - (t - 2) ^ 3 / 3000
  have hG : ∀ t ∈ Set.uIcc (2 : ℝ) (u - 1), HasDerivAt G (g t) t := by
    intro t ht
    rw [Set.uIcc_of_le hbounds] at ht
    have htne : t ≠ 0 := by linarith [ht.1]
    dsimp [G, g]
    have h := ((((hasDerivAt_id t).div_const 2).add
        ((hasDerivAt_const t (2 : ℝ)).div (hasDerivAt_id t) htne)).sub
          ((((hasDerivAt_id t).sub_const 2).pow 3).div_const 3000))
    convert h using 1
    all_goals try rfl
    all_goals simp only [id_eq]
    all_goals field_simp [htne]
    all_goals ring
  have hgeval : (∫ t in (2 : ℝ)..u - 1, g t) = G (u - 1) - G 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hG hg
  unfold jurkatRichertInnerIntegral
  change (∫ t in (2 : ℝ)..u - 1, f t) ≤ _
  calc
    (∫ t in (2 : ℝ)..u - 1, f t) ≤ ∫ t in (2 : ℝ)..u - 1, g t := hmono
    _ = G (u - 1) - G 2 := hgeval
    _ = (u - 3 + 4 / (u - 1) - 2) / 2 - (u - 3) ^ 3 / 3000 := by
      dsimp [G]
      have hu1 : u - 1 ≠ 0 := by linarith
      field_simp [hu1]
      ring

namespace Internal

/-- The exact inner Buchstab integral is continuous on the range needed for
Chen's outer integral. -/
lemma continuousOn_jurkatRichertInnerIntegral :
    ContinuousOn jurkatRichertInnerIntegral (Set.Icc (3 : ℝ) 4) := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hf : IntervalIntegrable f volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t - 1 ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
      linarith [ht.1]
    · exact continuousOn_id
    · intro t ht
      change t ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
      linarith [ht.1]
  have hp : ContinuousOn (fun b => ∫ t in (2 : ℝ)..b, f t) (Set.Icc 2 3) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (2 : ℝ)) hf
      (by
        rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)]
        constructor <;> norm_num)
    simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using h
  unfold jurkatRichertInnerIntegral
  change ContinuousOn (fun u => (∫ t in (2 : ℝ)..u - 1, f t)) (Set.Icc 3 4)
  apply hp.comp (continuousOn_id.sub continuousOn_const)
  intro u hu
  change 2 ≤ u - 1 ∧ u - 1 ≤ 3
  constructor <;> linarith [hu.1, hu.2]

end Internal

/-- Chen's numerical estimate for the exact integrals in equations (26)--(27).
The small cubic saving in `jurkatRichert_innerIntegral_le` makes the displayed
decimal bound valid despite the rounding in the printed elementary majorant. -/
theorem jurkatRichert_integralEstimate :
    (-0.0164725 : ℝ) ≤ jurkatRichertJ - jurkatRichertK / 4 := by
  let c : ℝ → ℝ := fun u => (u - 5 / 2) / (u * (5 - u))
  let B : ℝ → ℝ := fun u => (u - 3 + 4 / (u - 1) - 2) / 2
  let H : ℝ → ℝ := fun u => -c u * B u + (u - 3) ^ 3 / 36000
  let A : ℝ → ℝ := fun u =>
    u / 2 + (3 / 4) * Real.log (u - 1) + (1 / 4) * Real.log (5 - u) -
      (9 / 4) * Real.log u + (u - 3) ^ 4 / 144000
  have hc : ContinuousOn c (Set.Icc (3 : ℝ) 4) := by
    dsimp [c]
    apply ContinuousOn.div (continuousOn_id.sub continuousOn_const)
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    intro u hu
    change u * (5 - u) ≠ 0
    exact mul_ne_zero (by linarith [hu.1]) (by linarith [hu.2])
  have hB : ContinuousOn B (Set.Icc (3 : ℝ) 4) := by
    dsimp [B]
    apply ((continuousOn_id.sub continuousOn_const).add
      (ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const) ?_)).sub
      continuousOn_const |>.div_const 2
    intro u hu
    change u - 1 ≠ 0
    linarith [hu.1]
  have hH : ContinuousOn H (Set.Icc (3 : ℝ) 4) := by
    dsimp [H]
    exact (hc.neg.mul hB).add
      ((continuousOn_id.sub continuousOn_const).pow 3 |>.div_const 36000)
  have hHint : IntervalIntegrable H volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    exact hH
  have hJ : IntervalIntegrable
      (fun u : ℝ => jurkatRichertInnerIntegral u / u) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    apply ContinuousOn.div continuousOn_jurkatRichertInnerIntegral continuousOn_id
    intro u hu
    change u ≠ 0
    linarith [hu.1]
  have hK : IntervalIntegrable
      (fun u : ℝ => 10 / (u * (5 - u)) * jurkatRichertInnerIntegral u) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    apply (ContinuousOn.div continuousOn_const
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_).mul
        continuousOn_jurkatRichertInnerIntegral
    intro u hu
    change u * (5 - u) ≠ 0
    exact mul_ne_zero (by linarith [hu.1]) (by linarith [hu.2])
  have hactual : IntervalIntegrable
      (fun u : ℝ => -c u * jurkatRichertInnerIntegral u) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    exact hc.neg.mul continuousOn_jurkatRichertInnerIntegral
  have hcombine :
      jurkatRichertJ - jurkatRichertK / 4 =
        ∫ u in (3 : ℝ)..4, -c u * jurkatRichertInnerIntegral u := by
    unfold jurkatRichertJ jurkatRichertK
    have hscale :
        (∫ u in (3 : ℝ)..4,
            10 / (u * (5 - u)) * jurkatRichertInnerIntegral u) / 4 =
          ∫ u in (3 : ℝ)..4,
            (10 / (u * (5 - u)) * jurkatRichertInnerIntegral u) * (1 / 4) := by
      rw [intervalIntegral.integral_mul_const]
      ring
    rw [hscale, ← intervalIntegral.integral_sub hJ (hK.mul_const (1 / 4))]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u ≠ 0 := by
      rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
      linarith [hu.1]
    have h5u : 5 - u ≠ 0 := by
      rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
      linarith [hu.2]
    dsimp [c]
    field_simp [hu0, h5u]
    ring
  have hpoint : ∀ u ∈ Set.Icc (3 : ℝ) 4,
      H u ≤ -c u * jurkatRichertInnerIntegral u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have h5u : 0 < 5 - u := by linarith [hu.2]
    have hden : 0 < u * (5 - u) := mul_pos hu0 h5u
    have hprod : 0 ≤ (u - 3) * (u + 10) :=
      mul_nonneg (sub_nonneg.mpr hu.1) (by linarith [hu.1])
    have hc12 : (1 / 12 : ℝ) ≤ c u := by
      dsimp [c]
      rw [le_div_iff₀ hden]
      nlinarith
    have hc0 : 0 ≤ c u := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 12) hc12
    have hcube : 0 ≤ (u - 3) ^ 3 := pow_nonneg (sub_nonneg.mpr hu.1) _
    have hcube' : 0 ≤ (u - 3) ^ 3 / 3000 := div_nonneg hcube (by norm_num)
    have hsave : (u - 3) ^ 3 / 36000 ≤ c u * ((u - 3) ^ 3 / 3000) := by
      nlinarith [mul_le_mul_of_nonneg_right hc12 hcube']
    have hinner := jurkatRichert_innerIntegral_le hu.1 hu.2
    dsimp [H]
    calc
      -c u * B u + (u - 3) ^ 3 / 36000 ≤
          -c u * B u + c u * ((u - 3) ^ 3 / 3000) := by linarith
      _ = -c u * (B u - (u - 3) ^ 3 / 3000) := by ring
      _ ≤ -c u * jurkatRichertInnerIntegral u :=
        mul_le_mul_of_nonpos_left hinner (by linarith)
  have hA : ∀ u ∈ Set.uIcc (3 : ℝ) 4, HasDerivAt A (H u) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
    have h5u : 5 - u ≠ 0 := by linarith [hu.2]
    dsimp [A, H, B, c]
    have h1 := (hasDerivAt_id u).div_const 2
    have h2 := (((hasDerivAt_id u).sub_const 1).log hu1).const_mul (3 / 4)
    have h3 :=
      (((hasDerivAt_const u (5 : ℝ)).sub (hasDerivAt_id u)).log h5u).const_mul (1 / 4)
    have h4 := (Real.hasDerivAt_log hu0).const_mul (9 / 4)
    have h5 := (((hasDerivAt_id u).sub_const 3).pow 4).div_const 144000
    have h := (((h1.add h2).add h3).sub h4).add h5
    convert h using 1
    all_goals try rfl
    all_goals simp only [id_eq, Pi.sub_apply]
    all_goals field_simp [hu0, hu1, h5u]
    all_goals ring
  have hHeval : (∫ u in (3 : ℝ)..4, H u) =
      1 / 2 + 3 * Real.log 3 - 11 / 2 * Real.log 2 + 1 / 144000 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hA hHint]
    dsimp [A]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num [Real.log_one]
    ring
  have hnum : (-0.0164725 : ℝ) ≤
      1 / 2 + 3 * Real.log 3 - 11 / 2 * Real.log 2 + 1 / 144000 := by
    have h2 := Real.log_two_near_10
    have h3 := Real.log_three_near_10
    rw [abs_le] at h2 h3
    norm_num at h2 h3 ⊢
    linarith
  calc
    (-0.0164725 : ℝ) ≤
        1 / 2 + 3 * Real.log 3 - 11 / 2 * Real.log 2 + 1 / 144000 := hnum
    _ = ∫ u in (3 : ℝ)..4, H u := hHeval.symm
    _ ≤ ∫ u in (3 : ℝ)..4, -c u * jurkatRichertInnerIntegral u :=
      intervalIntegral.integral_mono_on (by norm_num) hHint hactual hpoint
    _ = jurkatRichertJ - jurkatRichertK / 4 := hcombine.symm

/-- The base lower-sieve coefficient in Chen's equation (26). -/
noncomputable def jurkatRichertBaseMainCoefficient (J : ℝ) : ℝ :=
  8 * (Real.log 4 + J)

/-- The dimensionless source lower-sieve factor before equation (25)'s
Mertens normalization is applied. -/
noncomputable def jurkatRichertBaseSieveFactor (J : ℝ) : ℝ :=
  (2 * Real.exp Real.eulerMascheroniConstant / 5) * (Real.log 4 + J)

/-- The factor in Chen's equation (25):
`Γ_N(N^(1/10)) ~ 20 exp(-γ) C_N / log N`. -/
noncomputable def jurkatRichertMertensFactor : ℝ :=
  20 * Real.exp (-Real.eulerMascheroniConstant)

theorem jurkatRichertBaseSieveFactor_pos :
    0 < jurkatRichertBaseSieveFactor jurkatRichertJ := by
  unfold jurkatRichertBaseSieveFactor
  exact mul_pos (by positivity)
    (add_pos_of_pos_of_nonneg (Real.log_pos (by norm_num)) jurkatRichertJ_nonneg)

theorem jurkatRichertMertensFactor_pos :
    0 < jurkatRichertMertensFactor := by
  unfold jurkatRichertMertensFactor
  positivity

/-- Equation (25)'s Mertens factor and equation (26)'s lower-sieve factor
multiply to the exact base coefficient, with no opaque constant. -/
theorem jurkatRichert_sieveFactor_mul_mertensFactor :
    jurkatRichertBaseSieveFactor jurkatRichertJ *
        jurkatRichertMertensFactor =
      jurkatRichertBaseMainCoefficient jurkatRichertJ := by
  unfold jurkatRichertBaseSieveFactor jurkatRichertMertensFactor
    jurkatRichertBaseMainCoefficient
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- The varying-level medium-prime upper-sieve coefficient in Chen's equations
(26)--(27). -/
noncomputable def jurkatRichertQ1MainCoefficient (K : ℝ) : ℝ :=
  8 * (Real.log 8 + K / 2)

/-- The exact algebraic split behind Chen's `2.6408`: the base lower-sieve
coefficient minus half the distinct-q upper-sieve coefficient. -/
theorem jurkatRichert_mainCoefficient_decomposition (J K : ℝ) :
    jurkatRichertBaseMainCoefficient J -
        jurkatRichertQ1MainCoefficient K / 2 =
      8 * (Real.log 4 - Real.log 8 / 2 + (J - K / 4)) := by
  unfold jurkatRichertBaseMainCoefficient jurkatRichertQ1MainCoefficient
  ring

/-- Chen's numerical integral input `J - K/4 ≥ -0.0164725` yields the published
coefficient `2.6408`.  The remaining decimal step is certified from Mathlib's
explicit lower bound for `log 2`. -/
theorem jurkatRichert_mainCoefficient_ge_twoPoint6408 (J K : ℝ)
    (hJK : (-0.0164725 : ℝ) ≤ J - K / 4) :
    (2.6408 : ℝ) ≤
      jurkatRichertBaseMainCoefficient J -
        jurkatRichertQ1MainCoefficient K / 2 := by
  rw [jurkatRichert_mainCoefficient_decomposition]
  have hlog :
      (0.3301 : ℝ) ≤ Real.log 4 - Real.log 8 / 2 - 0.0164725 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
    nlinarith [Real.log_two_gt_d9]
  nlinarith

/-- The valuation-weighted count used by the corrected finite Chen
decomposition.  It is not the direct literature object: repeated powers of one
medium prime are charged with their full valuation. -/
noncomputable def jurkatRichertWeightedCount (N : ℕ) : ℝ :=
  ((correctedChenCandidates N).card : ℝ) - correctedChenPrimePowerPenalty N / 2

/-- The canonical corrected endpoint.  For every positive coefficient margin,
the valuation-weighted count is eventually bounded below by
`(2.6408 - η) 𝔖(N) N / log² N` along the even integers, in Liu's genuine
singular-series normalization.  It is produced from the source-faithful
distinct-q theorem below, after a separate proper-prime-power correction. -/
def ChenJurkatRichertWeightedLowerBound : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (2.6408 - η) * SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ (2 : ℕ) ≤
        jurkatRichertWeightedCount N

/-- `correctedChenOmega` splits into its prime-power and triple parts. -/
theorem correctedChenOmega_eq_primePower_add_triple (N : ℕ) :
    correctedChenOmega N =
      (correctedChenCandidates N).sum
          (fun p => primePowerSum (N - p) (correctedChenZ N) (correctedChenY N)) +
      (correctedChenCandidates N).sum
          (fun p => tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)) := by
  unfold correctedChenOmega correctedChenPenalty
  rw [Finset.sum_add_distrib]

/-- Exact finite bookkeeping: the Jurkat--Richert weighted count has already
paid the prime-power part of the corrected penalty, leaving only half of the
strict ordered-triple penalty. -/
theorem correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple
    (N : ℕ) :
    ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 =
      jurkatRichertWeightedCount N - correctedChenTriplePenalty N / 2 := by
  rw [correctedChenOmega_eq_primePower_add_triple]
  unfold jurkatRichertWeightedCount correctedChenPrimePowerPenalty
    correctedChenTriplePenalty
  ring

/-- Source-scale upper input for the genuine strict ordered-triple penalty.
It is independent of the JR weighted lower conclusion and keeps the inverse-log
remainder visible. -/
def ChenJurkatRichertTriplePenaltyUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop, Even N →
    correctedChenTriplePenalty N ≤
      3.94033 * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) +
        C * (N : ℝ) / Real.log N ^ (3 : ℕ)

/-! ## Uniform prime-power bound -/

/-- `#{p < N : m | N-p} ≤ N/m + 1`: `p` is determined by the quotient `(N-p)/m` when `1 ≤ m`. -/
private theorem range_dvd_count_le (N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.range N).filter (fun p => m ∣ N - p)).card ≤ N / m + 1 := by
  classical
  let s : Finset ℕ := (Finset.range N).filter (fun p => m ∣ N - p)
  have hmap : ∀ p ∈ s, (N - p) / m ∈ Finset.range (N / m + 1) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpN, hdvd⟩
    have hle : (N - p) / m ≤ N / m := Nat.div_le_div_right (by omega : N - p ≤ N)
    rw [Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun p => (N - p) / m) (↑s : Set ℕ) := by
    intro p hp q hq hpq
    rcases Finset.mem_filter.mp hp with ⟨hpN, hpd⟩
    rcases Finset.mem_filter.mp hq with ⟨hqN, hqd⟩
    have hpc : N - p = (N - p) / m * m := (Nat.div_mul_cancel hpd).symm
    have hqc : N - q = (N - q) / m * m := (Nat.div_mul_cancel hqd).symm
    have hpN' : p < N := by simpa using hpN
    have hqN' : q < N := by simpa using hqN
    have hd : (N - p) / m * m = (N - q) / m * m := by
      simpa using congrArg (fun x => x * m) hpq
    have hpq' : N - p = N - q := by
      rw [hpc, hqc]
      exact hd
    omega
  have himg : s.image (fun p => (N - p) / m) ⊆ Finset.range (N / m + 1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact hmap p hp
  have hcardimg : (s.image (fun p => (N - p) / m)).card = s.card :=
    Finset.card_image_of_injOn hinj
  calc
    s.card = (s.image (fun p => (N - p) / m)).card := hcardimg.symm
    _ ≤ (Finset.range (N / m + 1)).card := Finset.card_le_card himg
    _ = N / m + 1 := by simp

/-- `Σ_{n ∈ Ico a b} 1/(n(n−1)) = 1/(a−1) − 1/(b−1)` (`2 ≤ a ≤ b`). -/
private theorem inv_mul_sub_one_Ico_sum (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (Finset.Ico a b).sum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) =
      1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
  have hfac : ∀ n ∈ Finset.Ico a b,
      (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨han, hnb⟩
    have hn2 : 2 ≤ n := by omega
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp [hn1, hn0]
    ring
  rw [Finset.sum_congr rfl hfac]
  let g : ℕ → ℝ := fun k => 1 / (((a + k : ℕ) : ℝ) - 1)
  have hshift : Finset.Ico a b = (Finset.range (b - a)).image (fun k => a + k) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨han, hnb⟩
      refine Finset.mem_image.mpr ⟨n - a, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · omega
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
      rw [Finset.mem_Ico]
      have hklt : k < b - a := by simpa using (Finset.mem_range.mp hk)
      constructor <;> omega
  have hinj : Set.InjOn (fun k => a + k) (↑(Finset.range (b - a)) : Set ℕ) := by
    intro k hk l hl hkl
    have hkl' : a + k = a + l := by simpa using hkl
    omega
  rw [hshift, Finset.sum_image hinj]
  have hstep : ∀ k : ℕ, (Nat.cast (a + (k + 1)) : ℝ) - 1 = (Nat.cast (a + k) : ℝ) := by
    intro k
    norm_num [Nat.cast_add]
    ring
  have hterm : ∀ k ∈ Finset.range (b - a),
      1 / ((Nat.cast (a + k) : ℝ) - 1) - 1 / (Nat.cast (a + k) : ℝ) =
        g k - g (k + 1) := by
    intro k hk
    unfold g
    rw [hstep k]
  rw [Finset.sum_congr rfl hterm]
  have hsum := Finset.sum_range_sub (f := g) (n := b - a)
  have hneg : (Finset.range (b - a)).sum (fun k => g k - g (k + 1)) = g 0 - g (b - a) := by
    calc
      (Finset.range (b - a)).sum (fun k => g k - g (k + 1))
          = (Finset.range (b - a)).sum (fun k => -(g (k + 1) - g k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = -((Finset.range (b - a)).sum (fun k => g (k + 1) - g k)) := by
              rw [Finset.sum_neg_distrib]
      _ = -(g (b - a) - g 0) := by rw [hsum]
      _ = g 0 - g (b - a) := by ring
  rw [hneg]
  unfold g
  norm_num [Nat.cast_sub hab, Nat.cast_add]


/-- **Uniform bound for proper prime powers**: the number of pairs `(p,q)` with p a corrected candidate,
q a prime in `[z,y)`, and `q² | N-p` is uniformly bounded by `6·N^{9/10}`. -/
theorem correctedChenPrimePowerProperCountBound (N : ℕ) (hNbig : 2 ^ 110 < N)
    (hEven : Even N) :
    (correctedChenCandidates N).sum (fun p =>
      ((Finset.range (correctedChenY N)).filter
        (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card) ≤
      6 * (N : ℝ) ^ (9 / 10 : ℝ) := by
  have hN2 : 2 ≤ N := by
    have h : 2 ^ 110 ≤ N := le_of_lt hNbig
    omega
  let Q : Finset ℕ := (Finset.range (correctedChenY N)).filter
    (fun q => q.Prime ∧ correctedChenZ N ≤ q)
  have hz2 : 2 ≤ correctedChenZ N := by
    unfold correctedChenZ
    exact le_max_left _ _
  have hz_ge : (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ (correctedChenZ N : ℝ) :=
    chenZ_ge_root_half N hNbig
  have hy_le : (correctedChenY N : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 3 : ℝ) := by
    unfold correctedChenY
    have hcu : (Nat.ceil ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) + 1 := by
      have hc := Nat.ceil_le_floor_add_one ((N : ℝ) ^ (1 / 3 : ℝ))
      have hfl := Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ))
      have hc' : (Nat.ceil ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
          (Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) + 1 := by exact_mod_cast hc
      linarith
    have hN13 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
    linarith
  have hzle_y : correctedChenZ N ≤ correctedChenY N :=
    (correctedChen_cutoffValid_of_nine_le (by omega : 9 ≤ N)).1.le
  have hper : ∀ q ∈ Q, ((correctedChenCandidates N).filter (fun p => q ^ 2 ∣ N - p)).card ≤
      N / q ^ 2 + 1 := by
    intro q hq
    have hsub : (correctedChenCandidates N).filter (fun p => q ^ 2 ∣ N - p) ⊆
        (Finset.range N).filter (fun p => q ^ 2 ∣ N - p) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpc, hdvd⟩
      rcases Finset.mem_filter.mp hpc with ⟨hpN, _⟩
      exact Finset.mem_filter.mpr ⟨hpN, hdvd⟩
    have hq2 : 2 ≤ q ^ 2 := by
      have hq' : q.Prime := (Finset.mem_filter.mp hq).2.1
      nlinarith [hq'.two_le]
    exact le_trans (Finset.card_le_card hsub)
      (range_dvd_count_le N (q ^ 2) (by omega))
  have htelesc : (∑ q ∈ Q, (1 : ℝ) / ((q : ℝ) ^ 2)) ≤ 2 / (correctedChenZ N : ℝ) := by
    have hsubq : Q ⊆ Finset.Ico (correctedChenZ N) (correctedChenY N) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqy, hcond⟩
      rw [Finset.mem_Ico]
      constructor
      · exact hcond.2
      · simpa using hqy
    have hle1 : (∑ q ∈ Q, (1 : ℝ) / ((q : ℝ) ^ 2)) ≤
        ∑ q ∈ Finset.Ico (correctedChenZ N) (correctedChenY N), (1 : ℝ) / ((q : ℝ) ^ 2) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubq (fun q hq hnot => by positivity)
    have hinv : ∀ q ∈ Finset.Ico (correctedChenZ N) (correctedChenY N),
        (1 : ℝ) / ((q : ℝ) ^ 2) ≤ (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := by
      intro q hq
      rcases Finset.mem_Ico.mp hq with ⟨hzq, hqy⟩
      have hq2n : 2 ≤ q := by omega
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
        have : (2 : ℝ) ≤ q := by exact_mod_cast hq2n
        linarith
      rw [div_le_div_iff₀ (sq_pos_of_pos hqpos) (mul_pos hqpos hq1)]
      have hsq : (q : ℝ) * ((q : ℝ) - 1) ≤ (q : ℝ) ^ 2 := by
        nlinarith
      simpa [mul_one] using hsq
    have hle2 : (∑ q ∈ Finset.Ico (correctedChenZ N) (correctedChenY N),
          (1 : ℝ) / ((q : ℝ) ^ 2)) ≤
        ∑ q ∈ Finset.Ico (correctedChenZ N) (correctedChenY N),
          (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := by
      exact Finset.sum_le_sum hinv
    have htel := inv_mul_sub_one_Ico_sum (correctedChenZ N) (correctedChenY N) hz2 hzle_y
    have htail : 1 / ((correctedChenZ N : ℝ) - 1) - 1 / ((correctedChenY N : ℝ) - 1) ≤
        2 / (correctedChenZ N : ℝ) := by
      have hzpos : (0 : ℝ) < (correctedChenZ N : ℝ) - 1 := by
        have : (2 : ℝ) ≤ correctedChenZ N := by exact_mod_cast hz2
        linarith
      have hfrac : 1 / ((correctedChenZ N : ℝ) - 1) ≤ 2 / (correctedChenZ N : ℝ) := by
        rw [div_le_div_iff₀ hzpos (by exact_mod_cast (by omega : 0 < correctedChenZ N))]
        have hz2r : (2 : ℝ) ≤ correctedChenZ N := by exact_mod_cast hz2
        nlinarith
      have hy2 : 2 ≤ correctedChenY N := by
        have : correctedChenZ N ≤ correctedChenY N := hzle_y
        omega
      have hy1 : (0 : ℝ) < (correctedChenY N : ℝ) - 1 := by
        have : (2 : ℝ) ≤ correctedChenY N := by exact_mod_cast hy2
        linarith
      have hnonneg : (0 : ℝ) ≤ 1 / ((correctedChenY N : ℝ) - 1) := by positivity
      linarith
    calc
      (∑ q ∈ Q, (1 : ℝ) / ((q : ℝ) ^ 2)) ≤
          ∑ q ∈ Finset.Ico (correctedChenZ N) (correctedChenY N), (1 : ℝ) / ((q : ℝ) ^ 2) := hle1
      _ ≤ ∑ q ∈ Finset.Ico (correctedChenZ N) (correctedChenY N),
            (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := hle2
      _ = 1 / ((correctedChenZ N : ℝ) - 1) - 1 / ((correctedChenY N : ℝ) - 1) := htel
      _ ≤ 2 / (correctedChenZ N : ℝ) := htail
  have hmain : (∑ q ∈ Q, (N : ℝ) / (q : ℝ) ^ 2) ≤ 4 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc
      (∑ q ∈ Q, (N : ℝ) / (q : ℝ) ^ 2) = (N : ℝ) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        congr 1
        ext q
        ring
      _ ≤ (N : ℝ) * (2 / (correctedChenZ N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left htelesc (by exact_mod_cast (by omega : 0 ≤ N))
      _ ≤ 4 * (N : ℝ) ^ (9 / 10 : ℝ) := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        have hdiv : (N : ℝ) * (2 / (correctedChenZ N : ℝ)) ≤
            (N : ℝ) * (2 / ((N : ℝ) ^ (1 / 10 : ℝ) / 2)) := by
          have hzpos2 : (0 : ℝ) < correctedChenZ N := by
            exact_mod_cast (by omega : 0 < correctedChenZ N)
          have hxpos2 : (0 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) / 2 := by positivity
          have hdiv2 : 2 / (correctedChenZ N : ℝ) ≤
              2 / ((N : ℝ) ^ (1 / 10 : ℝ) / 2) := by
            rw [div_le_div_iff₀ hzpos2 hxpos2]
            have hx2z : (N : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * (correctedChenZ N : ℝ) := by
              linarith [hz_ge]
            nlinarith
          exact mul_le_mul_of_nonneg_left
            hdiv2 (le_of_lt hNpos)
        have hmain4 : (N : ℝ) * (2 / ((N : ℝ) ^ (1 / 10 : ℝ) / 2)) ≤
            4 * (N : ℝ) ^ (9 / 10 : ℝ) := by
          have hx : (N : ℝ) ^ (1 / 10 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNpos _)
          have hN1 : (N : ℝ) ^ (1 : ℝ) = N := Real.rpow_one (N : ℝ)
          have h2 : (2 : ℝ) / ((N : ℝ) ^ (1 / 10 : ℝ) / 2) = 4 / (N : ℝ) ^ (1 / 10 : ℝ) := by
            ring_nf
          have hsub10 : (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) =
              (N : ℝ) ^ (9 / 10 : ℝ) := by
            have h := Real.rpow_sub hNpos (1 : ℝ) (1 / 10 : ℝ)
            have hfrac : (1 : ℝ) - 1 / 10 = 9 / 10 := by norm_num
            rw [hfrac, hN1] at h
            rw [hN1]
            exact h.symm
          calc
            (N : ℝ) * (2 / ((N : ℝ) ^ (1 / 10 : ℝ) / 2)) =
                4 * ((N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ)) := by
                  rw [h2]
                  ring_nf
             _ ≤ 4 * (N : ℝ) ^ (9 / 10 : ℝ) := by
                  have hstep : ((N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ)) =
                      (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) :=
                    congrArg (fun x : ℝ => x / (N : ℝ) ^ (1 / 10 : ℝ)) hN1.symm
                  rw [hstep]
                  rw [hsub10]
        exact le_trans hdiv hmain4
  have hone : (∑ q ∈ Q, (1 : ℝ)) ≤ 2 * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have hsub : Q ⊆ Finset.range (correctedChenY N) := by
      intro q hq
      exact (Finset.mem_filter.mp hq).1
    calc
      (∑ q ∈ Q, (1 : ℝ)) = (Q.card : ℝ) := by simp
      _ ≤ ((Finset.range (correctedChenY N)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (correctedChenY N : ℝ) := by simp
      _ ≤ 2 * (N : ℝ) ^ (1 / 3 : ℝ) := hy_le
  have hone6 : 2 * (N : ℝ) ^ (1 / 3 : ℝ) ≤ 2 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    have hmono : (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N))
        (by norm_num : (1 / 3 : ℝ) ≤ 9 / 10)
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)
  calc
    (correctedChenCandidates N).sum (fun p =>
        ((Finset.range (correctedChenY N)).filter
          (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card)
        = ∑ q ∈ Q, (((correctedChenCandidates N).filter (fun p => q ^ 2 ∣ N - p)).card : ℝ) := by
          unfold Q
          calc
            (correctedChenCandidates N).sum (fun p =>
              ((Finset.range (correctedChenY N)).filter
                (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ^ 2 ∣ N - p)).card)
                = (correctedChenCandidates N).sum (fun p =>
                    ∑ q ∈ Q, if q ^ 2 ∣ N - p then (1 : ℝ) else 0) := by
                  rw [Nat.cast_sum]
                  apply Finset.sum_congr rfl
                  intro p hp
                  rw [Finset.card_filter]
                  rw [Nat.cast_sum]
                  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
                  simp [Q, Finset.sum_filter, and_assoc, and_left_comm, and_comm]
                  congr 1
                  ext x
                  simp [Finset.mem_filter, and_assoc, and_left_comm, and_comm]
            _ = ∑ q ∈ Q, (correctedChenCandidates N).sum (fun p =>
                  if q ^ 2 ∣ N - p then (1 : ℝ) else 0) := by
                  rw [Finset.sum_comm]
            _ = ∑ q ∈ Q, (((correctedChenCandidates N).filter (fun p => q ^ 2 ∣ N - p)).card : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  rw [Finset.sum_boole]
    _ ≤ ∑ q ∈ Q, ((N / q ^ 2 + 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact_mod_cast hper q hq
    _ ≤ (∑ q ∈ Q, (N : ℝ) / (q : ℝ) ^ 2) + (∑ q ∈ Q, (1 : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro q hq
        rw [Nat.cast_add, ← Nat.cast_pow]
        have hmain_le : ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (q ^ 2 : ℕ) :=
          Nat.cast_div_le (α := ℝ)
        simpa using add_le_add_left hmain_le (1 : ℝ)
    _ ≤ 4 * (N : ℝ) ^ (9 / 10 : ℝ) + 2 * (N : ℝ) ^ (1 / 3 : ℝ) := by
        exact add_le_add hmain hone
    _ ≤ 4 * (N : ℝ) ^ (9 / 10 : ℝ) + 2 * (N : ℝ) ^ (9 / 10 : ℝ) := by
        linarith
    _ = 6 * (N : ℝ) ^ (9 / 10 : ℝ) := by ring

/-- **Structural decomposition of the prime-power sum**: `primePowerSum(n) ≤ #{q ∈ [z,y) : q | n} +
Σ_{q ∈ [z,y), q²|n} v_q(n)`. Thus the prime-power penalty is at most the k=1 prime-divisor count
plus the proper-power part, whose `N^{9/10}` bound is supplied by `correctedChenPrimePowerProperCountBound`. -/
theorem primePowerSum_le_factorCount_add_powerSum (n z y : ℕ) (hn : n ≠ 0) :
    primePowerSum n z y ≤
      (((Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n)).card : ℝ) +
        ∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ^ 2 ∣ n),
          (n.factorization q : ℝ) := by
  have hident := primePowerSum_eq_sum_factorization_of_dvd (n := n) (z := z) (y := y) hn
  rw [hident]
  let F1 : Finset ℕ := (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n)
  let F2 : Finset ℕ := (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ^ 2 ∣ n)
  have hper : ∀ q ∈ F1, (n.factorization q : ℝ) ≤
      (1 : ℝ) + (if q ^ 2 ∣ n then (n.factorization q : ℝ) else 0) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqr, hc⟩
    have hv1 : 1 ≤ n.factorization q :=
      (Nat.Prime.pow_dvd_iff_le_factorization hc.1 hn (k := 1)).mp (by simpa using hc.2.2)
    by_cases hq2 : q ^ 2 ∣ n
    · simp [hq2]
    · have hv : n.factorization q = 1 := by
        have hvlt2 : ¬ 2 ≤ n.factorization q := by
          intro h2
          exact hq2 ((Nat.Prime.pow_dvd_iff_le_factorization hc.1 hn).mpr h2)
        omega
      simp [hq2, hv]
  have hsum : (∑ q ∈ F1, (n.factorization q : ℝ)) ≤
      (∑ q ∈ F1, (1 : ℝ)) + (∑ q ∈ F1,
        if q ^ 2 ∣ n then (n.factorization q : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hper
  have hfilter : (∑ q ∈ F1, if q ^ 2 ∣ n then (n.factorization q : ℝ) else 0) =
      ∑ q ∈ F2, (n.factorization q : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext q
    constructor
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hF1, hq2⟩
      rcases Finset.mem_filter.mp hF1 with ⟨hr, hc⟩
      exact Finset.mem_filter.mpr ⟨hr, ⟨hc.1, hc.2.1, hq2⟩⟩
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hr, hc⟩
      have hqn : q ∣ n := dvd_trans (dvd_mul_right q q) (by simpa [pow_two] using hc.2.2)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr, ⟨hc.1, hc.2.1, hqn⟩⟩, hc.2.2⟩
  have hcard : (∑ q ∈ F1, (1 : ℝ)) = (F1.card : ℝ) := by simp
  calc
    (∑ q ∈ F1, (n.factorization q : ℝ)) ≤
        (∑ q ∈ F1, (1 : ℝ)) + (∑ q ∈ F1,
          if q ^ 2 ∣ n then (n.factorization q : ℝ) else 0) := hsum
    _ = (F1.card : ℝ) + (∑ q ∈ F2, (n.factorization q : ℝ)) := by
        rw [hcard, hfilter]
    _ = (((Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ∣ n)).card : ℝ) +
          ∑ q ∈ (Finset.range y).filter (fun q => q.Prime ∧ z ≤ q ∧ q ^ 2 ∣ n),
            (n.factorization q : ℝ) := by
        rfl

/-- **Negligibility threshold**: for any `Cerr`, there exists `N₀` such that
`Cerr·N/log³N ≤ (1/4)·N/log²N` for even `N ≥ N₀`. It suffices to have
`log N ≥ 4·Cerr`, so take `N₀ = ⌈exp(4·Cerr)⌉ + 1`. -/
theorem errLogCube_negligible (Cerr : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      Cerr * (N : ℝ) / (log (N : ℝ)) ^ 3 ≤ (1 / 4 : ℝ) * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
  let N₀ : ℕ := max 2 (Nat.ceil (Real.exp (4 * Cerr)) + 1)
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  have hN2 : 2 ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogpos : (0 : ℝ) < log (N : ℝ) := Real.log_pos hN1
  have hNbig : Real.exp (4 * Cerr) < (N : ℝ) := by
    have h1 : Real.exp (4 * Cerr) ≤ (Nat.ceil (Real.exp (4 * Cerr)) : ℝ) := Nat.le_ceil _
    have hN' : (Nat.ceil (Real.exp (4 * Cerr)) + 1 : ℕ) ≤ N := by
      dsimp [N₀] at hN
      omega
    have hNcast : ((Nat.ceil (Real.exp (4 * Cerr)) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN'
    have hcast : ((Nat.ceil (Real.exp (4 * Cerr)) + 1 : ℕ) : ℝ) =
        (Nat.ceil (Real.exp (4 * Cerr)) : ℝ) + 1 := by norm_num
    have hNcast' : (Nat.ceil (Real.exp (4 * Cerr)) : ℝ) + 1 ≤ (N : ℝ) := by
      rwa [hcast] at hNcast
    linarith
  have hlogge : 4 * Cerr ≤ log (N : ℝ) := by
    have hlogexp : log (Real.exp (4 * Cerr)) = 4 * Cerr := by rw [Real.log_exp]
    have hmono : log (Real.exp (4 * Cerr)) ≤ log (N : ℝ) :=
      (Real.log_le_log_iff (Real.exp_pos _) hNpos).2 (le_of_lt hNbig)
    rwa [hlogexp] at hmono
  have hmain : Cerr ≤ (1 / 4 : ℝ) * log (N : ℝ) := by linarith
  rw [div_le_div_iff₀ (pow_pos hlogpos 3) (pow_pos hlogpos 2)]
  nlinarith [hmain, mul_pos hNpos (sq_pos_of_pos hlogpos)]

/-- Any inverse-log-cube remainder is eventually absorbed by an arbitrary
positive fraction of the Liu singular-series `N/log² N` scale. -/
theorem eventually_jr_inverseLogRemainder_le_scale
    (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
        ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
  let U := SingularSeries.liuUniversalProduct
  have hU : 0 < U := by
    simpa [U] using SingularSeries.liuUniversalProduct_pos
  let Cerr := C / (4 * ρ * U)
  obtain ⟨N₀, hN₀⟩ := errLogCube_negligible Cerr
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  intro hEven
  have hbase := hN₀ N hN hEven
  have hmul := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ 4 * ρ * U by positivity)
  have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℕ) :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  calc
    C * (N : ℝ) / Real.log N ^ (3 : ℕ) =
        (4 * ρ * U) *
          (Cerr * (N : ℝ) / Real.log N ^ (3 : ℕ)) := by
      dsimp [Cerr]
      field_simp
    _ ≤ (4 * ρ * U) *
        ((1 / 4 : ℝ) * (N : ℝ) / Real.log N ^ (2 : ℕ)) := hmul
    _ = ρ * U * (N : ℝ) / Real.log N ^ (2 : ℕ) := by ring
    _ ≤ ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hρ.le)
        (Nat.cast_nonneg N)

/-! ## The q¹ distribution input -/

/-- q¹ distribution input: the aggregate count of prime factors in `[z,y)` over candidates,
`Σ_{p ∈ candidates} #{q ∈ [z,y) : q | N−p}`. -/
noncomputable def correctedChenQ1Count (N : ℕ) : ℝ :=
  (correctedChenCandidates N).sum (fun p =>
    ((Finset.range (correctedChenY N)).filter
      (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card)

end MathlibNt.SieveTheory.SwitchingPrinciple
