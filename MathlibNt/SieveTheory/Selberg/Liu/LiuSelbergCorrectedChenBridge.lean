import MathlibNt.ChensTheorem
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergEvenAssembly
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbelDeterministic
import MathlibNt.SieveTheory.SwitchingPrinciple
import MathlibNt.SieveTheory.LinearSieve.LevelSupported.Q1LevelSupportedSieve

/-!
# Finite bridge from Liu's Selberg square to corrected Chen triples

This module isolates the exact overlap between Liu's source-pair Selberg square
and the corrected Chen triple count.  A candidate residual prime contributes
unit Selberg weight unless it divides Liu's paper modulus; those exceptional
primes remain as an explicit finite residual.
-/

open scoped BigOperators Classical

namespace MathlibNt.SieveTheory.LiuWeight

open Finset
open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple

/-- Corrected Chen triples whose first two primes are one fixed Liu source pair.
The ordering `p₂ ≤ p₃` and the corrected candidate residual are retained. -/
noncomputable def liuSelbergCorrectedTripleSlice
    (N p₁ p₂ : ℕ) : ℝ :=
  ∑ p₃ ∈ (range (N + 1)).filter (fun p₃ =>
      p₃.Prime ∧ p₂ ≤ p₃ ∧ p₁ * p₂ * p₃ ≤ N),
    if N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N then 1 else 0

/-- The exact exceptional part of a corrected triple slice: the candidate
residual prime divides Liu's paper modulus, so its optimal Selberg packet need
not reduce to the coefficient at `1`. -/
noncomputable def liuSelbergCorrectedTripleQResidual
    (N : ℕ) (epsilon : ℝ) (p₁ p₂ : ℕ) : ℝ :=
  ∑ p₃ ∈ (range (N + 1)).filter (fun p₃ =>
      p₃.Prime ∧ p₂ ≤ p₃ ∧ p₁ * p₂ * p₃ ≤ N),
    if N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N ∧
        N - p₁ * p₂ * p₃ ∣ liuPaperQModulus N epsilon then 1 else 0

/-- The source pairs common to Liu's characteristic weight and the corrected
Chen rectangular switching range. -/
noncomputable def liuSelbergCorrectedSourcePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).filter (fun p =>
    correctedChenZ N ≤ p.1 ∧ p.1 < correctedChenY N ∧
      correctedChenY N ≤ p.2)

/-- The corrected triple count on the exact common source-pair region. -/
noncomputable def liuSelbergCorrectedSourceTripleCount (N : ℕ) : ℝ :=
  ∑ p ∈ liuSelbergCorrectedSourcePairs N,
    liuSelbergCorrectedTripleSlice N p.1 p.2

/-- The modulus-dividing residual summed over the exact common source-pair
region. -/
noncomputable def liuSelbergCorrectedSourceTripleQResidual
    (N : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ p ∈ liuSelbergCorrectedSourcePairs N,
    liuSelbergCorrectedTripleQResidual N epsilon p.1 p.2

/-- The two possible source-pair contributions of a strict ordered triple to
the historical switched sum. -/
noncomputable def historicalChenOrderedTripleMultiplicity
    (N p₁ p₂ p₃ : ℕ) : ℝ :=
  chenF N (p₁ * p₂) + chenF N (p₁ * p₃)

/-- The historical `chenF` fibre has the same exact one-or-two multiplicity as
Liu's source weight: the smaller large prime always contributes, while the
larger contributes exactly on the additional square-cutoff subregion. -/
theorem historicalChenOrderedTripleMultiplicity_eq_one_add_indicator
    {N p₁ p₂ p₃ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (hroot₁ : (N : ℝ) ^ (1 / 10 : ℝ) < p₁)
    (hp₁root : (p₁ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hroot₂ : (N : ℝ) ^ (1 / 3 : ℝ) < p₂)
    (hp₂p₃ : p₂ < p₃) (hprod : p₁ * p₂ * p₃ ≤ N) :
    historicalChenOrderedTripleMultiplicity N p₁ p₂ p₃ =
      1 + if p₁ * p₃ ^ 2 ≤ N then 1 else 0 := by
  have hsmall : p₁ * p₂ ^ 2 ≤ N := by
    calc
      p₁ * p₂ ^ 2 = p₁ * p₂ * p₂ := by ring
      _ ≤ p₁ * p₂ * p₃ := Nat.mul_le_mul_left (p₁ * p₂) hp₂p₃.le
      _ ≤ N := hprod
  have hsmallSqrt :
      (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1 / 2 : ℝ) := by
    simpa [Real.sqrt_eq_rpow] using
      (liuSizeCondition_iff_real_sqrt hp₁.pos).mp hsmall
  have hf₂ : chenF N (p₁ * p₂) = 1 := by
    rw [chenF, if_pos]
    exact ⟨p₁, p₂, hp₁, hp₂, hroot₁, hp₁root, hroot₂, hsmallSqrt, rfl⟩
  by_cases hlarge : p₁ * p₃ ^ 2 ≤ N
  · have hlargeSqrt :
        (p₃ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1 / 2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow] using
        (liuSizeCondition_iff_real_sqrt hp₁.pos).mp hlarge
    have hf₃ : chenF N (p₁ * p₃) = 1 := by
      rw [chenF, if_pos]
      exact ⟨p₁, p₃, hp₁, hp₃, hroot₁, hp₁root,
        hroot₂.trans (by exact_mod_cast hp₂p₃), hlargeSqrt, rfl⟩
    simp [historicalChenOrderedTripleMultiplicity, hf₂, hf₃, hlarge]
  · have hf₃ : chenF N (p₁ * p₃) = 0 := by
      rw [chenF, if_neg]
      rintro ⟨q₁, q₂, hq₁, hq₂, _, hq₁root, _, hq₂sqrt, heq⟩
      have hq₁dvd : q₁ ∣ p₁ * p₃ := heq ▸ dvd_mul_right q₁ q₂
      rcases hq₁.dvd_mul.mp hq₁dvd with hq₁p₁ | hq₁p₃
      · have hq₁eq : q₁ = p₁ :=
          (Nat.prime_dvd_prime_iff_eq hq₁ hp₁).mp hq₁p₁
        subst q₁
        have hq₂eq : q₂ = p₃ := Nat.mul_left_cancel hp₁.pos heq.symm
        subst q₂
        apply hlarge
        apply (liuSizeCondition_iff_real_sqrt hp₁.pos).mpr
        simpa [Real.sqrt_eq_rpow] using hq₂sqrt
      · have hq₁eq : q₁ = p₃ :=
          (Nat.prime_dvd_prime_iff_eq hq₁ hp₃).mp hq₁p₃
        subst q₁
        have hp₃root : (N : ℝ) ^ (1 / 3 : ℝ) < p₃ :=
          hroot₂.trans (by exact_mod_cast hp₂p₃)
        linarith
    simp [historicalChenOrderedTripleMultiplicity, hf₂, hf₃, hlarge]

/-- On common integer and real cutoffs, historical `chenOmega` source fibres
and the source-pair carrier underlying Liu's square count have exactly the same
local multiplicity.  The square count additionally weights each carrier element
by its squared divisor packet. -/
theorem historicalChenOrderedTripleMultiplicity_eq_liu
    {N z y p₁ p₂ p₃ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (hzp₁ : z < p₁) (hp₁y : p₁ ≤ y) (hyp₂ : y < p₂)
    (hroot₁ : (N : ℝ) ^ (1 / 10 : ℝ) < p₁)
    (hp₁root : (p₁ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hroot₂ : (N : ℝ) ^ (1 / 3 : ℝ) < p₂)
    (hp₂p₃ : p₂ < p₃) (hprod : p₁ * p₂ * p₃ ≤ N) :
    historicalChenOrderedTripleMultiplicity N p₁ p₂ p₃ =
      liuOrderedTriplePairMultiplicity N z y p₁ p₂ p₃ := by
  rw [historicalChenOrderedTripleMultiplicity_eq_one_add_indicator
      hp₁ hp₂ hp₃ hroot₁ hp₁root hroot₂ hp₂p₃ hprod,
    liuOrderedTriplePairMultiplicity_eq_one_add_indicator
      hp₁ hp₂ hp₃ hzp₁ hp₁y hyp₂ hp₂p₃ hprod]

/-- A product of three primes has exactly three prime factors with
multiplicity, so it is not a `P₂`. -/
theorem strict_ordered_triple_not_isAtMostAlmostPrime_two
    {p₁ p₂ p₃ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime) :
    ¬Nat.IsAtMostAlmostPrime 2 (p₁ * p₂ * p₃) := by
  have hthree : Nat.IsAlmostPrime 3 (p₁ * p₂ * p₃) := by
    simpa using (hp₁.mul_isAlmostPrime_two hp₂).mul hp₃.isAlmostPrime_one
  rw [Nat.IsAlmostPrime] at hthree
  rw [Nat.IsAtMostAlmostPrime]
  omega

/-- A historical W-candidate with a strict three-prime complement belongs to
the bad fibre. -/
theorem strict_ordered_triple_mem_chenWBadCandidates
    {N p p₁ p₂ p₃ : ℕ} (hp : p ∈ chenWCandidates N)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (hcomplement : N - p = p₁ * p₂ * p₃) :
    p ∈ chenWBadCandidates N := by
  rw [chenWBadCandidates, mem_filter]
  exact ⟨hp, by
    rw [hcomplement]
    exact strict_ordered_triple_not_isAtMostAlmostPrime_two hp₁ hp₂ hp₃⟩

/-- On a strict ordered squarefree triple, the corrected penalty is exactly
two: one unit from the medium-prime multiplicity and one from the canonical
ordered-triple witness. -/
theorem correctedPenalty_of_strict_ordered_triple_eq_two
    {z y p₁ p₂ p₃ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (hzp₁ : z ≤ p₁) (hp₁y : p₁ < y) (hyp₂ : y ≤ p₂)
    (hp₂p₃ : p₂ < p₃) :
    primePowerSum (p₁ * p₂ * p₃) z y +
      tripleFactorCount (p₁ * p₂ * p₃) z y = 2 := by
  have hn0 : p₁ * p₂ * p₃ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hp₁.ne_zero hp₂.ne_zero) hp₃.ne_zero
  have hp₁p₂ : p₁ ≠ p₂ := by omega
  have hp₁p₃ : p₁ ≠ p₃ := by omega
  have hfilter :
      (range y).filter
          (fun q => q.Prime ∧ z ≤ q ∧ q ∣ p₁ * p₂ * p₃) = {p₁} := by
    ext q
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hqy, hq, _, hqdiv⟩
      rcases hq.dvd_mul.mp hqdiv with hqp₁p₂ | hqp₃
      · rcases hq.dvd_mul.mp hqp₁p₂ with hqp₁ | hqp₂
        · exact (Nat.prime_dvd_prime_iff_eq hq hp₁).mp hqp₁
        · have heq := (Nat.prime_dvd_prime_iff_eq hq hp₂).mp hqp₂
          omega
      · have heq := (Nat.prime_dvd_prime_iff_eq hq hp₃).mp hqp₃
        omega
    · intro hqeq
      subst q
      refine ⟨hp₁y, hp₁, hzp₁, ?_⟩
      simp [mul_assoc]
  have hfactorization : (p₁ * p₂ * p₃).factorization p₁ = 1 := by
    rw [Nat.factorization_mul
        (mul_ne_zero hp₁.ne_zero hp₂.ne_zero) hp₃.ne_zero,
      Nat.factorization_mul hp₁.ne_zero hp₂.ne_zero]
    simp [hp₁.factorization, hp₂.factorization, hp₃.factorization,
      hp₁p₂, hp₁p₃]
  have hprimePower : primePowerSum (p₁ * p₂ * p₃) z y = 1 := by
    rw [primePowerSum_eq_sum_factorization_of_dvd hn0, hfilter]
    simp [hfactorization]
  have htripleFilter :
      (range (p₁ * p₂ * p₃ + 1)).filter (fun q =>
        q.Prime ∧ z ≤ q ∧ q < y ∧
          ∃ r s, r.Prime ∧ s.Prime ∧ y ≤ r ∧ r ≤ s ∧
            q * r * s = p₁ * p₂ * p₃ ∧ q < r ∧ r ≤ s) = {p₁} := by
    ext q
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨_, hq, hqz, hqy, r, s, _, _, _, _, hqrs, _, _⟩
      have hqdiv : q ∣ p₁ * p₂ * p₃ := by
        rw [← hqrs]
        simp [mul_assoc]
      have hqmem : q ∈ (range y).filter
          (fun q => q.Prime ∧ z ≤ q ∧ q ∣ p₁ * p₂ * p₃) :=
        mem_filter.mpr ⟨mem_range.mpr hqy, hq, hqz, hqdiv⟩
      rw [hfilter] at hqmem
      exact mem_singleton.mp hqmem
    · intro hqeq
      subst q
      refine ⟨?_, hp₁, hzp₁, hp₁y, p₂, p₃, hp₂, hp₃, hyp₂,
        hp₂p₃.le, rfl, ?_, hp₂p₃.le⟩
      · exact Nat.lt_succ_of_le <| calc
          p₁ ≤ p₁ * p₂ := Nat.le_mul_of_pos_right p₁ hp₂.pos
          _ ≤ p₁ * p₂ * p₃ :=
            Nat.le_mul_of_pos_right (p₁ * p₂) hp₃.pos
      · omega
  have htriple : tripleFactorCount (p₁ * p₂ * p₃) z y = 1 := by
    unfold tripleFactorCount
    rw [htripleFilter]
    simp
  norm_num [hprimePower, htriple]

/-- The exact strict-triple value of the corrected candidate penalty. -/
theorem correctedChenPenalty_eq_two_of_strict_ordered_triple
    {N p p₁ p₂ p₃ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (hzp₁ : correctedChenZ N ≤ p₁)
    (hp₁y : p₁ < correctedChenY N)
    (hyp₂ : correctedChenY N ≤ p₂) (hp₂p₃ : p₂ < p₃)
    (hcomplement : N - p = p₁ * p₂ * p₃) :
    correctedChenPenalty N p = 2 := by
  unfold correctedChenPenalty
  rw [hcomplement]
  exact correctedPenalty_of_strict_ordered_triple_eq_two
    hp₁ hp₂ hp₃ hzp₁ hp₁y hyp₂ hp₂p₃

/-- The honest finite carrier behind the corrected triple-factor sum.  Its
elements are candidate residuals together with the first prime factor; the
larger two prime factors remain existential, exactly as in
`tripleFactorCount`. -/
noncomputable def correctedChenFirstFactorCarrier
    (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (correctedChenCandidates N).sigma (fun p =>
    (range (N - p + 1)).filter (fun p₁ =>
      p₁.Prime ∧ correctedChenZ N ≤ p₁ ∧ p₁ < correctedChenY N ∧
      ∃ p₂ p₃, p₂.Prime ∧ p₃.Prime ∧ correctedChenY N ≤ p₂ ∧ p₂ ≤ p₃ ∧
        p₁ * p₂ * p₃ = N - p ∧ p₁ < p₂ ∧ p₂ ≤ p₃))

/-- The finite ordered-triple carrier counted by the common Liu source
region. -/
noncomputable def liuSelbergCorrectedSourceTripleCarrier
    (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (liuSelbergCorrectedSourcePairs N).sigma (fun p =>
    ((range (N + 1)).filter (fun p₃ =>
      p₃.Prime ∧ p.2 ≤ p₃ ∧ p.1 * p.2 * p₃ ≤ N)).filter (fun p₃ =>
        N - p.1 * p.2 * p₃ ∈ correctedChenCandidates N))

/-- The lower-cutoff endpoint fibre, represented by its candidate residual.
Divisibility by the fixed first factor is all that is needed for the ensuing
cardinality bound. -/
noncomputable def correctedChenLowerEndpointCarrier (N : ℕ) : Finset ℕ :=
  (correctedChenCandidates N).filter (fun p =>
    liuSourceZ10 N ∣ N - p)

/-- The upper-cutoff endpoint fibre, represented by the candidate residual and
the first prime factor. -/
noncomputable def correctedChenUpperEndpointCarrier
    (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (correctedChenCandidates N).sigma (fun p =>
    (range (correctedChenY N)).filter (fun p₁ =>
      p₁.Prime ∧ correctedChenZ N ≤ p₁ ∧
        p₁ * liuSourceY3 N ∣ N - p))

/-- Conditions on the ordered pair of larger factors selected from one
first-factor witness. -/
def correctedChenLargeFactorConditions
    (N p p₁ : ℕ) (q : ℕ × ℕ) : Prop :=
  q.1.Prime ∧ q.2.Prime ∧ correctedChenY N ≤ q.1 ∧ q.1 ≤ q.2 ∧
    p₁ * q.1 * q.2 = N - p ∧ p₁ < q.1 ∧ q.1 ≤ q.2

/-- A fixed ordered pair of larger factors for a member of the honest
first-factor carrier.  It is used only to inject that carrier into the source
and endpoint fibres; no multiplicity assertion is made. -/
noncomputable def correctedChenSelectedLargeFactors
    (N p p₁ : ℕ) : ℕ × ℕ :=
  if h : ∃ q : ℕ × ℕ, correctedChenLargeFactorConditions N p p₁ q then
    Classical.choose h
  else
    (0, 0)

/-- The selected larger factors satisfy all the ordered-factor conditions for
members of the first-factor carrier. -/
theorem correctedChenSelectedLargeFactors_spec
    {N : ℕ} {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ correctedChenFirstFactorCarrier N) :
    correctedChenLargeFactorConditions N x.1 x.2
      (correctedChenSelectedLargeFactors N x.1 x.2) := by
  rw [correctedChenFirstFactorCarrier, mem_sigma, mem_filter] at hx
  rcases hx.2.2.2.2.2 with ⟨p₂, p₃, h⟩
  have hex : ∃ q : ℕ × ℕ,
      correctedChenLargeFactorConditions N x.1 x.2 q :=
    ⟨(p₂, p₃), h⟩
  rw [correctedChenSelectedLargeFactors, dif_pos hex]
  exact Classical.choose_spec hex

/-- The selected-factor map sends a first-factor witness either to the common
source triple, to the lower endpoint, or to the upper endpoint. -/
noncomputable def correctedChenSourceEndpointMap
    (N : ℕ) (x : Σ _ : ℕ, ℕ) :
      (Σ _ : ℕ × ℕ, ℕ) ⊕ (ℕ ⊕ (Σ _ : ℕ, ℕ)) :=
  if x.2 = liuSourceZ10 N then
    Sum.inr (Sum.inl x.1)
  else
    let q := correctedChenSelectedLargeFactors N x.1 x.2
    if (x.2, q.1) ∈ liuSelbergCorrectedSourcePairs N then
      Sum.inl ⟨(x.2, q.1), q.2⟩
    else
      Sum.inr (Sum.inr x)

/-- The corrected triple-factor sum is exactly the cardinality of its
first-factor carrier.  In particular, this does not identify the summand with
the multiplicity of ordered triples. -/
theorem correctedChenTripleFactorSum_eq_firstFactorCarrier_card (N : ℕ) :
    (correctedChenCandidates N).sum
        (fun p => tripleFactorCount
          (N - p) (correctedChenZ N) (correctedChenY N)) =
      ((correctedChenFirstFactorCarrier N).card : ℝ) := by
  classical
  rw [correctedChenFirstFactorCarrier, card_sigma, Nat.cast_sum]
  rfl

/-- The common Liu source count is exactly the cardinality of its ordered
triple carrier. -/
theorem liuSelbergCorrectedSourceTripleCount_eq_carrier_card (N : ℕ) :
    liuSelbergCorrectedSourceTripleCount N =
      ((liuSelbergCorrectedSourceTripleCarrier N).card : ℝ) := by
  classical
  rw [liuSelbergCorrectedSourceTripleCarrier, card_sigma, Nat.cast_sum]
  unfold liuSelbergCorrectedSourceTripleCount liuSelbergCorrectedTripleSlice
  apply sum_congr rfl
  intro p hp
  rw [sum_boole]

/-- Once Liu's lower cutoff has reached `2`, it is exactly the corrected Chen
lower cutoff; the latter differs only by its small-`N` guard. -/
theorem correctedChenZ_eq_liuSourceZ10_of_two_le
    {N : ℕ} (hZ : 2 ≤ liuSourceZ10 N) :
    correctedChenZ N = liuSourceZ10 N := by
  simp only [correctedChenZ, liuSourceZ10]
  exact max_eq_right hZ

/-- The floor source split never exceeds the corrected ceiling split. -/
theorem liuSourceY3_le_correctedChenY (N : ℕ) :
    liuSourceY3 N ≤ correctedChenY N := by
  exact Nat.floor_le_ceil ((N : ℝ) ^ (1 / 3 : ℝ))

/-- The corrected ceiling split is at most one beyond Liu's floor split. -/
theorem correctedChenY_le_liuSourceY3_add_one (N : ℕ) :
    correctedChenY N ≤ liuSourceY3 N + 1 := by
  exact Nat.ceil_le_floor_add_one ((N : ℝ) ^ (1 / 3 : ℝ))

/-- Thus the only upper-cutoff mismatch is the single integer endpoint. -/
theorem correctedChenY_eq_liuSourceY3_or_add_one (N : ℕ) :
    correctedChenY N = liuSourceY3 N ∨
      correctedChenY N = liuSourceY3 N + 1 := by
  have hlo := liuSourceY3_le_correctedChenY N
  have hhi := correctedChenY_le_liuSourceY3_add_one N
  omega

/-- A corrected ordered triple lies in Liu's source carrier unless one of the
two integer cutoff endpoints is attained. -/
theorem correctedOrderedTriple_mem_liuWeightPairs_or_cutoff_endpoint
    {N p₁ p₂ p₃ : ℕ}
    (hZ : correctedChenZ N = liuSourceZ10 N)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (_hp₃ : p₃.Prime)
    (hZp₁ : correctedChenZ N ≤ p₁) (hp₁Y : p₁ < correctedChenY N)
    (hYp₂ : correctedChenY N ≤ p₂) (hp₂p₃ : p₂ ≤ p₃)
    (hprod : p₁ * p₂ * p₃ ≤ N) :
    (p₁, p₂) ∈
        liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N) ∨
      p₁ = liuSourceZ10 N ∨ p₂ = liuSourceY3 N := by
  have hp₁leY : p₁ ≤ liuSourceY3 N := by
    have hceil := correctedChenY_le_liuSourceY3_add_one N
    omega
  have hsourceZle : liuSourceZ10 N ≤ p₁ := by omega
  have hsourceYle : liuSourceY3 N ≤ p₂ :=
    (liuSourceY3_le_correctedChenY N).trans hYp₂
  by_cases hZstrict : liuSourceZ10 N < p₁
  · by_cases hYstrict : liuSourceY3 N < p₂
    · left
      rw [mem_liuWeightPairs]
      refine ⟨hp₁, hp₂, hZstrict, hp₁leY, hYstrict, ?_⟩
      have hmul := Nat.mul_le_mul_left (p₁ * p₂) hp₂p₃
      simpa [pow_two, mul_assoc] using hmul.trans hprod
    · exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inl (by omega))

/-- Away from the two displayed endpoints, corrected ordered triples are
literally Liu source pairs; the product-square condition follows from
`p₂ ≤ p₃`. -/
theorem correctedOrderedTriple_mem_liuWeightPairs
    {N p₁ p₂ p₃ : ℕ}
    (hZ : correctedChenZ N = liuSourceZ10 N)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (hZp₁ : correctedChenZ N ≤ p₁) (hp₁Y : p₁ < correctedChenY N)
    (hYp₂ : correctedChenY N ≤ p₂) (hp₂p₃ : p₂ ≤ p₃)
    (hprod : p₁ * p₂ * p₃ ≤ N)
    (hp₁ne : p₁ ≠ liuSourceZ10 N) (hp₂ne : p₂ ≠ liuSourceY3 N) :
    (p₁, p₂) ∈
      liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N) := by
  rcases correctedOrderedTriple_mem_liuWeightPairs_or_cutoff_endpoint
    hZ hp₁ hp₂ hp₃ hZp₁ hp₁Y hYp₂ hp₂p₃ hprod with h | h
  · exact h
  · exact (h.elim (fun h' => (hp₁ne h').elim)
      (fun h' => (hp₂ne h').elim))

/-- The selected-factor map lands in the disjoint union of the common source
carrier and the two endpoint fibres. -/
theorem correctedChenSourceEndpointMap_mem
    {N : ℕ} (hZ : correctedChenZ N = liuSourceZ10 N)
    {x : Σ _ : ℕ, ℕ} (hx : x ∈ correctedChenFirstFactorCarrier N) :
    correctedChenSourceEndpointMap N x ∈
      (liuSelbergCorrectedSourceTripleCarrier N).disjSum
        ((correctedChenLowerEndpointCarrier N).disjSum
          (correctedChenUpperEndpointCarrier N)) := by
  have hx' := hx
  rw [correctedChenFirstFactorCarrier, mem_sigma, mem_filter] at hx'
  have hp := hx'.1
  have hpN : x.1 < N := by
    rw [correctedChenCandidates, mem_filter] at hp
    exact mem_range.mp hp.1
  have hp₁Prime := hx'.2.2.1
  have hZp₁ := hx'.2.2.2.1
  have hp₁Y := hx'.2.2.2.2.1
  let q := correctedChenSelectedLargeFactors N x.1 x.2
  have hq := correctedChenSelectedLargeFactors_spec hx
  change correctedChenLargeFactorConditions N x.1 x.2 q at hq
  have hprodle : x.2 * q.1 * q.2 ≤ N := by
    rw [hq.2.2.2.2.1]
    omega
  have hclass :=
    correctedOrderedTriple_mem_liuWeightPairs_or_cutoff_endpoint
      hZ hp₁Prime hq.1 hq.2.1 hZp₁ hp₁Y hq.2.2.1 hq.2.2.2.1 hprodle
  by_cases hlower : x.2 = liuSourceZ10 N
  · have hdvd : liuSourceZ10 N ∣ N - x.1 := by
      refine ⟨q.1 * q.2, ?_⟩
      simpa [hlower, mul_assoc] using hq.2.2.2.2.1.symm
    have hmem : x.1 ∈ correctedChenLowerEndpointCarrier N :=
      mem_filter.mpr ⟨hp, hdvd⟩
    simp [correctedChenSourceEndpointMap, hlower, mem_disjSum, hmem]
  · by_cases hsource :
        (x.2, q.1) ∈ liuSelbergCorrectedSourcePairs N
    · have hq₂leprod : q.2 ≤ x.2 * q.1 * q.2 := by
        calc
          q.2 ≤ q.1 * q.2 := Nat.le_mul_of_pos_left q.2 hq.1.pos
          _ ≤ x.2 * (q.1 * q.2) :=
            Nat.le_mul_of_pos_left (q.1 * q.2) hp₁Prime.pos
          _ = x.2 * q.1 * q.2 := by rw [mul_assoc]
      have hq₂leN : q.2 ≤ N := hq₂leprod.trans hprodle
      have hresidual : N - x.2 * q.1 * q.2 = x.1 := by
        rw [hq.2.2.2.2.1, Nat.sub_sub_self (Nat.le_of_lt hpN)]
      have hmem : (⟨(x.2, q.1), q.2⟩ : Σ _ : ℕ × ℕ, ℕ) ∈
          liuSelbergCorrectedSourceTripleCarrier N := by
        rw [liuSelbergCorrectedSourceTripleCarrier, mem_sigma,
          mem_filter, mem_filter]
        exact ⟨hsource, ⟨mem_range.mpr (Nat.lt_succ_of_le hq₂leN),
          hq.2.1, hq.2.2.2.1, hprodle⟩, by simpa [hresidual] using hp⟩
      simp [correctedChenSourceEndpointMap, hlower, q, hsource,
        mem_disjSum, hmem]
    · have hupper : q.1 = liuSourceY3 N := by
        rcases hclass with hweight | hendpoint
        · exact (hsource (mem_filter.mpr
            ⟨hweight, hZp₁, hp₁Y, hq.2.2.1⟩)).elim
        · exact hendpoint.elim (fun h => (hlower h).elim) id
      have hdvd : x.2 * liuSourceY3 N ∣ N - x.1 := by
        refine ⟨q.2, ?_⟩
        simpa [hupper, mul_assoc] using hq.2.2.2.2.1.symm
      have hmem : x ∈ correctedChenUpperEndpointCarrier N := by
        rw [correctedChenUpperEndpointCarrier, mem_sigma, mem_filter]
        exact ⟨hp, mem_range.mpr hp₁Y, hp₁Prime, hZp₁, hdvd⟩
      rw [correctedChenSourceEndpointMap, if_neg hlower]
      dsimp only
      rw [if_neg hsource, mem_disjSum]
      refine Or.inr ⟨Sum.inr x, ?_, rfl⟩
      rw [mem_disjSum]
      exact Or.inr ⟨x, hmem, rfl⟩

/-- The selected-factor map is injective on the honest first-factor carrier.
In the source branch the candidate residual is recovered from
`p = N - p₁p₂p₃`; the endpoint branches retain enough coordinates directly. -/
theorem correctedChenSourceEndpointMap_injOn (N : ℕ) :
    Set.InjOn (correctedChenSourceEndpointMap N)
      (↑(correctedChenFirstFactorCarrier N) : Set (Σ _ : ℕ, ℕ)) := by
  intro x hx y hy hxy
  have hx' := hx
  have hy' := hy
  change x ∈ correctedChenFirstFactorCarrier N at hx'
  change y ∈ correctedChenFirstFactorCarrier N at hy'
  rw [correctedChenFirstFactorCarrier, mem_sigma, mem_filter] at hx' hy'
  have hxN : x.1 < N := by
    have h := hx'.1
    rw [correctedChenCandidates, mem_filter] at h
    exact mem_range.mp h.1
  have hyN : y.1 < N := by
    have h := hy'.1
    rw [correctedChenCandidates, mem_filter] at h
    exact mem_range.mp h.1
  let qx := correctedChenSelectedLargeFactors N x.1 x.2
  let qy := correctedChenSelectedLargeFactors N y.1 y.2
  have hqx := correctedChenSelectedLargeFactors_spec hx
  have hqy := correctedChenSelectedLargeFactors_spec hy
  change correctedChenLargeFactorConditions N x.1 x.2 qx at hqx
  change correctedChenLargeFactorConditions N y.1 y.2 qy at hqy
  by_cases hxl : x.2 = liuSourceZ10 N
  · by_cases hyl : y.2 = liuSourceZ10 N
    · have hp : x.1 = y.1 := by
        simpa [correctedChenSourceEndpointMap, hxl, hyl] using hxy
      apply Sigma.ext hp
      simp [hxl, hyl]
    · by_cases hys :
          (y.2, qy.1) ∈ liuSelbergCorrectedSourcePairs N
      · simp [correctedChenSourceEndpointMap, hxl, hyl, qy, hys] at hxy
      · simp [correctedChenSourceEndpointMap, hxl, hyl, qy, hys] at hxy
  · by_cases hyl : y.2 = liuSourceZ10 N
    · by_cases hxs :
          (x.2, qx.1) ∈ liuSelbergCorrectedSourcePairs N
      · simp [correctedChenSourceEndpointMap, hxl, hyl, qx, hxs] at hxy
      · simp [correctedChenSourceEndpointMap, hxl, hyl, qx, hxs] at hxy
    · by_cases hxs :
          (x.2, qx.1) ∈ liuSelbergCorrectedSourcePairs N
      · by_cases hys :
          (y.2, qy.1) ∈ liuSelbergCorrectedSourcePairs N
        · have htriple :
              (⟨(x.2, qx.1), qx.2⟩ : Σ _ : ℕ × ℕ, ℕ) =
                ⟨(y.2, qy.1), qy.2⟩ := by
            simpa [correctedChenSourceEndpointMap, hxl, hyl, qx, qy,
              hxs, hys] using hxy
          have hpair : (x.2, qx.1) = (y.2, qy.1) :=
            congrArg Sigma.fst htriple
          have hp₁ : x.2 = y.2 := congrArg Prod.fst hpair
          have hp₂ : qx.1 = qy.1 := congrArg Prod.snd hpair
          have hp₃ : qx.2 = qy.2 :=
            congrArg (fun z : Σ _ : ℕ × ℕ, ℕ => z.2) htriple
          have hresidual : N - x.1 = N - y.1 := by
            rw [← hqx.2.2.2.2.1, ← hqy.2.2.2.2.1, hp₁, hp₂, hp₃]
          have hp : x.1 = y.1 := by omega
          apply Sigma.ext hp
          simpa using hp₁
        · simp [correctedChenSourceEndpointMap, hxl, hyl, qx, qy,
            hxs, hys] at hxy
      · by_cases hys :
          (y.2, qy.1) ∈ liuSelbergCorrectedSourcePairs N
        · simp [correctedChenSourceEndpointMap, hxl, hyl, qx, qy,
            hxs, hys] at hxy
        · simpa [correctedChenSourceEndpointMap, hxl, hyl, qx, qy,
            hxs, hys] using hxy

/-- Exact finite-carrier accounting gives the corrected first-factor carrier
as a subcardinal of the common source triples plus the two endpoint fibres. -/
theorem correctedChenFirstFactorCarrier_card_le_source_add_endpoints
    {N : ℕ} (hZ : correctedChenZ N = liuSourceZ10 N) :
    (correctedChenFirstFactorCarrier N).card ≤
      (liuSelbergCorrectedSourceTripleCarrier N).card +
        (correctedChenLowerEndpointCarrier N).card +
          (correctedChenUpperEndpointCarrier N).card := by
  calc
    (correctedChenFirstFactorCarrier N).card ≤
        ((liuSelbergCorrectedSourceTripleCarrier N).disjSum
          ((correctedChenLowerEndpointCarrier N).disjSum
            (correctedChenUpperEndpointCarrier N))).card :=
      card_le_card_of_injOn (correctedChenSourceEndpointMap N)
        (fun _ hx => correctedChenSourceEndpointMap_mem hZ hx)
        (correctedChenSourceEndpointMap_injOn N)
    _ = _ := by simp [card_disjSum, add_assoc]

/-- The aggregate corrected triple-factor sum is bounded by the exact common
source count plus the two explicit endpoint-cardinality fibres. -/
theorem correctedChenTripleFactorSum_le_source_add_endpoint_cards
    {N : ℕ} (hZ : correctedChenZ N = liuSourceZ10 N) :
    (correctedChenCandidates N).sum
        (fun p => tripleFactorCount
          (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      liuSelbergCorrectedSourceTripleCount N +
        (correctedChenLowerEndpointCarrier N).card +
          (correctedChenUpperEndpointCarrier N).card := by
  rw [correctedChenTripleFactorSum_eq_firstFactorCarrier_card,
    liuSelbergCorrectedSourceTripleCount_eq_carrier_card]
  exact_mod_cast
    correctedChenFirstFactorCarrier_card_le_source_add_endpoints hZ

/-- The lower endpoint candidates inject into the quotient interval modulo the
fixed lower cutoff. -/
theorem correctedChenLowerEndpointCarrier_card_le_div_add_one (N : ℕ) :
    (correctedChenLowerEndpointCarrier N).card ≤
      N / liuSourceZ10 N + 1 := by
  rw [← card_range (N / liuSourceZ10 N + 1)]
  apply card_le_card_of_injOn
    (fun p => (N - p) / liuSourceZ10 N)
    (t := range (N / liuSourceZ10 N + 1))
  · intro p hp
    change p ∈ correctedChenLowerEndpointCarrier N at hp
    rw [correctedChenLowerEndpointCarrier, mem_filter] at hp
    have hle : (N - p) / liuSourceZ10 N ≤ N / liuSourceZ10 N :=
      Nat.div_le_div_right (Nat.sub_le N p)
    simpa using
      (mem_range.mpr (Nat.lt_succ_of_le hle))
  · intro p hp q hq heq
    change p ∈ correctedChenLowerEndpointCarrier N at hp
    change q ∈ correctedChenLowerEndpointCarrier N at hq
    rw [correctedChenLowerEndpointCarrier, mem_filter] at hp hq
    change (N - p) / liuSourceZ10 N =
      (N - q) / liuSourceZ10 N at heq
    have hpN : p < N := by
      have h := hp.1
      rw [correctedChenCandidates, mem_filter] at h
      exact mem_range.mp h.1
    have hqN : q < N := by
      have h := hq.1
      rw [correctedChenCandidates, mem_filter] at h
      exact mem_range.mp h.1
    have hsub : N - p = N - q := by
      calc
        N - p = (N - p) / liuSourceZ10 N * liuSourceZ10 N :=
          (Nat.div_mul_cancel hp.2).symm
        _ = (N - q) / liuSourceZ10 N * liuSourceZ10 N := by rw [heq]
        _ = N - q := Nat.div_mul_cancel hq.2
    omega

/-- The upper endpoint pairs inject into a quotient interval times the
first-factor interval. -/
theorem correctedChenUpperEndpointCarrier_card_le_product
    (N : ℕ) (hcut : correctedChenZ N = liuSourceZ10 N)
    (hZ : 1 ≤ liuSourceZ10 N) (hY : 1 ≤ liuSourceY3 N) :
    (correctedChenUpperEndpointCarrier N).card ≤
      (N / (liuSourceZ10 N * liuSourceY3 N) + 1) *
        correctedChenY N := by
  let f : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun x =>
    ((N - x.1) / (x.2 * liuSourceY3 N), x.2)
  have hmap : Set.MapsTo f
      (↑(correctedChenUpperEndpointCarrier N) : Set (Σ _ : ℕ, ℕ))
      (↑((range (N / (liuSourceZ10 N * liuSourceY3 N) + 1)).product
        (range (correctedChenY N))) : Set (ℕ × ℕ)) := by
    intro x hx
    change x ∈ correctedChenUpperEndpointCarrier N at hx
    rw [correctedChenUpperEndpointCarrier, mem_sigma, mem_filter] at hx
    change f x ∈
      (range (N / (liuSourceZ10 N * liuSourceY3 N) + 1)).product
        (range (correctedChenY N))
    dsimp [f]
    rw [mem_product, mem_range, mem_range]
    refine ⟨?_, mem_range.mp hx.2.1⟩
    have hzle : liuSourceZ10 N ≤ x.2 := by
      rw [← hcut]
      exact hx.2.2.2.1
    have hdenom :
        liuSourceZ10 N * liuSourceY3 N ≤
          x.2 * liuSourceY3 N :=
      Nat.mul_le_mul_right (liuSourceY3 N) hzle
    have hquotient :
        (N - x.1) / (x.2 * liuSourceY3 N) ≤
          N / (liuSourceZ10 N * liuSourceY3 N) := by
      calc
        (N - x.1) / (x.2 * liuSourceY3 N) ≤
            N / (x.2 * liuSourceY3 N) :=
          Nat.div_le_div_right (Nat.sub_le N x.1)
        _ ≤ N / (liuSourceZ10 N * liuSourceY3 N) :=
          Nat.div_le_div_left hdenom (Nat.mul_pos hZ hY)
    omega
  have hinj : Set.InjOn f
      (↑(correctedChenUpperEndpointCarrier N) : Set (Σ _ : ℕ, ℕ)) := by
    intro x hx y hy heq
    change x ∈ correctedChenUpperEndpointCarrier N at hx
    change y ∈ correctedChenUpperEndpointCarrier N at hy
    rw [correctedChenUpperEndpointCarrier, mem_sigma, mem_filter] at hx hy
    have hp₁ : x.2 = y.2 := congrArg Prod.snd heq
    have hquotient :
        (N - x.1) / (x.2 * liuSourceY3 N) =
          (N - y.1) / (y.2 * liuSourceY3 N) :=
      congrArg Prod.fst heq
    have hxN : x.1 < N := by
      have h := hx.1
      rw [correctedChenCandidates, mem_filter] at h
      exact mem_range.mp h.1
    have hyN : y.1 < N := by
      have h := hy.1
      rw [correctedChenCandidates, mem_filter] at h
      exact mem_range.mp h.1
    have hsub : N - x.1 = N - y.1 := by
      calc
        N - x.1 =
            (N - x.1) / (x.2 * liuSourceY3 N) *
              (x.2 * liuSourceY3 N) :=
          (Nat.div_mul_cancel hx.2.2.2.2).symm
        _ = (N - y.1) / (y.2 * liuSourceY3 N) *
              (y.2 * liuSourceY3 N) := by rw [hquotient, hp₁]
        _ = N - y.1 := Nat.div_mul_cancel hy.2.2.2.2
    have hp : x.1 = y.1 := by omega
    apply Sigma.ext hp
    simpa using hp₁
  calc
    (correctedChenUpperEndpointCarrier N).card ≤
        ((range (N / (liuSourceZ10 N * liuSourceY3 N) + 1)).product
          (range (correctedChenY N))).card :=
      card_le_card_of_injOn f hmap hinj
    _ = (N / (liuSourceZ10 N * liuSourceY3 N) + 1) *
        correctedChenY N := by simp

/-- Together the two cutoff fibres have the unconditional
`13 * N^(9/10)` power-saving bound once the lower floor cutoff has reached
`2`. -/
theorem correctedChenEndpointCards_le_thirteen_mul_rpow_nine_tenths
    (N : ℕ) (hN : 1 ≤ N) (hZ2 : 2 ≤ liuSourceZ10 N) :
    ((correctedChenLowerEndpointCarrier N).card : ℝ) +
        (correctedChenUpperEndpointCarrier N).card ≤
      13 * (N : ℝ) ^ (9 / 10 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNreal
  let X : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  let Y : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
  let Q : ℝ := (N : ℝ) ^ (17 / 30 : ℝ)
  let P : ℝ := (N : ℝ) ^ (9 / 10 : ℝ)
  have hXone : 1 ≤ X := Real.one_le_rpow hNreal (by norm_num)
  have hYone : 1 ≤ Y := Real.one_le_rpow hNreal (by norm_num)
  have hPone : 1 ≤ P := Real.one_le_rpow hNreal (by norm_num)
  have hzhalf : X / 2 < (liuSourceZ10 N : ℝ) := by
    simpa [X, liuSourceZ10] using Nat.div_two_lt_floor hXone
  have hyhalf : Y / 2 < (liuSourceY3 N : ℝ) := by
    simpa [Y, liuSourceY3] using Nat.div_two_lt_floor hYone
  have hYpos : 1 ≤ liuSourceY3 N := by
    have hpos : (0 : ℝ) < (liuSourceY3 N : ℝ) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < Y / 2) hyhalf.le
    exact_mod_cast hpos
  have hcut : correctedChenZ N = liuSourceZ10 N :=
    correctedChenZ_eq_liuSourceZ10_of_two_le hZ2
  have hceil : (correctedChenY N : ℝ) ≤ 2 * Y := by
    simpa [correctedChenY, Y] using
      (Nat.ceil_le_two_mul (show (2 : ℝ)⁻¹ ≤ Y by linarith))
  have hPX : P * X = (N : ℝ) := by
    dsimp [P, X]
    rw [← Real.rpow_add hNpos]
    norm_num
  have hQXY : Q * X * Y = (N : ℝ) := by
    dsimp [Q, X, Y]
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    norm_num
  have hQY : Q * Y = P := by
    dsimp [Q, Y, P]
    rw [← Real.rpow_add hNpos]
    norm_num
  have hYP : Y ≤ P := by
    dsimp [Y, P]
    exact Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num)
  have hzpos : (0 : ℝ) < liuSourceZ10 N := by positivity
  have hypos : (0 : ℝ) < liuSourceY3 N := by positivity
  have hdivZ : (N : ℝ) / liuSourceZ10 N < 2 * P := by
    rw [div_lt_iff₀ hzpos]
    have hmul :=
      mul_lt_mul_of_pos_left hzhalf (show 0 < 2 * P by positivity)
    calc
      (N : ℝ) = P * X := hPX.symm
      _ = (2 * P) * (X / 2) := by ring
      _ < (2 * P) * liuSourceZ10 N := hmul
  have hzy : X * Y / 4 <
      (liuSourceZ10 N : ℝ) * liuSourceY3 N := by
    calc
      X * Y / 4 = (X / 2) * (Y / 2) := by ring
      _ < (liuSourceZ10 N : ℝ) * liuSourceY3 N :=
        mul_lt_mul hzhalf hyhalf.le
          (show 0 < Y / 2 by positivity)
          (show (0 : ℝ) ≤ liuSourceZ10 N by positivity)
  have hzypos :
      (0 : ℝ) < (liuSourceZ10 N : ℝ) * liuSourceY3 N := by
    positivity
  have hdivZY :
      (N : ℝ) /
          ((liuSourceZ10 N : ℝ) * liuSourceY3 N) < 4 * Q := by
    rw [div_lt_iff₀ hzypos]
    have hmul :=
      mul_lt_mul_of_pos_left hzy (show 0 < 4 * Q by positivity)
    calc
      (N : ℝ) = Q * X * Y := hQXY.symm
      _ = (4 * Q) * (X * Y / 4) := by ring
      _ < (4 * Q) *
          ((liuSourceZ10 N : ℝ) * liuSourceY3 N) := hmul
  have hlower :
      ((correctedChenLowerEndpointCarrier N).card : ℝ) ≤ 3 * P := by
    calc
      ((correctedChenLowerEndpointCarrier N).card : ℝ) ≤
          ((N / liuSourceZ10 N + 1 : ℕ) : ℝ) := by
        exact_mod_cast
          correctedChenLowerEndpointCarrier_card_le_div_add_one N
      _ = ((N / liuSourceZ10 N : ℕ) : ℝ) + 1 := by norm_num
      _ ≤ (N : ℝ) / liuSourceZ10 N + 1 :=
        add_le_add Nat.cast_div_le le_rfl
      _ ≤ 2 * P + 1 := add_le_add hdivZ.le le_rfl
      _ ≤ 3 * P := by linarith
  have hupper :
      ((correctedChenUpperEndpointCarrier N).card : ℝ) ≤ 10 * P := by
    have hqcast :
        ((N / (liuSourceZ10 N * liuSourceY3 N) : ℕ) : ℝ) + 1 ≤
          (N : ℝ) /
              ((liuSourceZ10 N : ℝ) * liuSourceY3 N) + 1 := by
      simpa only [Nat.cast_mul] using
        add_le_add
          (Nat.cast_div_le :
            ((N / (liuSourceZ10 N * liuSourceY3 N) : ℕ) : ℝ) ≤
              (N : ℝ) / (liuSourceZ10 N * liuSourceY3 N : ℕ))
          le_rfl
    calc
      ((correctedChenUpperEndpointCarrier N).card : ℝ) ≤
          (((N / (liuSourceZ10 N * liuSourceY3 N) + 1) *
            correctedChenY N : ℕ) : ℝ) := by
        exact_mod_cast
          correctedChenUpperEndpointCarrier_card_le_product
            N hcut (by omega) hYpos
      _ = (((N / (liuSourceZ10 N * liuSourceY3 N) : ℕ) : ℝ) + 1) *
          correctedChenY N := by norm_num
      _ ≤ ((N : ℝ) /
              ((liuSourceZ10 N : ℝ) * liuSourceY3 N) + 1) *
            (2 * Y) :=
        mul_le_mul hqcast hceil (by positivity) (by positivity)
      _ ≤ (4 * Q + 1) * (2 * Y) :=
        mul_le_mul_of_nonneg_right
          (add_le_add hdivZY.le le_rfl) (by positivity)
      _ = 8 * P + 2 * Y := by rw [← hQY]; ring
      _ ≤ 10 * P := by linarith
  dsimp [P] at hlower hupper ⊢
  linarith

/-- The complete corrected triple-factor sum differs from the common Liu
source count by at most `13 * N^(9/10)`. -/
theorem correctedChenTripleFactorSum_le_source_add_thirteen_mul_rpow_nine_tenths
    (N : ℕ) (hN : 1 ≤ N) (hZ2 : 2 ≤ liuSourceZ10 N) :
    (correctedChenCandidates N).sum
        (fun p => tripleFactorCount
          (N - p) (correctedChenZ N) (correctedChenY N)) ≤
      liuSelbergCorrectedSourceTripleCount N +
        13 * (N : ℝ) ^ (9 / 10 : ℝ) := by
  have hcut := correctedChenZ_eq_liuSourceZ10_of_two_le hZ2
  calc
    (correctedChenCandidates N).sum
          (fun p => tripleFactorCount
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        liuSelbergCorrectedSourceTripleCount N +
          (correctedChenLowerEndpointCarrier N).card +
            (correctedChenUpperEndpointCarrier N).card :=
      correctedChenTripleFactorSum_le_source_add_endpoint_cards hcut
    _ ≤ liuSelbergCorrectedSourceTripleCount N +
          13 * (N : ℝ) ^ (9 / 10 : ℝ) := by
      have hendpoint :=
        correctedChenEndpointCards_le_thirteen_mul_rpow_nine_tenths
          N hN hZ2
      linarith

/-- A fixed power saving is eventually bounded at any inverse-log scale.
This step is shared by the endpoint fibres and the paper-modulus residual. -/
private theorem eventually_mul_rpow_le_div_log_rpow
    (C A δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ (1 - δ) ≤ C * N / Real.log N ^ A := by
  have hreal : ∀ᶠ x : ℝ in atTop, Real.log x ^ A ≤ x ^ δ := by
    have hbound := (isLittleO_log_rpow_rpow_atTop A hδ).bound
      (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) A),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) δ),
      one_mul] at hx
    exact hx
  have hnat : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ A ≤ (N : ℝ) ^ δ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with N hgrowth hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdenom : 0 < Real.log (N : ℝ) ^ A :=
    Real.rpow_pos_of_pos hlogpos A
  have hcombine : (N : ℝ) ^ (1 - δ) * Real.log N ^ A ≤ N := by
    calc
      (N : ℝ) ^ (1 - δ) * Real.log N ^ A ≤
          (N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg hNpos.le _)
      _ = N := by rw [← Real.rpow_add hNpos, sub_add_cancel, Real.rpow_one]
  rw [le_div_iff₀ hdenom]
  calc
    (C * (N : ℝ) ^ (1 - δ)) * Real.log N ^ A =
        C * ((N : ℝ) ^ (1 - δ) * Real.log N ^ A) := by ring
    _ ≤ C * N := mul_le_mul_of_nonneg_left hcombine hC

/-- Hence the endpoint complement is smaller than every fixed inverse-log
scale. -/
theorem eventually_correctedChenTripleFactorSum_le_source_add_div_log_rpow
    (A : ℝ) (_hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      (correctedChenCandidates N).sum
          (fun p => tripleFactorCount
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        liuSelbergCorrectedSourceTripleCount N +
          13 * N / Real.log N ^ A := by
  have hscale := eventually_mul_rpow_le_div_log_rpow
    13 A (1 / 10) (by norm_num) (by norm_num)
  have hZ2 : ∀ᶠ N : ℕ in atTop, 2 ≤ liuSourceZ10 N := by
    simpa [liuSourceZ10,
      MathlibNt.SieveTheory.PrimeReciprocalLogScale.rpowFloor] using
      (MathlibNt.SieveTheory.PrimeReciprocalLogScale.eventually_two_le_rpowFloor
        (a := (1 / 10 : ℝ)) (by norm_num))
  filter_upwards [hscale, hZ2, eventually_ge_atTop (1 : ℕ)] with
      N hscaleN hZ2N hN
  have hscaleN' : 13 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
      13 * N / Real.log N ^ A := by
    convert hscaleN using 1; norm_num
  exact (correctedChenTripleFactorSum_le_source_add_thirteen_mul_rpow_nine_tenths
    N hN hZ2N).trans (add_le_add le_rfl hscaleN')

/-- Each fixed source-pair residual injects into the prime factors of Liu's
paper modulus via the candidate residual `N - p₁p₂p₃`. -/
theorem liuSelbergCorrectedTripleQResidual_le_primeFactors_card
    (N : ℕ) (epsilon : ℝ) (p₁ p₂ : ℕ)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    liuSelbergCorrectedTripleQResidual N epsilon p₁ p₂ ≤
      ((liuPaperQModulus N epsilon).primeFactors.card : ℝ) := by
  classical
  let P := (range (N + 1)).filter (fun p₃ =>
    p₃.Prime ∧ p₂ ≤ p₃ ∧ p₁ * p₂ * p₃ ≤ N)
  let R := P.filter (fun p₃ =>
    N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N ∧
      N - p₁ * p₂ * p₃ ∣ liuPaperQModulus N epsilon)
  have hcard :
      R.card ≤ (liuPaperQModulus N epsilon).primeFactors.card := by
    apply Finset.card_le_card_of_injOn
      (fun p₃ => N - p₁ * p₂ * p₃)
    · intro p₃ hp₃
      have hp₃R : p₃ ∈ R := hp₃
      rw [mem_filter] at hp₃R
      have hrCandidate := hp₃R.2.1
      have hrPrime : (N - p₁ * p₂ * p₃).Prime := by
        rw [correctedChenCandidates, mem_filter] at hrCandidate
        exact hrCandidate.2.1
      exact (Nat.mem_primeFactors_of_ne_zero
        (liuPaperQModulus_squarefree N epsilon).ne_zero).mpr
          ⟨hrPrime, hp₃R.2.2⟩
    · intro p₃ hp₃ q₃ hq₃ heq
      have hp₃P : p₃ ∈ P := (mem_filter.mp hp₃).1
      have hq₃P : q₃ ∈ P := (mem_filter.mp hq₃).1
      have hp₃le : p₁ * p₂ * p₃ ≤ N := (mem_filter.mp hp₃P).2.2.2
      have hq₃le : p₁ * p₂ * q₃ ≤ N := (mem_filter.mp hq₃P).2.2.2
      change N - p₁ * p₂ * p₃ = N - p₁ * p₂ * q₃ at heq
      have hprod : p₁ * p₂ * p₃ = p₁ * p₂ * q₃ := by
        calc
          p₁ * p₂ * p₃ = N - (N - p₁ * p₂ * p₃) :=
            (Nat.sub_sub_self hp₃le).symm
          _ = N - (N - p₁ * p₂ * q₃) := congrArg (N - ·) heq
          _ = p₁ * p₂ * q₃ := Nat.sub_sub_self hq₃le
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp₁.pos hp₂.pos) (by
        simpa [mul_assoc] using hprod)
  unfold liuSelbergCorrectedTripleQResidual
  rw [sum_boole]
  change ((R.card : ℕ) : ℝ) ≤ _
  exact_mod_cast hcard

/-- Reindex an arbitrary sum against Liu's characteristic source by its unique
admissible ordered prime pair. -/
theorem sum_liuWeight_mul_eq_sum_pairs
    (N z y : ℕ) (F : ℕ → ℝ) :
    (∑ a ∈ range (N + 1), liuWeight N z y a * F a) =
      ∑ p ∈ liuWeightPairs N z y, F (p.1 * p.2) := by
  classical
  calc
    (∑ a ∈ range (N + 1), liuWeight N z y a * F a) =
        ∑ a ∈ (range (N + 1)).filter (LiuWeightSupport N z y), F a := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : LiuWeightSupport N z y a <;> simp [liuWeight, ha]
    _ = ∑ p ∈ liuWeightPairs N z y, F (p.1 * p.2) := by
      symm
      apply sum_bij (fun p _ => p.1 * p.2)
      · intro p hp
        rw [mem_filter]
        exact ⟨mem_range.mpr (Nat.lt_succ_iff.mpr
            (liuWeightSupport_le ⟨p, hp, rfl⟩)),
          ⟨p, hp, rfl⟩⟩
      · intro p hp q hq hpq
        have hu := liuPairConditions_unique
          (mem_liuWeightPairs.mp hp) (mem_liuWeightPairs.mp hq) hpq
        exact Prod.ext hu.1 hu.2
      · intro a ha
        rw [mem_filter] at ha
        rcases ha.2 with ⟨p, hp, hpa⟩
        exact ⟨p, hp, hpa⟩
      · intro p _
        rfl

/-- The unique product map identifies Liu's pair carrier with the supported
source integers. -/
theorem liuWeightPairs_card_eq_support_card (N z y : ℕ) :
    (liuWeightPairs N z y).card =
      ((Icc 1 N).filter (LiuWeightSupport N z y)).card := by
  classical
  apply Finset.card_bij (fun p _ => p.1 * p.2)
  · intro p hp
    have hpair := mem_liuWeightPairs.mp hp
    exact mem_filter.mpr
      ⟨mem_Icc.mpr ⟨Nat.mul_pos hpair.1.pos hpair.2.1.pos,
        liuWeightSupport_le ⟨p, hp, rfl⟩⟩,
        ⟨p, hp, rfl⟩⟩
  · intro p hp q hq hpq
    have hu := liuPairConditions_unique
      (mem_liuWeightPairs.mp hp) (mem_liuWeightPairs.mp hq) hpq
    exact Prod.ext hu.1 hu.2
  · intro a ha
    rcases (mem_filter.mp ha).2 with ⟨p, hp, hpa⟩
    exact ⟨p, hp, hpa⟩

/-- Every prime factor of Liu's paper modulus lies below its defining cutoff. -/
theorem liuPaperQModulus_primeFactors_card_le_cutoff_add_one
    (N : ℕ) (epsilon : ℝ) :
    (liuPaperQModulus N epsilon).primeFactors.card ≤
      paperQSourceCutoff N epsilon + 1 := by
  calc
    (liuPaperQModulus N epsilon).primeFactors.card ≤
        (range (paperQSourceCutoff N epsilon + 1)).card := by
      apply card_le_card
      intro r hr
      have hrPrime := Nat.prime_of_mem_primeFactors hr
      have hrCutoff :=
        (prime_dvd_liuPaperQModulus (N := N) (epsilon := epsilon) hrPrime).mp
          (Nat.dvd_of_mem_primeFactors hr) |>.1
      exact mem_range.mpr (Nat.lt_succ_of_le hrCutoff)
    _ = paperQSourceCutoff N epsilon + 1 := card_range _

/-- Summing the fixed-pair injection bounds the complete source residual by the
source-pair cardinality times the number of prime factors of the paper modulus. -/
theorem liuSelbergCorrectedSourceTripleQResidual_le_pair_card_mul_primeFactors_card
    (N : ℕ) (epsilon : ℝ) :
    liuSelbergCorrectedSourceTripleQResidual N epsilon ≤
      ((liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card : ℝ) *
        ((liuPaperQModulus N epsilon).primeFactors.card : ℝ) := by
  classical
  let S := liuSelbergCorrectedSourcePairs N
  let P := liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)
  let M : ℝ := (liuPaperQModulus N epsilon).primeFactors.card
  calc
    liuSelbergCorrectedSourceTripleQResidual N epsilon =
        ∑ p ∈ S, liuSelbergCorrectedTripleQResidual N epsilon p.1 p.2 := rfl
    _ ≤ ∑ _p ∈ S, M := by
      apply sum_le_sum
      intro p hp
      have hpP : p ∈ P := by
        exact (mem_filter.mp hp).1
      have hcond := mem_liuWeightPairs.mp hpP
      exact liuSelbergCorrectedTripleQResidual_le_primeFactors_card
        N epsilon p.1 p.2 hcond.1 hcond.2.1
    _ = (S.card : ℝ) * M := by simp
    _ ≤ (P.card : ℝ) * M := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_le_card (filter_subset _ _)
      · positivity
    _ = _ := rfl

/-- A completely finite envelope for the modulus-dividing source residual. -/
theorem liuSelbergCorrectedSourceTripleQResidual_le_source_cutoff_envelope
    (N : ℕ) (epsilon : ℝ) :
    liuSelbergCorrectedSourceTripleQResidual N epsilon ≤
      ((Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) + 1 : ℕ) : ℝ) *
        (paperQSourceCutoff N epsilon + 1 : ℕ) := by
  calc
    liuSelbergCorrectedSourceTripleQResidual N epsilon ≤
        ((liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card : ℝ) *
          ((liuPaperQModulus N epsilon).primeFactors.card : ℝ) :=
      liuSelbergCorrectedSourceTripleQResidual_le_pair_card_mul_primeFactors_card
        N epsilon
    _ ≤ ((Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) + 1 : ℕ) : ℝ) *
          (paperQSourceCutoff N epsilon + 1 : ℕ) := by
      apply mul_le_mul
      · exact_mod_cast (liuWeightPairs_card_eq_support_card N
          (liuSourceZ10 N) (liuSourceY3 N)).trans_le
            (liuWeight_support_card_le_ceil_rpow_two_thirds N
              (liuSourceZ10 N) (liuSourceY3 N))
      · exact_mod_cast
          liuPaperQModulus_primeFactors_card_le_cutoff_add_one N epsilon
      · positivity
      · positivity

/-- The source support and the paper-modulus cutoff give an unconditional
`N^(11/12)` power saving for the exceptional residual. -/
theorem liuSelbergCorrectedSourceTripleQResidual_le_six_mul_rpow_eleven_twelfths
    (N : ℕ) (epsilon : ℝ) (hN : 1 ≤ N) (hepsilon : 0 ≤ epsilon) :
    liuSelbergCorrectedSourceTripleQResidual N epsilon ≤
      6 * (N : ℝ) ^ (11 / 12 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNreal
  have hNnonneg : (0 : ℝ) ≤ N := hNpos.le
  let X : ℝ := (N : ℝ) ^ (2 / 3 : ℝ)
  let W : ℝ := (N : ℝ) ^ (1 / 4 : ℝ)
  have hXone : 1 ≤ X := Real.one_le_rpow hNreal (by norm_num)
  have hWone : 1 ≤ W := Real.one_le_rpow hNreal (by norm_num)
  have hceil : ((Nat.ceil X + 1 : ℕ) : ℝ) ≤ 3 * X := by
    have hc := Nat.ceil_le_floor_add_one X
    have hf := Nat.floor_le (Real.rpow_nonneg hNnonneg (2 / 3 : ℝ))
    have hc' : (Nat.ceil X : ℝ) ≤ (Nat.floor X : ℝ) + 1 := by
      exact_mod_cast hc
    rw [Nat.cast_add, Nat.cast_one]
    dsimp [X] at hf hc' hXone ⊢
    linarith
  have hcutoff :
      ((paperQSourceCutoff N epsilon + 1 : ℕ) : ℝ) ≤ 2 * W := by
    have hexponent : 1 / 4 - epsilon / 2 ≤ (1 / 4 : ℝ) := by linarith
    have hpow :
        (N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ) ≤ W := by
      dsimp [W]
      exact Real.rpow_le_rpow_of_exponent_le hNreal hexponent
    have hfloor :
        (Nat.floor ((N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ)) : ℝ) ≤
          (N : ℝ) ^ (1 / 4 - epsilon / 2 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hNnonneg _)
    simp only [paperQSourceCutoff, Nat.cast_add, Nat.cast_one]
    linarith
  calc
    liuSelbergCorrectedSourceTripleQResidual N epsilon ≤
        ((Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) + 1 : ℕ) : ℝ) *
          (paperQSourceCutoff N epsilon + 1 : ℕ) :=
      liuSelbergCorrectedSourceTripleQResidual_le_source_cutoff_envelope
        N epsilon
    _ ≤ (3 * X) * (2 * W) :=
      mul_le_mul hceil hcutoff (by positivity) (by positivity)
    _ = 6 * ((N : ℝ) ^ (2 / 3 : ℝ) *
          (N : ℝ) ^ (1 / 4 : ℝ)) := by
      dsimp [X, W]
      ring
    _ = 6 * (N : ℝ) ^ (11 / 12 : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num

/-- Consequently the modulus-dividing source residual is smaller than every
fixed inverse logarithmic scale. -/
theorem eventually_liuSelbergCorrectedSourceTripleQResidual_le_div_log_rpow
    (epsilon A : ℝ) (hepsilon : 0 ≤ epsilon) (_hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      liuSelbergCorrectedSourceTripleQResidual N epsilon ≤
        6 * N / Real.log N ^ A := by
  have hscale := eventually_mul_rpow_le_div_log_rpow
    6 A (1 / 12) (by norm_num) (by norm_num)
  filter_upwards [hscale, eventually_ge_atTop (1 : ℕ)] with N hscaleN hN
  have hscaleN' : 6 * (N : ℝ) ^ (11 / 12 : ℝ) ≤
      6 * N / Real.log N ^ A := by
    convert hscaleN using 1; norm_num
  exact (liuSelbergCorrectedSourceTripleQResidual_le_six_mul_rpow_eleven_twelfths
    N epsilon hN hepsilon).trans hscaleN'

/-- Liu's square count is exactly the sum of its Selberg packets over the
admissible source pairs and third primes. -/
theorem liuSelbergSquareCount_eq_sum_pairs
    (N : ℕ) (epsilon : ℝ) (lambda : ℕ → ℝ) :
    liuSelbergSquareCount N epsilon lambda =
      ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
        ∑ p₃ ∈ (range (N + 1)).filter
            (fun p₃ => p₃.Prime ∧ (p.1 * p.2) * p₃ ≤ N),
          (∑ d ∈ (liuSelbergLambdaSourceCarrier N epsilon).filter
              (fun d => d ∣ N - (p.1 * p.2) * p₃), lambda d) ^ 2 := by
  unfold liuSelbergSquareCount
  exact sum_liuWeight_mul_eq_sum_pairs N
    (liuSourceZ10 N) (liuSourceY3 N) _

/-- Away from candidate residual primes dividing Liu's paper modulus, one
corrected triple slice is bounded by the corresponding optimal Selberg square
slice.  The exceptional primes are retained exactly in the final summand. -/
theorem liuSelbergCorrectedTripleSlice_le_square_add_QResidual
    {N p₁ p₂ : ℕ} {epsilon : ℝ}
    (hEven : Even N) (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    liuSelbergCorrectedTripleSlice N p₁ p₂ ≤
      (∑ p₃ ∈ (range (N + 1)).filter
          (fun p₃ => p₃.Prime ∧ (p₁ * p₂) * p₃ ≤ N),
        (∑ d ∈ (liuSelbergLambdaSourceCarrier N epsilon).filter
            (fun d => d ∣ N - (p₁ * p₂) * p₃),
          liuSelbergOptimalLambda N epsilon d) ^ 2) +
      liuSelbergCorrectedTripleQResidual N epsilon p₁ p₂ := by
  classical
  let P := (range (N + 1)).filter (fun p₃ =>
    p₃.Prime ∧ p₂ ≤ p₃ ∧ p₁ * p₂ * p₃ ≤ N)
  let C := liuSelbergLambdaSourceCarrier N epsilon
  let Q := liuPaperQModulus N epsilon
  have hpacket {p₃ : ℕ} (hp₃ : p₃ ∈ P)
      (hc : N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N)
      (hQ : ¬N - p₁ * p₂ * p₃ ∣ Q) :
      (∑ d ∈ C.filter (fun d => d ∣ N - (p₁ * p₂) * p₃),
          liuSelbergOptimalLambda N epsilon d) = 1 := by
    let r := N - p₁ * p₂ * p₃
    have hrPrime : r.Prime := by
      rw [correctedChenCandidates, mem_filter] at hc
      exact hc.2.1
    have h1C : 1 ∈ C := by
      exact mem_liuSelbergLambdaSourceCarrier.mpr ⟨one_dvd _, hR⟩
    rw [sum_eq_single 1]
    · exact liuSelbergOptimalLambda_one hEven hR
    · intro d hd hd1
      exfalso
      have hdr : d ∣ r := (mem_filter.mp hd).2
      rcases (Nat.dvd_prime hrPrime).mp hdr with hdone | hdr
      · exact hd1 hdone
      · apply hQ
        change r ∣ Q
        rw [← hdr]
        exact (mem_liuSelbergLambdaSourceCarrier.mp (mem_filter.mp hd).1).1
    · intro h1
      exact (h1 (mem_filter.mpr ⟨h1C, one_dvd _⟩)).elim
  have hsplit :
      liuSelbergCorrectedTripleSlice N p₁ p₂ =
        (∑ p₃ ∈ P,
          if N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N ∧
              ¬N - p₁ * p₂ * p₃ ∣ Q then 1 else 0) +
        liuSelbergCorrectedTripleQResidual N epsilon p₁ p₂ := by
    unfold liuSelbergCorrectedTripleSlice
      liuSelbergCorrectedTripleQResidual
    change (∑ p₃ ∈ P, _) = (∑ p₃ ∈ P, _) + ∑ p₃ ∈ P, _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p₃ hp₃
    by_cases hc : N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N <;>
      by_cases hQ : N - p₁ * p₂ * p₃ ∣ Q <;>
        simp [hc, hQ, Q]
  rw [hsplit]
  apply add_le_add
  · calc
      (∑ p₃ ∈ P,
          if N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N ∧
              ¬N - p₁ * p₂ * p₃ ∣ Q then 1 else 0) ≤
          ∑ p₃ ∈ P,
            (∑ d ∈ C.filter (fun d => d ∣ N - (p₁ * p₂) * p₃),
              liuSelbergOptimalLambda N epsilon d) ^ 2 := by
        apply sum_le_sum
        intro p₃ hp₃
        by_cases hc : N - p₁ * p₂ * p₃ ∈ correctedChenCandidates N
        · by_cases hQ : N - p₁ * p₂ * p₃ ∣ Q
          · simp [hQ, sq_nonneg]
          · rw [if_pos ⟨hc, hQ⟩, hpacket hp₃ hc hQ]
            norm_num
        · simp [hc, sq_nonneg]
      _ ≤ ∑ p₃ ∈ (range (N + 1)).filter
            (fun p₃ => p₃.Prime ∧ (p₁ * p₂) * p₃ ≤ N),
            (∑ d ∈ C.filter (fun d => d ∣ N - (p₁ * p₂) * p₃),
              liuSelbergOptimalLambda N epsilon d) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p₃ hp₃
          rw [mem_filter] at hp₃ ⊢
          exact ⟨hp₃.1, hp₃.2.1, by simpa [mul_assoc] using hp₃.2.2.2⟩
        · intro p₃ hp₃ hnot
          exact sq_nonneg _
  · exact le_rfl

/-- On the exact common source-pair region, the corrected triple count is
bounded by Liu's optimal square count plus only the explicit modulus-dividing
candidate-prime residual. -/
theorem liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual
    {N : ℕ} {epsilon : ℝ}
    (hEven : Even N) (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    liuSelbergCorrectedSourceTripleCount N ≤
      liuSelbergSquareCount N epsilon
          (liuSelbergOptimalLambda N epsilon) +
        liuSelbergCorrectedSourceTripleQResidual N epsilon := by
  classical
  let S := liuSelbergCorrectedSourcePairs N
  let P := liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)
  let F : ℕ × ℕ → ℝ := fun p =>
    ∑ p₃ ∈ (range (N + 1)).filter
        (fun p₃ => p₃.Prime ∧ (p.1 * p.2) * p₃ ≤ N),
      (∑ d ∈ (liuSelbergLambdaSourceCarrier N epsilon).filter
          (fun d => d ∣ N - (p.1 * p.2) * p₃),
        liuSelbergOptimalLambda N epsilon d) ^ 2
  have hlocal :
      liuSelbergCorrectedSourceTripleCount N ≤
        (∑ p ∈ S, F p) +
          liuSelbergCorrectedSourceTripleQResidual N epsilon := by
    unfold liuSelbergCorrectedSourceTripleCount
      liuSelbergCorrectedSourceTripleQResidual
    change (∑ p ∈ S, liuSelbergCorrectedTripleSlice N p.1 p.2) ≤
      (∑ p ∈ S, F p) +
        ∑ p ∈ S, liuSelbergCorrectedTripleQResidual N epsilon p.1 p.2
    rw [← sum_add_distrib]
    exact sum_le_sum fun p hp =>
      liuSelbergCorrectedTripleSlice_le_square_add_QResidual hEven hR
  calc
    liuSelbergCorrectedSourceTripleCount N ≤
        (∑ p ∈ S, F p) +
          liuSelbergCorrectedSourceTripleQResidual N epsilon := hlocal
    _ ≤ (∑ p ∈ P, F p) +
          liuSelbergCorrectedSourceTripleQResidual N epsilon := by
      apply add_le_add
      · apply sum_le_sum_of_subset_of_nonneg
        · exact filter_subset _ _
        · intro p hp hnot
          exact sum_nonneg fun p₃ hp₃ => sq_nonneg _
      · exact le_rfl
    _ = liuSelbergSquareCount N epsilon
          (liuSelbergOptimalLambda N epsilon) +
        liuSelbergCorrectedSourceTripleQResidual N epsilon := by
      rw [liuSelbergSquareCount_eq_sum_pairs]

/-- The inverse-log residual contract between the corrected ordered-triple sum
and Liu's exact source-pair count. -/
def LiuSelbergCorrectedSourceComplementResidualBound : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        (correctedChenCandidates N).sum
            (fun p => tripleFactorCount
              (N - p) (correctedChenZ N) (correctedChenY N)) ≤
          liuSelbergCorrectedSourceTripleCount N +
            C * N / Real.log N ^ A

/-- The explicit endpoint-fibre power saving unconditionally inhabits the
source-complement residual contract. -/
theorem liuSelbergCorrectedSourceComplementResidualBound :
   LiuSelbergCorrectedSourceComplementResidualBound := by
 intro A hA
 refine ⟨13, by norm_num, ?_⟩
 filter_upwards
     [eventually_correctedChenTripleFactorSum_le_source_add_div_log_rpow A hA]
     with N hN
 intro _hEven
 exact hN

/-- The canonical Pan--Wang--Ding square estimate controls the complete
corrected Chen triple term unconditionally at the endpoint seam.  The
paper-modulus residual is discharged by the unconditional `N^(11/12)` estimate
above. -/
theorem LiuPanCanonicalCoprimeTheorem.eventually_correctedChenOmegaTriple_le
   (hPan : LiuPanCanonicalCoprimeTheorem)
   (epsilon A : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        (correctedChenCandidates N).sum
            (fun p => tripleFactorCount
              (N - p) (correctedChenZ N) (correctedChenY N)) ≤
          3.94033 * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              N / Real.log N ^ 2 +
            C * N / Real.log N ^ A := by
  obtain ⟨Cend, hCend, hComplementN⟩ :=
    liuSelbergCorrectedSourceComplementResidualBound A hA
  obtain ⟨Cpan, hCpan, hSquare⟩ :=
    hPan.eventually_liuSelbergOptimalSquareCount_le_even
      epsilon A hepsilon hepsilon_le hA
  rw [eventually_inf_principal] at hSquare
  have hCutoff :=
    eventually_one_le_paperQSourceCutoff_of_le_evenAssemblyEpsilon0 hepsilon_le
  have hQ :=
    eventually_liuSelbergCorrectedSourceTripleQResidual_le_div_log_rpow
      epsilon A hepsilon.le hA
  refine ⟨Cend + Cpan + 6, by positivity, ?_⟩
  filter_upwards [hComplementN, hSquare, hCutoff, hQ] with
      N hComplementN hSquareN hR hQN
  intro hEven
  have hSource :=
    liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual
      (epsilon := epsilon) hEven hR
  calc
    (correctedChenCandidates N).sum
          (fun p => tripleFactorCount
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        liuSelbergCorrectedSourceTripleCount N +
          Cend * N / Real.log N ^ A := hComplementN hEven
    _ ≤ (liuSelbergSquareCount N epsilon
            (liuSelbergOptimalLambda N epsilon) +
          liuSelbergCorrectedSourceTripleQResidual N epsilon) +
        Cend * N / Real.log N ^ A :=
      add_le_add hSource le_rfl
    _ ≤ (3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              N / Real.log N ^ 2 +
          Cpan * N / Real.log N ^ A +
          6 * N / Real.log N ^ A) +
        Cend * N / Real.log N ^ A := by
      exact add_le_add
        (add_le_add (hSquareN hEven) hQN) le_rfl
    _ = 3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              N / Real.log N ^ 2 +
          (Cend + Cpan + 6) * N / Real.log N ^ A := by ring

/-- The canonical Liu--Pan coprime theorem produces the strict ordered-triple
upper-bound contract consumed by the generic Jurkat--Richert endpoint.  This is
a producer of the remaining penalty input, not another Chen endpoint consumer. -/
theorem liu_pan_wang_ding_strictTriple_upper
    (hPan : LiuPanCanonicalCoprimeTheorem) :
    ChenJurkatRichertTriplePenaltyUpperBound := by
  obtain ⟨C, hC, htriple⟩ :=
    hPan.eventually_correctedChenOmegaTriple_le
      liuEvenAssemblyEpsilon0 (3 : ℝ)
        liuEvenAssemblyEpsilon0_pos le_rfl (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [htriple] with N htripleN
  intro hEven
  unfold correctedChenTriplePenalty
  convert htripleN hEven using 1; norm_num [Real.rpow_natCast]

/-- Backward-compatible wrapper for the stronger canonical source contract. -/
theorem LiuPanWangDingTheorem.eventually_correctedChenOmegaTriple_le
    (hPan : LiuPanWangDingTheorem)
    (epsilon A : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        (correctedChenCandidates N).sum
            (fun p => tripleFactorCount
              (N - p) (correctedChenZ N) (correctedChenY N)) ≤
          3.94033 * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              N / Real.log N ^ 2 +
            C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_correctedChenOmegaTriple_le
    epsilon A hepsilon hepsilon_le hA

/-- An inverse-log remainder is absorbed into an arbitrary positive multiple of
the genuine Liu singular-series scale.  The uniform lower bound is the positive
universal Euler product, since every divisor correction factor is at least one. -/
theorem eventually_inverse_log_remainder_le_liuSingularSeries
    (C ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
        ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun N : ℕ => C / Real.log (N : ℝ)) atTop (nhds 0) :=
    hlog.const_div_atTop C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C / Real.log (N : ℝ) ≤
        ρ * SingularSeries.liuUniversalProduct :=
    hratio.eventually (Iic_mem_nhds
      (mul_pos hρ SingularSeries.liuUniversalProduct_pos))
  filter_upwards [hsmall, eventually_ge_atTop 2] with N hsmallN hN
  have hcoef : C / Real.log (N : ℝ) ≤
      ρ * SingularSeries.liuSingularSeries N :=
    hsmallN.trans (mul_le_mul_of_nonneg_left
      (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hρ.le)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hXnonneg :
      0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
    positivity
  calc
    C * (N : ℝ) / Real.log N ^ (3 : ℕ) =
        (C / Real.log N) *
          ((N : ℝ) / Real.log N ^ (2 : ℕ)) := by
      field_simp [hlogpos.ne']
    _ ≤ (ρ * SingularSeries.liuSingularSeries N) *
          ((N : ℝ) / Real.log N ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcoef hXnonneg
    _ = ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by ring

/-- The final Chen theorem from the derived Jurkat--Richert weighted lower API
and the Liu--Pan--Wang--Ding aggregate theorem.  This broad intermediate
interface is retained for downstream compatibility. -/
theorem chens_theorem_of_jurkat_richert_weighted_lower_bound
    (hJR : ChenJurkatRichertWeightedLowerBound)
    (hLiu : LiuPanCanonicalCoprimeTheorem) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  chensTheorem_of_jurkatRichertWeightedLowerBound_and_triplePenalty
    hJR (liu_pan_wang_ding_strictTriple_upper hLiu)

/-- Backward wrapper from the stronger canonical source contract. -/
theorem chens_theorem_of_jurkat_richert_weighted_lower_bound_of_liuPanWangDing
    (hJR : ChenJurkatRichertWeightedLowerBound)
    (hLiu : LiuPanWangDingTheorem) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  chens_theorem_of_jurkat_richert_weighted_lower_bound
    hJR hLiu.to_canonicalCoprimeTheorem

/-- Source-faithful wrapper from literal Corollary `(2.30)`. -/
theorem chens_theorem_of_jurkat_richert_weighted_lower_bound_of_corollary230
    (hJR : ChenJurkatRichertWeightedLowerBound)
    (hLiu : LiuPanWangDingCorollary230) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  chens_theorem_of_jurkat_richert_weighted_lower_bound
    hJR hLiu.to_canonicalCoprimeTheorem

/-- The canonical internal Chen endpoint from the five remaining literature
interfaces: generic lower Rosser density, standard Bombieri--Vinogradov, upper
Rosser density, varying-`q` weighted Bombieri--Vinogradov, and
Liu--Pan--Wang--Ding. -/
theorem chens_theorem_of_literature_inputs
    (hLowerDensity :
      DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV : BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperDensity : DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBV : ChenJurkatRichertVaryingQWeightedBombieriVinogradov)
    (hLiu : LiuPanCanonicalCoprimeTheorem) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  chens_theorem_of_jurkat_richert_weighted_lower_bound
    (chenJurkatRichertWeightedLowerBound_of_literature_inputs
      hLowerDensity hBV hUpperDensity hWeightedBV)
    hLiu

/-- Backward wrapper for the former stronger Pan hypothesis. -/
theorem chens_theorem_of_literature_inputs_of_liuPanWangDing
    (hLowerDensity : DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV : BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperDensity : DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBV : ChenJurkatRichertVaryingQWeightedBombieriVinogradov)
    (hLiu : LiuPanWangDingTheorem) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  chens_theorem_of_literature_inputs hLowerDensity hBV hUpperDensity hWeightedBV
    hLiu.to_canonicalCoprimeTheorem

/-- Source-faithful literature endpoint from literal Corollary `(2.30)`. -/
theorem chens_theorem_of_literature_inputs_of_corollary230
    (hLowerDensity : DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV : BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperDensity : DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBV : ChenJurkatRichertVaryingQWeightedBombieriVinogradov)
    (hLiu : LiuPanWangDingCorollary230) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  chens_theorem_of_literature_inputs hLowerDensity hBV hUpperDensity hWeightedBV
    hLiu.to_canonicalCoprimeTheorem

/-- An inverse-log remainder is absorbed into an arbitrary positive multiple of
the truncated main scale.  The uniform lower bound `𝔖_trunc ≥ 1/2` is used
explicitly here. -/
theorem eventually_inverse_log_remainder_le_truncated
    (C ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
        ρ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) /
            Real.log N ^ (2 : ℕ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun N : ℕ => C / Real.log (N : ℝ)) atTop (nhds 0) :=
    hlog.const_div_atTop C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C / Real.log (N : ℝ) ≤ ρ / 2 :=
    hratio.eventually (Iic_mem_nhds (by linarith))
  filter_upwards [hsmall, eventually_ge_atTop 59049] with N hsmallN hN
  have hz : 2 ≤ correctedChenZ N - 1 :=
    correctedChenZ_sub_one_ge_two_of_large hN
  have hseries : (1 / 2 : ℝ) ≤
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) :=
    singularSeriesTruncated_ge_half hz
  have hcoef : C / Real.log (N : ℝ) ≤
      ρ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
        (correctedChenZ N - 1) := by
    calc
      C / Real.log (N : ℝ) ≤ ρ / 2 := hsmallN
      _ ≤ ρ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) := by nlinarith
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hXnonneg :
      0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
    positivity
  calc
    C * (N : ℝ) / Real.log N ^ (3 : ℕ) =
        (C / Real.log N) *
          ((N : ℝ) / Real.log N ^ (2 : ℕ)) := by
      field_simp [hlogpos.ne']
    _ ≤ (ρ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1)) *
            ((N : ℝ) / Real.log N ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcoef hXnonneg
    _ = ρ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) /
            Real.log N ^ (2 : ℕ) := by ring

/-- The canonical corrected-triple estimate in the analytic truncation units.
The Euler-tail margin `ηs` and inverse-log absorption margin `ηr` remain
separate in the coefficient. -/
theorem LiuPanWangDingTheorem.eventually_correctedChenOmegaTriple_le_truncated
    (hPan : LiuPanWangDingTheorem)
    (epsilon ηs ηr : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (correctedChenCandidates N).sum
          (fun p => tripleFactorCount
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        ((3.94033 / 2) * (1 + ηs) + ηr) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := by
  obtain ⟨C, _hC, htriple⟩ :=
    hPan.eventually_correctedChenOmegaTriple_le
      epsilon (3 : ℝ) hepsilon hepsilon_le (by norm_num)
  have htriple' : ∀ᶠ N : ℕ in atTop, Even N →
      (correctedChenCandidates N).sum
          (fun p => tripleFactorCount
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        3.94033 * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) +
          C * (N : ℝ) / Real.log N ^ (3 : ℕ) := by
    filter_upwards [htriple] with N hN
    intro hEven
    convert hN hEven using 1
    norm_num [Real.rpow_natCast]
  have hseries :=
    eventually_two_mul_liuSingularSeries_le_truncated ηs hηs
  have hrem :=
    eventually_inverse_log_remainder_le_truncated C ηr hηr
  filter_upwards
      [htriple', hseries, hrem, eventually_ge_atTop 2] with
      N htripleN hseriesN hremN hN
  intro hEven
  let S := AnalyticNumberTheory.Sieve.singularSeriesTruncated N
    (correctedChenZ N - 1)
  let X := (N : ℝ) / Real.log N ^ (2 : ℕ)
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity
  have hseriesN' :
      2 * SingularSeries.liuSingularSeries N ≤ (1 + ηs) * S := by
    simpa [S] using hseriesN hEven
  have hmainCoef :
      3.94033 * SingularSeries.liuSingularSeries N ≤
        (3.94033 / 2) * (1 + ηs) * S := by
    have h := mul_le_mul_of_nonneg_left hseriesN'
      (show (0 : ℝ) ≤ 3.94033 / 2 by norm_num)
    nlinarith
  have hmain :
      3.94033 * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) ≤
        ((3.94033 / 2) * (1 + ηs) * S) * X := by
    calc
      3.94033 * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) =
          (3.94033 * SingularSeries.liuSingularSeries N) * X := by
        dsimp [X]
        ring
      _ ≤ ((3.94033 / 2) * (1 + ηs) * S) * X :=
        mul_le_mul_of_nonneg_right hmainCoef hX
  have hremN' :
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤ ηr * S * X := by
    calc
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
          ηr * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := hremN
      _ = ηr * S * X := by
        dsimp [S, X]
        ring
  calc
    (correctedChenCandidates N).sum
          (fun p => tripleFactorCount
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        3.94033 * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) +
          C * (N : ℝ) / Real.log N ^ (3 : ℕ) :=
      htripleN hEven
    _ ≤ ((3.94033 / 2) * (1 + ηs) * S) * X + ηr * S * X :=
      add_le_add hmain hremN'
    _ = ((3.94033 / 2) * (1 + ηs) + ηr) * S * X := by
      ring
    _ = ((3.94033 / 2) * (1 + ηs) + ηr) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := by
      dsimp [S, X]
      ring

/-- The existing q1/proper-power reduction with its two contributions kept
visible: `Cq` from q1 and `1/2` from proper prime powers. -/
theorem eventually_correctedChenPrimePowerSum_le_of_q1
    (Cq : ℝ)
    (hq1 : ∀ᶠ N : ℕ in atTop, Even N →
      correctedChenQ1Count N ≤
        Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) /
            Real.log N ^ (2 : ℕ)) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (correctedChenCandidates N).sum
          (fun p => primePowerSum
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        (Cq + 1 / 2) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := by
  obtain ⟨Nn, hproper⟩ := properPower_negligible_threshold
  filter_upwards
      [hq1, eventually_ge_atTop Nn,
        eventually_ge_atTop (2 ^ 110 + 1)] with
      N hq1N hNn hNbig
  intro hEven
  have hred :=
    correctedChenPrimePowerSum_le_q1Count_add_negligible N
      (by omega) hEven
  let S := AnalyticNumberTheory.Sieve.singularSeriesTruncated N
    (correctedChenZ N - 1)
  let X := (N : ℝ) / Real.log N ^ (2 : ℕ)
  have hq1N' : correctedChenQ1Count N ≤ Cq * S * X := by
    convert hq1N hEven using 1
    dsimp [S, X]
    ring
  have hproperN :
      60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤ (1 / 2 : ℝ) * S * X := by
    convert hproper N hNn hEven using 1
    dsimp [S, X]
    ring
  calc
    (correctedChenCandidates N).sum
          (fun p => primePowerSum
            (N - p) (correctedChenZ N) (correctedChenY N)) ≤
        correctedChenQ1Count N +
          60 * (N : ℝ) ^ (9 / 10 : ℝ) := hred
    _ ≤ Cq * S * X + (1 / 2 : ℝ) * S * X :=
      add_le_add hq1N' hproperN
    _ = (Cq + 1 / 2) * S * X := by ring
    _ = (Cq + 1 / 2) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := by
      dsimp [S, X]
      ring

/-- Diagnostic corrected-penalty assembly.  Besides the Pan--Wang--Ding
contract, the only analytic input is the q¹ bound.  The fixed Pan level cannot
meet the displayed final numerical inequality, even with optimal weights, so
this theorem records the obstruction rather than a canonical final route. -/
theorem CorrectedChenOmegaUpperBound_of_liuPanWangDing_q1
    (hPan : LiuPanWangDingTheorem)
    (epsilon ηs ηr Cq : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr)
    (hq1 : ∀ᶠ N : ℕ in atTop, Even N →
      correctedChenQ1Count N ≤
        Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) /
            Real.log N ^ (2 : ℕ))
    (hnum : (10 / 3 : ℝ) >
      (((3.94033 / 2) * (1 + ηs) + ηr) + (Cq + 1 / 2)) / 2) :
    CorrectedChenOmegaUpperBound := by
  have htriple :=
    hPan.eventually_correctedChenOmegaTriple_le_truncated
      epsilon ηs ηr hepsilon hepsilon_le hηs hηr
  have hpower :=
    eventually_correctedChenPrimePowerSum_le_of_q1 Cq hq1
  have hOmega : ∀ᶠ N : ℕ in atTop, Even N →
      correctedChenOmega N ≤
        (((3.94033 / 2) * (1 + ηs) + ηr) + (Cq + 1 / 2)) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := by
    filter_upwards [htriple, hpower] with N htripleN hpowerN
    intro hEven
    let S := AnalyticNumberTheory.Sieve.singularSeriesTruncated N
      (correctedChenZ N - 1)
    let X := (N : ℝ) / Real.log N ^ (2 : ℕ)
    have htripleN' :
        (correctedChenCandidates N).sum
            (fun p => tripleFactorCount
              (N - p) (correctedChenZ N) (correctedChenY N)) ≤
          ((3.94033 / 2) * (1 + ηs) + ηr) * S * X := by
      convert htripleN hEven using 1
      dsimp [S, X]
      ring
    have hpowerN' :
        (correctedChenCandidates N).sum
            (fun p => primePowerSum
              (N - p) (correctedChenZ N) (correctedChenY N)) ≤
          (Cq + 1 / 2) * S * X := by
      convert hpowerN hEven using 1
      dsimp [S, X]
      ring
    calc
      correctedChenOmega N =
          (correctedChenCandidates N).sum
              (fun p => primePowerSum
                (N - p) (correctedChenZ N) (correctedChenY N)) +
            (correctedChenCandidates N).sum
              (fun p => tripleFactorCount
                (N - p) (correctedChenZ N) (correctedChenY N)) :=
        correctedChenOmega_eq_primePower_add_triple N
      _ ≤ (Cq + 1 / 2) * S * X +
          ((3.94033 / 2) * (1 + ηs) + ηr) * S * X :=
        add_le_add hpowerN' htripleN'
      _ = (((3.94033 / 2) * (1 + ηs) + ηr) + (Cq + 1 / 2)) *
          S * X := by ring
      _ = (((3.94033 / 2) * (1 + ηs) + ηr) + (Cq + 1 / 2)) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (correctedChenZ N - 1) * (N : ℝ) /
              Real.log N ^ (2 : ℕ) := by
        dsimp [S, X]
        ring
  rcases Filter.eventually_atTop.mp hOmega with ⟨N₀, hN₀⟩
  exact ⟨((3.94033 / 2) * (1 + ηs) + ηr) + (Cq + 1 / 2),
    hnum, N₀, hN₀⟩

/-- Diagnostic Liu--Pan--Wang--Ding Omega assembly with the q¹ bound supplied
by the direct weighted aggregate theorem.  Its fixed-level coefficient is
larger than the available final budget. -/
theorem CorrectedChenOmegaUpperBound_of_liuPanWangDing_q1WeightedAggregate
    (hLiu : LiuPanWangDingTheorem)
    (hQ1 : Q1WeightedAggregateTheorem)
    (epsilon ηs ηr : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr)
    (hnum : (10 / 3 : ℝ) >
      (((3.94033 / 2) * (1 + ηs) + ηr) +
        (q1WeightedAggregateConstant hQ1 + 1 / 2)) / 2) :
    CorrectedChenOmegaUpperBound := by
  rcases q1WeightedAggregateConstant_spec hQ1 with ⟨hCq, Nq, hq1⟩
  let Cq := q1WeightedAggregateConstant hQ1
  have hq1Eventually : ∀ᶠ N : ℕ in atTop, Even N →
      correctedChenQ1Count N ≤
        Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) /
            Real.log N ^ (2 : ℕ) :=
    Filter.eventually_atTop.mpr ⟨Nq, fun N hN => hq1 N hN⟩
  exact CorrectedChenOmegaUpperBound_of_liuPanWangDing_q1
    hLiu epsilon ηs ηr Cq hepsilon hepsilon_le hηs hηr hq1Eventually
      (by simpa [Cq] using hnum)

/-- Diagnostic corrected-Chen endpoint whose q¹ input is exactly the weighted
aggregate theorem consumed by the finite q¹ reduction.  The numerical
hypothesis is incompatible with the fixed Pan level. -/
theorem corrected_chens_theorem_of_liuPanWangDing_q1WeightedAggregate
    (hW : ChenWeightedPanInput)
    (hLiu : LiuPanWangDingTheorem)
    (hQ1 : Q1WeightedAggregateTheorem)
    (epsilon ηs ηr : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr)
    (hnum : (10 / 3 : ℝ) >
      (((3.94033 / 2) * (1 + ηs) + ηr) +
        (q1WeightedAggregateConstant hQ1 + 1 / 2)) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  exact corrected_chens_theorem_of_inputs hW
    (CorrectedChenOmegaUpperBound_of_liuPanWangDing_q1WeightedAggregate
      hLiu hQ1 epsilon ηs ηr
      hepsilon hepsilon_le hηs hηr hnum)

/-- Source-faithful W-side specialization of the diagnostic weighted-aggregate
q¹ endpoint. -/
theorem corrected_chens_theorem_of_liuPanWangDing_sourceFaithful_q1WeightedAggregate
    {u v : ℕ}
    (hI : AnalyticNumberTheory.Sieve.PanTypeICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u)
    (hII : AnalyticNumberTheory.Sieve.PanTypeIICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (hM : AnalyticNumberTheory.Sieve.PanSourceFaithfulSignedMainBound
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (hWTrunc : CorrectedChenPanTruncationInput)
    (hLiu : LiuPanWangDingTheorem)
    (hQ1 : Q1WeightedAggregateTheorem)
    (epsilon ηs ηr : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr)
    (hnum : (10 / 3 : ℝ) >
      (((3.94033 / 2) * (1 + ηs) + ηr) +
        (q1WeightedAggregateConstant hQ1 + 1 / 2)) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  have hW : ChenWeightedPanInput :=
    chenPanInput_of_sourceFaithfulSignedInputs hI hII hM hWTrunc
  exact corrected_chens_theorem_of_liuPanWangDing_q1WeightedAggregate
    hW hLiu hQ1 epsilon ηs ηr
      hepsilon hepsilon_le hηs hηr hnum

/-- Diagnostic Liu--Pan--Wang--Ding Omega assembly from the stronger
cutoff-free full-divisor-lane delta-one predicates. -/
theorem CorrectedChenOmegaUpperBound_of_liuPanWangDing_deltaOnePan
    (hLiu : LiuPanWangDingTheorem)
    (hQ1Pan : Q1DeltaOnePanMeanValue)
    (hQ1Trunc : Q1DeltaOnePanTruncationInput)
    (epsilon ηs ηr : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr)
    (hnum : (10 / 3 : ℝ) >
      (((3.94033 / 2) * (1 + ηs) + ηr) +
        (q1DeltaOnePanConstant hQ1Pan hQ1Trunc + 1 / 2)) / 2) :
    CorrectedChenOmegaUpperBound := by
  rcases q1DeltaOnePanConstant_spec hQ1Pan hQ1Trunc with
    ⟨hCq, Nq, hq1⟩
  let Cq := q1DeltaOnePanConstant hQ1Pan hQ1Trunc
  have hq1Eventually : ∀ᶠ N : ℕ in atTop, Even N →
      correctedChenQ1Count N ≤
        Cq * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (correctedChenZ N - 1) * (N : ℝ) /
            Real.log N ^ (2 : ℕ) :=
    Filter.eventually_atTop.mpr ⟨Nq, fun N hN => hq1 N hN⟩
  exact CorrectedChenOmegaUpperBound_of_liuPanWangDing_q1
    hLiu epsilon ηs ηr Cq hepsilon hepsilon_le hηs hηr hq1Eventually
      (by simpa [Cq] using hnum)

/-- Diagnostic corrected-Chen endpoint retaining the stronger full-lane
delta-one assumptions for audit compatibility. -/
theorem corrected_chens_theorem_of_liuPanWangDing_deltaOnePan
    (hW : ChenWeightedPanInput)
    (hLiu : LiuPanWangDingTheorem)
    (hQ1Pan : Q1DeltaOnePanMeanValue)
    (hQ1Trunc : Q1DeltaOnePanTruncationInput)
    (epsilon ηs ηr : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr)
    (hnum : (10 / 3 : ℝ) >
      (((3.94033 / 2) * (1 + ηs) + ηr) +
        (q1DeltaOnePanConstant hQ1Pan hQ1Trunc + 1 / 2)) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  exact corrected_chens_theorem_of_inputs hW
    (CorrectedChenOmegaUpperBound_of_liuPanWangDing_deltaOnePan
      hLiu hQ1Pan hQ1Trunc epsilon ηs ηr
      hepsilon hepsilon_le hηs hηr hnum)

/-- Source-faithful W-side specialization of the diagnostic full-lane q¹
endpoint. -/
theorem corrected_chens_theorem_of_liuPanWangDing_sourceFaithful_deltaOnePan
    {u v : ℕ}
    (hI : AnalyticNumberTheory.Sieve.PanTypeICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u)
    (hII : AnalyticNumberTheory.Sieve.PanTypeIICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (hM : AnalyticNumberTheory.Sieve.PanSourceFaithfulSignedMainBound
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (hWTrunc : CorrectedChenPanTruncationInput)
    (hLiu : LiuPanWangDingTheorem)
    (hQ1Pan : Q1DeltaOnePanMeanValue)
    (hQ1Trunc : Q1DeltaOnePanTruncationInput)
    (epsilon ηs ηr : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0)
    (hηs : 0 < ηs) (hηr : 0 < ηr)
    (hnum : (10 / 3 : ℝ) >
      (((3.94033 / 2) * (1 + ηs) + ηr) +
        (q1DeltaOnePanConstant hQ1Pan hQ1Trunc + 1 / 2)) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  have hW : ChenWeightedPanInput :=
    chenPanInput_of_sourceFaithfulSignedInputs hI hII hM hWTrunc
  exact corrected_chens_theorem_of_liuPanWangDing_deltaOnePan
    hW hLiu hQ1Pan hQ1Trunc epsilon ηs ηr
      hepsilon hepsilon_le hηs hηr hnum

end MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.ChensTheorem

/-- Public Chen theorem from the derived Jurkat--Richert weighted lower API.
This broad intermediate interface is retained for downstream compatibility. -/
theorem chens_theorem_of_jurkat_richert_weighted_lower_bound
    (hJR :
      SieveTheory.SwitchingPrinciple.ChenJurkatRichertWeightedLowerBound)
    (hLiu : SieveTheory.LiuWeight.LiuPanCanonicalCoprimeTheorem) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q := by
  obtain ⟨N₀, hchen⟩ :=
    SieveTheory.LiuWeight.chens_theorem_of_jurkat_richert_weighted_lower_bound
      hJR hLiu
  refine ⟨N₀, ?_⟩
  intro n hn_large hn_even
  obtain ⟨p, q, hp, hq_two, hq_almost, hn⟩ :=
    hchen n hn_large hn_even
  exact ⟨p, q, hp, ⟨hq_two, hq_almost⟩, hn⟩

/-- Backward public wrapper from the stronger canonical source contract. -/
theorem chens_theorem_of_jurkat_richert_weighted_lower_bound_of_liuPanWangDing
    (hJR :
      SieveTheory.SwitchingPrinciple.ChenJurkatRichertWeightedLowerBound)
    (hLiu : SieveTheory.LiuWeight.LiuPanWangDingTheorem) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q :=
  chens_theorem_of_jurkat_richert_weighted_lower_bound
    hJR hLiu.to_canonicalCoprimeTheorem

/-- Public source-faithful wrapper from literal Corollary `(2.30)`. -/
theorem chens_theorem_of_jurkat_richert_weighted_lower_bound_of_corollary230
    (hJR :
      SieveTheory.SwitchingPrinciple.ChenJurkatRichertWeightedLowerBound)
    (hLiu : SieveTheory.LiuWeight.LiuPanWangDingCorollary230) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q :=
  chens_theorem_of_jurkat_richert_weighted_lower_bound
    hJR hLiu.to_canonicalCoprimeTheorem

/-- Canonical public form of Chen's theorem, conditional exactly on the generic
dimension-one lower Rosser density fundamental lemma, standard
Bombieri--Vinogradov, the upper Rosser density fundamental lemma, varying-`q`
weighted Bombieri--Vinogradov, and the Liu--Pan--Wang--Ding theorem. -/
theorem chens_theorem_of_literature_inputs
    (hLowerDensity :
      SieveTheory.SwitchingPrinciple.DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV :
      SieveTheory.BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperDensity :
      SieveTheory.SwitchingPrinciple.DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBV :
      SieveTheory.SwitchingPrinciple.ChenJurkatRichertVaryingQWeightedBombieriVinogradov)
    (hLiu : SieveTheory.LiuWeight.LiuPanCanonicalCoprimeTheorem) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q :=
  chens_theorem_of_jurkat_richert_weighted_lower_bound
    (SieveTheory.SwitchingPrinciple.chenJurkatRichertWeightedLowerBound_of_literature_inputs
        hLowerDensity hBV hUpperDensity hWeightedBV)
    hLiu

/-- Backward public endpoint from the stronger canonical source contract. -/
theorem chens_theorem_of_literature_inputs_of_liuPanWangDing
    (hLowerDensity :
      SieveTheory.SwitchingPrinciple.DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV : SieveTheory.BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperDensity :
      SieveTheory.SwitchingPrinciple.DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBV :
      SieveTheory.SwitchingPrinciple.ChenJurkatRichertVaryingQWeightedBombieriVinogradov)
    (hLiu : SieveTheory.LiuWeight.LiuPanWangDingTheorem) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q :=
  chens_theorem_of_literature_inputs hLowerDensity hBV hUpperDensity hWeightedBV
    hLiu.to_canonicalCoprimeTheorem

/-- Public source-faithful endpoint from literal Corollary `(2.30)`. -/
theorem chens_theorem_of_literature_inputs_of_corollary230
    (hLowerDensity :
      SieveTheory.SwitchingPrinciple.DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV : SieveTheory.BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperDensity :
      SieveTheory.SwitchingPrinciple.DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBV :
      SieveTheory.SwitchingPrinciple.ChenJurkatRichertVaryingQWeightedBombieriVinogradov)
    (hLiu : SieveTheory.LiuWeight.LiuPanWangDingCorollary230) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q :=
  chens_theorem_of_literature_inputs hLowerDensity hBV hUpperDensity hWeightedBV
    hLiu.to_canonicalCoprimeTheorem

end MathlibNt.ChensTheorem
