import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitActualFamily
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledCoprimeOutputSplit
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeRelative

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Exact original-sigma dictionary on prime outputs only. -/
theorem actualFamily_weightAt_prime {i N ell : ℕ} {δ : ℝ}
    (p : SecondFunctionalParameters) (W : Fin i → Finset ℕ) (high : Bool)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) (hell : ell.Prime) :
    (actualFamily N δ p W high hd).weightAt ell =
      ∑ x ∈ actualProfiles N δ p W high, (convolutionCoeff W x.1 : ℝ) *
        ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card := by
  have ht := actualFamily_test_dictionary (N := N) (δ := δ) p W high hd
    (fun x q => if N-cofactor x*q = ell then (convolutionCoeff W x.1 : ℝ) else 0)
  have hf (x : Profile) (hx : x ∈ actualProfiles N δ p W high) :
      (actualRawFibre N δ p x).filter (fun q => N-cofactor x*q = ell) =
        (actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell) := by
    rw [← (actualFamily_fibres p W high hd hx).2,
      (actualFamily_fibres p W high hd hx).1]
    ext q
    simp only [mem_filter]
    constructor
    · rintro ⟨hq, he⟩
      exact ⟨⟨hq, he ▸ hell⟩, he⟩
    · rintro ⟨⟨hq, _⟩, he⟩
      exact ⟨hq, he⟩
  change (∑ x ∈ (actualFamily N δ p W high hd).labels,
    (convolutionCoeff W x.1 : ℝ) *
      (((actualFamily N δ p W high hd).primes x).filter
        (fun q => N-cofactor x*q = ell)).card) = _
  simp only [← sum_filter, sum_const, nsmul_eq_mul] at ht
  simp only [show ∀ a b : ℝ, a*b=b*a from mul_comm] at ht
  rw [ht]
  exact sum_congr rfl (fun x hx => by rw [hf x hx])

/-- Source support supplies positivity internally; nonprime outputs are not identified. -/
theorem sourceFamily_weightAt_prime {i N ell : ℕ} {δ Δ : ℝ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) (hell : ell.Prime) :
    (sourceFamily N δ Δ V p high).weightAt ell =
      ∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high,
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card :=
  actualFamily_weightAt_prime p _ high _ hell

/-- The genuine internal multiplicity theorem bounds every prime output, uniformly. -/
theorem source_prime_weightAt_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      ∀ ell : ℕ, ell.Prime →
        (sourceFamily N δ Δ V p high).weightAt ell ≤
          (max 1 (1/(wuLocalExponent k δ / 10)))^(k+arity high+1) := by
  obtain ⟨T,hT,hm⟩ := source_multiplicities k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp high ell hell
  rw [sourceFamily_weightAt_prime V p high hell]
  exact (hm N hN i Δ V hb p hp high).2 ell

/-- Exceptional prime outputs are divisors of N; the full original weight is retained. -/
theorem source_bad_primeMass_log_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
        (sourceFamily N δ Δ V p high).noncoprimePart.primeMass ≤
          (max 1 (1/(wuLocalExponent k δ / 10)))^(k+arity high+1) * log N / log 2 := by
  obtain ⟨T,hT,hm⟩ := source_prime_weightAt_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp high
  apply LabelledPhysical.Family.noncoprimePart_primeMass_le_log
    (sourceFamily N δ Δ V p high) (by have := hT.trans hN; omega) (by positivity)
  intro ell hell
  exact hm N hN i Δ V hb p hp high ell (Nat.prime_of_mem_primeFactors hell)

/-- Both high words cost at most the explicit logarithmic exceptional term. -/
theorem source_bad_primeMass_pair_log_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        (sourceFamily N δ Δ V p false).noncoprimePart.primeMass +
        (sourceFamily N δ Δ V p true).noncoprimePart.primeMass ≤
          2 * (max 1 (1/(wuLocalExponent k δ / 10)))^(k+6) * log N / log 2 := by
  obtain ⟨T,hT,hm⟩ := source_bad_primeMass_log_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by have := hT.trans hN; omega))
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hone (high : Bool) :
      (sourceFamily N δ Δ V p high).noncoprimePart.primeMass ≤
        (max 1 (1/(wuLocalExponent k δ / 10)))^(k+6) * log N / log 2 := by
    apply (hm N hN i Δ V hb p hp high).trans
    apply div_le_div_of_nonneg_right _ hlog2.le
    apply mul_le_mul_of_nonneg_right _ hlog
    exact pow_le_pow_right₀ (le_max_left 1 _) (by cases high <;> simp [arity])
  calc
    _ ≤ _ := add_le_add (hone false) (hone true)
    _ = _ := by ring

/-- One epsilon pays the two bad PRIME masses, without any claim on bad raw mass. -/
theorem source_bad_primeMass_pair_theta_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        (sourceFamily N δ Δ V p false).noncoprimePart.primeMass +
        (sourceFamily N δ Δ V p true).noncoprimePart.primeMass ≤
          ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let C := 2 * (max 1 (1/(wuLocalExponent k δ / 10)))^(k+6) / log 2
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T1,hT1,hm⟩ := source_bad_primeMass_pair_log_uniform k hδ hδhi
  obtain ⟨T2,_,ha⟩ := omega3_absolute_power_log_relative k 1 hδ hδhi hε hC
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by have := hT1.trans hN1; omega)
  apply (hm N hN1 i Δ V hb p hp).trans
  have hpay := ha N hN2 i Δ V hb
  have hid : C * N * log N ^ 1 / (N : ℝ) ^ (1 : ℝ) =
      2 * (max 1 (1/(wuLocalExponent k δ / 10)))^(k+6) * log N / log 2 := by
    rw [rpow_one, pow_one]
    dsimp [C]
    field_simp
  rw [hid] at hpay
  exact hpay

/-- Exact prime-mass splitting and explicit exceptional payment; no raw-mass replacement. -/
theorem sourceFamily_pair_le_good_primeMass (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
        (sourceFamily N δ Δ V p false).primeMass +
        (sourceFamily N δ Δ V p true).primeMass ≤
          (sourceFamily N δ Δ V p false).coprimePart.primeMass +
          (sourceFamily N δ Δ V p true).coprimePart.primeMass +
          ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := source_bad_primeMass_pair_theta_relative k hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  have h := hm N hN i Δ V hb p hp
  rw [(sourceFamily N δ Δ V p false).primeMass_coprime_split,
    (sourceFamily N δ Δ V p true).primeMass_coprime_split]
  linarith

/-- The actual two nonunit sources reach the two good prime masses with one epsilon. -/
theorem mother_source_pair_le_good_primeMass (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → 4 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        actualSource N δ p (convolutionWuWindows N Δ V) false +
        actualSource N δ p (convolutionWuWindows N Δ V) true ≤
          (sourceFamily N δ Δ V p false).coprimePart.primeMass +
          (sourceFamily N δ Δ V p true).coprimePart.primeMass +
          ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := sourceFamily_pair_le_good_primeMass k hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN hN4 he i Δ V hb p hp hs
  exact (add_le_add (mother_source_le_family p hp hs hN4 he hδ hδhi hb false)
    (mother_source_le_family p hp hs hN4 he hδ hδhi hb true)).trans
      (hm N hN i Δ V hb p hp)

end Wu2008DoubleSieve.HighNonunit
