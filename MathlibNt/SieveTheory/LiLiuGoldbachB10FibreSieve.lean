import MathlibNt.SieveTheory.LiLiuGoldbachB10Congruence
import MathlibNt.SieveTheory.LinearSieve
import Mathlib.Data.Nat.Cast.Order.Field

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB10FibreSieve (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The literal output value attached to a labelled `B10` atom. -/
abbrev goldbachB10Output (N : ℕ) : (Σ _rs : ℕ × ℕ, ℕ) → ℕ :=
  goldbachPi10Output N

/-- The finite support of the genuine `B10` pushforward sieve. -/
noncomputable def goldbachB10Support (N : ℕ) (ε b c : ℝ) : Finset ℕ :=
  (goldbachB10Atoms N ε b c).image (goldbachB10Output N)

/-- The multiplicity weight of an output value `p = N - rsq`. Repeated outputs
from different labelled atoms are accumulated rather than collapsed. -/
noncomputable def goldbachB10Weight (N : ℕ) (ε b c : ℝ) (p : ℕ) : ℝ :=
  (((goldbachB10Atoms N ε b c).filter fun x => goldbachB10Output N x = p).card : ℝ)

/-- The exact finite prime carrier for the literal strict sieve cutoff `p < Z`
with the exceptional primes dividing `N` removed. -/
noncomputable def goldbachB10SiftingPrimes (N : ℕ) (Z : ℝ) : Finset ℕ :=
  (range (Nat.ceil Z)).filter fun p => p.Prime ∧ ¬ p ∣ N

/-- The corresponding finite product of the actual sieved primes. -/
noncomputable def goldbachB10ProdPrimes (N : ℕ) (Z : ℝ) : ℕ :=
  (goldbachB10SiftingPrimes N Z).prod id

theorem mem_goldbachB10SiftingPrimes_iff
    {N : ℕ} {Z : ℝ} {p : ℕ} :
    p ∈ goldbachB10SiftingPrimes N Z ↔ p < Nat.ceil Z ∧ p.Prime ∧ ¬ p ∣ N := by
  simp [goldbachB10SiftingPrimes]

theorem goldbachB10ProdPrimes_squarefree (N : ℕ) (Z : ℝ) :
    Squarefree (goldbachB10ProdPrimes N Z) := by
  unfold goldbachB10ProdPrimes goldbachB10SiftingPrimes
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2.1
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hpPrime hqPrime).mpr hpq)
  · intro p hp
    exact ((Finset.mem_filter.mp hp).2.1).squarefree

theorem goldbachB10ProdPrimes_ne_zero (N : ℕ) (Z : ℝ) :
    goldbachB10ProdPrimes N Z ≠ 0 := by
  unfold goldbachB10ProdPrimes goldbachB10SiftingPrimes
  exact ne_of_gt <| Finset.prod_pos fun p hp => by
    exact (mem_goldbachB10SiftingPrimes_iff.mp hp).2.1.pos

private theorem B10FibreSieve_primeFactors_prod_eq_self {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) : (S.prod id).primeFactors = S := by
  exact Nat.primeFactors_prod hS

theorem goldbachB10ProdPrimes_primeFactors (N : ℕ) (Z : ℝ) :
    (goldbachB10ProdPrimes N Z).primeFactors = goldbachB10SiftingPrimes N Z := by
  unfold goldbachB10ProdPrimes
  exact B10FibreSieve_primeFactors_prod_eq_self
    (fun p hp => (mem_goldbachB10SiftingPrimes_iff.mp hp).2.1)

theorem prime_dvd_goldbachB10ProdPrimes_iff
    {N : ℕ} {Z : ℝ} {p : ℕ} (hp : p.Prime) :
    p ∣ goldbachB10ProdPrimes N Z ↔ (p : ℝ) < Z ∧ ¬ p ∣ N := by
  constructor
  · intro hpP
    have hmem : p ∈ (goldbachB10ProdPrimes N Z).primeFactors := by
      exact (Nat.mem_primeFactors_of_ne_zero
        (goldbachB10ProdPrimes_ne_zero N Z)).mpr ⟨hp, hpP⟩
    rw [goldbachB10ProdPrimes_primeFactors] at hmem
    rcases mem_goldbachB10SiftingPrimes_iff.mp hmem with ⟨hpZ, _, hpN⟩
    exact ⟨Nat.lt_ceil.mp hpZ, hpN⟩
  · rintro ⟨hpZ, hpN⟩
    have hmem : p ∈ goldbachB10SiftingPrimes N Z := by
      exact mem_goldbachB10SiftingPrimes_iff.mpr ⟨Nat.lt_ceil.mpr hpZ, hp, hpN⟩
    exact Finset.dvd_prod_of_mem id hmem

theorem goldbachB10ProdPrimes_coprime_N (N : ℕ) (Z : ℝ) :
    Nat.Coprime (goldbachB10ProdPrimes N Z) N := by
  apply Nat.coprime_of_dvd'
  intro p hpPrime hpP hpN
  exact False.elim <| ((prime_dvd_goldbachB10ProdPrimes_iff hpPrime).mp hpP).2 hpN

theorem goldbachB10_dvd_prodPrimes_coprime_N
    {N d : ℕ} {Z : ℝ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    Nat.Coprime d N :=
  (goldbachB10ProdPrimes_coprime_N N Z).coprime_dvd_left hd

theorem prime_dvd_goldbachB10ProdPrimes_lt
    {N : ℕ} {Z : ℝ} {p : ℕ} (hp : p.Prime) (hpP : p ∣ goldbachB10ProdPrimes N Z) :
    (p : ℝ) < Z :=
  (prime_dvd_goldbachB10ProdPrimes_iff hp).mp hpP |>.1

private theorem B10FibreSieve_pushforward_sum_eq_card_filter
    {α : Type*} [DecidableEq α]
    (A : Finset α) (out : α → ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ n ∈ (A.image out).filter P, (((A.filter fun x => out x = n).card : ℕ) : ℝ) =
      (((A.filter fun x => P (out x)).card : ℕ) : ℝ) := by
  let U : Finset ℕ := (A.image out).filter P
  have hfiberwise :=
    Finset.sum_fiberwise_eq_sum_filter A U out (fun _ => (1 : ℝ))
  have hfilter :
      A.filter (fun x => out x ∈ U) = A.filter (fun x => P (out x)) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxA, hxU⟩
      exact Finset.mem_filter.mpr
        ⟨hxA, (Finset.mem_filter.mp hxU).2⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxA, hxP⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨hxA, Finset.mem_filter.mpr ?_⟩
      exact ⟨Finset.mem_image.mpr ⟨x, hxA, rfl⟩, hxP⟩
  rw [hfilter] at hfiberwise
  have hsum :
      ∑ n ∈ U, ∑ x ∈ A.filter (fun x => out x = n), (1 : ℝ) =
        (((A.filter fun x => P (out x)).card : ℕ) : ℝ) := by
    simpa [U] using hfiberwise
  calc
    ∑ n ∈ (A.image out).filter P, (((A.filter fun x => out x = n).card : ℕ) : ℝ)
        = ∑ n ∈ U, ∑ x ∈ A.filter (fun x => out x = n), (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp
    _ = (((A.filter fun x => P (out x)).card : ℕ) : ℝ) := hsum

theorem goldbachB10_coprime_prodPrimes_iff_literalHPoint
    (N : ℕ) (Z : ℝ) (n : ℕ) :
    Nat.Coprime (goldbachB10ProdPrimes N Z) n ↔ literalHPoint N 1 Z n := by
  rw [literalHPoint_one_iff_survivesSieve]
  constructor
  · intro hcopr p hpPrime hpn hpN
    refine le_of_not_gt ?_
    intro hpZ
    have hpP : p ∣ goldbachB10ProdPrimes N Z :=
      (prime_dvd_goldbachB10ProdPrimes_iff hpPrime).mpr ⟨hpZ, hpN⟩
    exact (prime_not_dvd_of_coprime hcopr.symm hpPrime hpn) hpP
  · intro hsieve
    apply Nat.coprime_of_dvd'
    intro p hpPrime hpP hpn
    have hpData := (prime_dvd_goldbachB10ProdPrimes_iff hpPrime).mp hpP
    exact False.elim <| (not_le_of_gt hpData.1) (hsieve p hpPrime hpn hpData.2)

/-- The actual finite pushforward sieve on labelled `B10` atoms. The total mass
is the supplied parameter `X`; no analytic identification is built into this
finite adapter. -/
noncomputable def goldbachB10BoundingSieve
    (N : ℕ) (hEven : Even N) (ε b c Z X : ℝ) : BoundingSieve where
  support := goldbachB10Support N ε b c
  weights := goldbachB10Weight N ε b c
  weights_nonneg := by
    intro p
    unfold goldbachB10Weight
    positivity
  prodPrimes := goldbachB10ProdPrimes N Z
  prodPrimes_squarefree := goldbachB10ProdPrimes_squarefree N Z
  totalMass := X
  nu := AnalyticNumberTheory.Sieve.goldbachNu
  nu_mult := AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hpP
    exact AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hpP
    have hpN : ¬ p ∣ N := (prime_dvd_goldbachB10ProdPrimes_iff hp).mp hpP |>.2
    have hp2 : 2 < p := by
      have hpne : p ≠ 2 := by
        intro hpEq
        apply hpN
        rw [hpEq]
        exact even_iff_two_dvd.mp hEven
      exact lt_of_le_of_ne hp.two_le (by simpa using hpne.symm)
    exact AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hp hp2

theorem goldbachB10BoundingSieve_multSum_eq_card_divisorAtoms
    (N : ℕ) (hEven : Even N) (ε b c Z X : ℝ) (d : ℕ) :
    (goldbachB10BoundingSieve N hEven ε b c Z X).multSum d =
      ((goldbachB10DivisorAtoms N d ε b c).card : ℝ) := by
  let A := goldbachB10Atoms N ε b c
  let out := goldbachB10Output N
  calc
    (goldbachB10BoundingSieve N hEven ε b c Z X).multSum d
        = ∑ n ∈ (A.image out).filter (fun n => d ∣ n),
            (((A.filter fun x => out x = n).card : ℕ) : ℝ) := by
              simp [goldbachB10BoundingSieve, goldbachB10Support, goldbachB10Weight,
                BoundingSieve.multSum, A, out, Finset.sum_filter]
    _ = (((A.filter fun x => d ∣ out x).card : ℕ) : ℝ) := by
          simpa [A, out] using
            B10FibreSieve_pushforward_sum_eq_card_filter
              A out (fun n => d ∣ n)
    _ = ((goldbachB10DivisorAtoms N d ε b c).card : ℝ) := by
          rw [show A.filter (fun x => d ∣ out x) = goldbachB10DivisorAtoms N d ε b c by
            ext x
            simp [A, out, goldbachB10DivisorAtoms]]

private theorem B10FibreSieve_siftedAtoms_eq_filter
    (N : ℕ) (ε b c Z : ℝ) :
    (goldbachB10Atoms N ε b c).filter
        (fun x => literalHPoint N 1 Z (goldbachB10Output N x)) =
      goldbachB10SiftedAtoms N ε b c Z := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxA, hxSift⟩
    rcases mem_goldbachB10Atoms_iff.mp hxA with ⟨hrs, hqRange, hpoint⟩
    exact mem_goldbachB10SiftedAtoms_iff.mpr ⟨hrs, hqRange, hpoint, hxSift⟩
  · intro hx
    rcases mem_goldbachB10SiftedAtoms_iff.mp hx with ⟨hrs, hqRange, hpoint, hxSift⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachB10Atoms_iff.mpr ⟨hrs, hqRange, hpoint⟩, hxSift⟩

theorem goldbachB10BoundingSieve_siftedSum_eq
    (N : ℕ) (hEven : Even N) (ε b c Z X : ℝ) :
    (goldbachB10BoundingSieve N hEven ε b c Z X).siftedSum =
      (goldbachB10SiftedCount N ε b c Z : ℝ) := by
  let A := goldbachB10Atoms N ε b c
  let out := goldbachB10Output N
  let P := goldbachB10ProdPrimes N Z
  calc
    (goldbachB10BoundingSieve N hEven ε b c Z X).siftedSum
        = ∑ n ∈ (A.image out).filter (fun n => Nat.Coprime P n),
            (((A.filter fun x => out x = n).card : ℕ) : ℝ) := by
              rw [goldbachB10BoundingSieve, BoundingSieve.siftedSum, ← Finset.sum_filter]
              rfl
    _ = (((A.filter fun x => Nat.Coprime P (out x)).card : ℕ) : ℝ) := by
          simpa [A, out, P] using
            B10FibreSieve_pushforward_sum_eq_card_filter
              A out (fun n => Nat.Coprime P n)
    _ = (((A.filter fun x => literalHPoint N 1 Z (out x)).card : ℕ) : ℝ) := by
          rw [show A.filter (fun x => Nat.Coprime P (out x)) =
            A.filter (fun x => literalHPoint N 1 Z (out x)) by
              ext x
              simp [P, out, goldbachB10_coprime_prodPrimes_iff_literalHPoint]]
    _ = ((goldbachB10SiftedAtoms N ε b c Z).card : ℝ) := by
          rw [B10FibreSieve_siftedAtoms_eq_filter]
    _ = (goldbachB10SiftedCount N ε b c Z : ℝ) := by
          rw [goldbachB10SiftedCount_eq_card_atoms]
          norm_num

theorem goldbachB10BoundingSieve_nu_eq_inv_totient
    {N : ℕ} (hEven : Even N) {ε b c Z X : ℝ} {d : ℕ}
    (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachB10BoundingSieve N hEven ε b c Z X).nu d =
      (1 : ℝ) / Nat.totient d := by
  have hd' : d ∣ (goldbachB10BoundingSieve N hEven ε b c Z X).prodPrimes := by
    simpa [goldbachB10BoundingSieve] using hd
  exact AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient
    (BoundingSieve.squarefree_of_dvd_prodPrimes
      (s := goldbachB10BoundingSieve N hEven ε b c Z X) hd')

theorem goldbachB10BoundingSieve_rem_eq_card_sub
    {N : ℕ} (hEven : Even N) {ε b c Z X : ℝ} {d : ℕ}
    (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachB10BoundingSieve N hEven ε b c Z X).rem d =
      ((goldbachB10DivisorAtoms N d ε b c).card : ℝ) - X / Nat.totient d := by
  unfold BoundingSieve.rem
  rw [goldbachB10BoundingSieve_multSum_eq_card_divisorAtoms,
    goldbachB10BoundingSieve_nu_eq_inv_totient (hEven := hEven) (ε := ε)
      (b := b) (c := c) (Z := Z) (X := X) hd]
  simp [goldbachB10BoundingSieve, div_eq_mul_inv, mul_comm]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig