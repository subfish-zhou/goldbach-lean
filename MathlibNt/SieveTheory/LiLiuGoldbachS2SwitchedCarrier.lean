import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.ModEq
import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve
import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachS2PrimePairs
import MathlibNt.SieveTheory.LinearSieve

open scoped BigOperators

open Finset
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

noncomputable local instance instDecidableGoldbachS2SwitchedCarrier (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The literal relaxed switched labels `(r,q)` for the actual `S2` source. -/
noncomputable def goldbachS2SwitchedLabels (N : ℕ) (T : ℝ) : Finset (Sigma fun _r : ℕ => ℕ) :=
  (goldbachS2Primes N T).sigma fun r =>
    (range (N + 1)).filter fun q => q.Prime ∧ r * q < N

theorem mem_goldbachS2SwitchedLabels_iff
    {N : ℕ} {T : ℝ} {x : Sigma fun _r : ℕ => ℕ} :
    x ∈ goldbachS2SwitchedLabels N T ↔
      x.1 ∈ goldbachS2Primes N T ∧ x.2.Prime ∧ x.1 * x.2 < N := by
  constructor
  · intro hx
    rcases Finset.mem_sigma.mp hx with ⟨hr, hq⟩
    rcases Finset.mem_filter.mp hq with ⟨_, hqPrime, hlt⟩
    exact ⟨hr, hqPrime, hlt⟩
  · rintro ⟨hr, hqPrime, hlt⟩
    have hx2le : x.2 ≤ N := by
      rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, _, _⟩
      calc
        x.2 ≤ x.1 * x.2 := Nat.le_mul_of_pos_left _ hrPrime.pos
        _ ≤ N := hlt.le
    simp [goldbachS2SwitchedLabels, hr, hqPrime, hlt, Finset.mem_range.mpr (Nat.lt_succ_of_le hx2le)]

/-- The switched output is the literal partner `b(r,q)=N-rq`. -/
abbrev goldbachS2SwitchedOutput (N : ℕ) : (Sigma fun _r : ℕ => ℕ) → ℕ :=
  fun x => N - x.1 * x.2

theorem goldbachS2SwitchedOutput_eq_sub
    {N : ℕ} {x : Sigma fun _r : ℕ => ℕ} :
    goldbachS2SwitchedOutput N x = N - x.1 * x.2 := by
  rfl

theorem goldbachS2SwitchedAtom_prod_lt
    {N : ℕ} {T : ℝ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ goldbachS2SwitchedLabels N T) :
    x.1 * x.2 < N :=
  (mem_goldbachS2SwitchedLabels_iff.mp hx).2.2

theorem goldbachS2SwitchedAtom_prod_add_output
    {N : ℕ} {T : ℝ} {x : Sigma fun _r : ℕ => ℕ}
    (hx : x ∈ goldbachS2SwitchedLabels N T) :
    x.1 * x.2 + goldbachS2SwitchedOutput N x = N := by
  rw [goldbachS2SwitchedOutput_eq_sub]
  exact Nat.add_sub_of_le (goldbachS2SwitchedAtom_prod_lt hx).le

/-- On a genuine switched label, divisibility of the output is exactly the
congruence `rq ≡ N (mod d)`. -/
theorem goldbachS2SwitchedAtom_output_dvd_iff_modEq
    {N d : ℕ} {T : ℝ} {x : Sigma fun _r : ℕ => ℕ}
    (_hd : 1 ≤ d)
    (hx : x ∈ goldbachS2SwitchedLabels N T) :
    d ∣ goldbachS2SwitchedOutput N x ↔ Nat.ModEq d (x.1 * x.2) N := by
  have hle : x.1 * x.2 ≤ N := (goldbachS2SwitchedAtom_prod_lt hx).le
  rw [goldbachS2SwitchedOutput_eq_sub, Nat.modEq_iff_dvd' hle]

/-- Exact residue condition on a switched divisor fibre. -/
def goldbachS2SwitchedDivisorResidueCondition
    (N d : ℕ) (x : Sigma fun _r : ℕ => ℕ) : Prop :=
  Nat.Coprime x.1 d ∧ ((x.2 : ZMod d) = (N : ZMod d) * (x.1 : ZMod d)⁻¹)

theorem goldbachS2SwitchedAtom_left_coprime_of_coprime_modulus
    {N d : ℕ} {T : ℝ} {x : Sigma fun _r : ℕ => ℕ}
    (_hd : 1 ≤ d)
    (hx : x ∈ goldbachS2SwitchedLabels N T)
    (hdp : d ∣ goldbachS2SwitchedOutput N x) :
    Nat.Coprime x.1 d := by
  rcases mem_goldbachS2SwitchedLabels_iff.mp hx with ⟨hrMem, _, _⟩
  rcases Finset.mem_filter.mp hrMem with ⟨_, hrPrime, hrN, _, _⟩
  apply Nat.coprime_of_dvd'
  intro p hpPrime hpr hpd
  have hpp : p ∣ goldbachS2SwitchedOutput N x := dvd_trans hpd hdp
  have hpProd : p ∣ x.1 * x.2 := dvd_mul_of_dvd_left hpr x.2
  have hN' : p ∣ N := by
    simpa [goldbachS2SwitchedAtom_prod_add_output hx] using Nat.dvd_add hpProd hpp
  exact (prime_not_dvd_of_coprime hrN hpPrime hpr hN').elim

theorem goldbachS2SwitchedAtom_output_dvd_iff_residueCondition
    {N d : ℕ} {T : ℝ} {x : Sigma fun _r : ℕ => ℕ}
    (hd : 1 ≤ d)
    (hx : x ∈ goldbachS2SwitchedLabels N T) :
    d ∣ goldbachS2SwitchedOutput N x ↔ goldbachS2SwitchedDivisorResidueCondition N d x := by
  constructor
  · intro hdp
    have hcop :
        Nat.Coprime x.1 d :=
      goldbachS2SwitchedAtom_left_coprime_of_coprime_modulus hd hx hdp
    have hmod : Nat.ModEq d (x.1 * x.2) N :=
      (goldbachS2SwitchedAtom_output_dvd_iff_modEq hd hx).mp hdp
    have hzprod :
        (((x.1 * x.2 : ℕ) : ZMod d)) = (N : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff (x.1 * x.2) N d).2 hmod
    have hzmul :
        ((x.1 : ZMod d) * (x.2 : ZMod d)) = (N : ZMod d) := by
      simpa using hzprod
    refine ⟨hcop, ?_⟩
    calc
      (x.2 : ZMod d) = (1 : ZMod d) * (x.2 : ZMod d) := by simp
      _ = (((x.1 : ZMod d) * (x.1 : ZMod d)⁻¹) * (x.2 : ZMod d)) := by
            rw [← ZMod.coe_mul_inv_eq_one x.1 hcop]
      _ = (x.1 : ZMod d)⁻¹ * ((x.1 : ZMod d) * (x.2 : ZMod d)) := by
            ac_rfl
      _ = (x.1 : ZMod d)⁻¹ * (N : ZMod d) := by rw [hzmul]
      _ = (N : ZMod d) * (x.1 : ZMod d)⁻¹ := by simp [mul_comm]
  · rintro ⟨hcop, hqeq⟩
    have hzmul :
        ((x.1 : ZMod d) * (x.2 : ZMod d)) = (N : ZMod d) := by
      calc
        (x.1 : ZMod d) * (x.2 : ZMod d)
            = (x.1 : ZMod d) * ((N : ZMod d) * (x.1 : ZMod d)⁻¹) := by
                rw [hqeq]
        _ = (N : ZMod d) * ((x.1 : ZMod d) * (x.1 : ZMod d)⁻¹) := by
              ac_rfl
        _ = (N : ZMod d) * 1 := by
              rw [ZMod.coe_mul_inv_eq_one x.1 hcop]
        _ = (N : ZMod d) := by simp
    have hzprod :
        (((x.1 * x.2 : ℕ) : ZMod d)) = (N : ZMod d) := by
      simpa using hzmul
    have hmod : Nat.ModEq d (x.1 * x.2) N :=
      (ZMod.natCast_eq_natCast_iff (x.1 * x.2) N d).1 hzprod
    exact (goldbachS2SwitchedAtom_output_dvd_iff_modEq hd hx).mpr hmod

/-- The literal divisor fibre on the relaxed switched labels. -/
noncomputable def goldbachS2SwitchedDivisorLabels
    (N : ℕ) (T : ℝ) (d : ℕ) : Finset (Sigma fun _r : ℕ => ℕ) :=
  (goldbachS2SwitchedLabels N T).filter fun x => d ∣ goldbachS2SwitchedOutput N x

theorem mem_goldbachS2SwitchedDivisorLabels_iff
    {N d : ℕ} {T : ℝ} {x : Sigma fun _r : ℕ => ℕ} :
    x ∈ goldbachS2SwitchedDivisorLabels N T d ↔
      x ∈ goldbachS2SwitchedLabels N T ∧ d ∣ goldbachS2SwitchedOutput N x := by
  simp [goldbachS2SwitchedDivisorLabels]

theorem goldbachS2SwitchedDivisorLabels_eq_residueFilter
    {N d : ℕ} {T : ℝ}
    (hd : 1 ≤ d)
    :
    goldbachS2SwitchedDivisorLabels N T d =
      (goldbachS2SwitchedLabels N T).filter
        (goldbachS2SwitchedDivisorResidueCondition N d) := by
  ext x
  constructor
  · intro hx
    rcases mem_goldbachS2SwitchedDivisorLabels_iff.mp hx with ⟨hxS, hdiv⟩
    exact Finset.mem_filter.mpr
      ⟨hxS, (goldbachS2SwitchedAtom_output_dvd_iff_residueCondition hd hxS).mp hdiv⟩
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxS, hcond⟩
    exact mem_goldbachS2SwitchedDivisorLabels_iff.mpr
      ⟨hxS, (goldbachS2SwitchedAtom_output_dvd_iff_residueCondition hd hxS).mpr hcond⟩

/-- The relaxed switched support after pushforward along `b(r,q)=N-rq`. -/
noncomputable def goldbachS2SwitchedSupport (N : ℕ) (T : ℝ) : Finset ℕ :=
  (goldbachS2SwitchedLabels N T).image (goldbachS2SwitchedOutput N)

theorem mem_goldbachS2SwitchedSupport_iff
    {N n : ℕ} {T : ℝ} :
    n ∈ goldbachS2SwitchedSupport N T ↔
      ∃ x ∈ goldbachS2SwitchedLabels N T, goldbachS2SwitchedOutput N x = n := by
  simp [goldbachS2SwitchedSupport]

/-- The fibre multiplicity of the output value `b=N-rq`. -/
noncomputable def goldbachS2SwitchedWeight (N : ℕ) (T : ℝ) (n : ℕ) : ℝ :=
  (((goldbachS2SwitchedLabels N T).filter fun x => goldbachS2SwitchedOutput N x = n).card : ℝ)

/-- The relaxed switched sifted labels at the literal sieve cutoff `Z`. -/
noncomputable def goldbachS2SwitchedSiftedLabels
    (N : ℕ) (T Z : ℝ) : Finset (Sigma fun _r : ℕ => ℕ) :=
  (goldbachS2SwitchedLabels N T).filter fun x => SurvivesSieve N Z (goldbachS2SwitchedOutput N x)

theorem mem_goldbachS2SwitchedSiftedLabels_iff
    {N : ℕ} {T Z : ℝ} {x : Sigma fun _r : ℕ => ℕ} :
    x ∈ goldbachS2SwitchedSiftedLabels N T Z ↔
      x ∈ goldbachS2SwitchedLabels N T ∧
        SurvivesSieve N Z (goldbachS2SwitchedOutput N x) := by
  simp [goldbachS2SwitchedSiftedLabels]

/-- The literal sifted count on the relaxed switched labels. -/
noncomputable def goldbachS2SwitchedSiftedCount (N : ℕ) (T Z : ℝ) : ℕ :=
  (goldbachS2SwitchedSiftedLabels N T Z).card

/-- Exact divisor count on the relaxed switched labels. -/
noncomputable def goldbachS2SwitchedDivCount (N : ℕ) (T : ℝ) (d : ℕ) : ℕ :=
  (goldbachS2SwitchedDivisorLabels N T d).card

/-- The actual one-endpoint switched mass `X(N,T)`. -/
noncomputable def goldbachS2SwitchedMainMass (N : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ goldbachS2Primes N T,
    liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / r)

theorem goldbachS2SwitchedMainMass_nonneg
    (N : ℕ) (T : ℝ) :
    0 ≤ goldbachS2SwitchedMainMass N T := by
  unfold goldbachS2SwitchedMainMass
  apply Finset.sum_nonneg
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, _, hrSqN⟩
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hrPrime.pos
  have hrle : (r : ℝ) ≤ (N : ℝ) / r := by
    rw [le_div_iff₀ hrpos]
    simpa [pow_two] using (show (r : ℝ) ^ 2 ≤ N by exact_mod_cast hrSqN)
  have htwo : (2 : ℝ) ≤ (N : ℝ) / r :=
    (show (2 : ℝ) ≤ r by exact_mod_cast hrPrime.two_le).trans hrle
  exact liuLogarithmicIntegral_nonneg (2 / Real.log 2) (by positivity) htwo

private theorem S2Switched_pushforward_sum_eq_card_filter
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
      exact Finset.mem_filter.mpr ⟨hxA, (Finset.mem_filter.mp hxU).2⟩
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

theorem goldbachS2SwitchedWeight_sum_eq_card_labels
    (N : ℕ) (T : ℝ) :
    ∑ n ∈ goldbachS2SwitchedSupport N T, goldbachS2SwitchedWeight N T n =
      ((goldbachS2SwitchedLabels N T).card : ℝ) := by
  simpa [goldbachS2SwitchedSupport, goldbachS2SwitchedWeight] using
    (S2Switched_pushforward_sum_eq_card_filter
      (goldbachS2SwitchedLabels N T) (goldbachS2SwitchedOutput N) (fun _ => True))

theorem goldbachS2SwitchedWeight_nonneg
    (N : ℕ) (T : ℝ) (n : ℕ) :
    0 ≤ goldbachS2SwitchedWeight N T n := by
  unfold goldbachS2SwitchedWeight
  positivity

theorem goldbachS2Switched_coprime_prodPrimes_iff_survivesSieve
    (N : ℕ) (Z : ℝ) (n : ℕ) :
    Nat.Coprime (goldbachS1ProdPrimes N Z) n ↔ SurvivesSieve N Z n := by
  simpa [literalHPoint_one_iff_survivesSieve] using
    (goldbachS1_coprime_prodPrimes_iff_literalHPoint N Z n)

/-- The actual bounding sieve carried by the relaxed switched labels. -/
noncomputable def goldbachS2SwitchedBoundingSieve
    (N : ℕ) (hEven : Even N) (T Z : ℝ) : BoundingSieve where
  support := goldbachS2SwitchedSupport N T
  weights := goldbachS2SwitchedWeight N T
  weights_nonneg := goldbachS2SwitchedWeight_nonneg N T
  prodPrimes := goldbachS1ProdPrimes N Z
  prodPrimes_squarefree := goldbachS1ProdPrimes_squarefree N Z
  totalMass := goldbachS2SwitchedMainMass N T
  nu := AnalyticNumberTheory.Sieve.goldbachNu
  nu_mult := AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hpP
    exact AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hpP
    have hpN : ¬ p ∣ N := (prime_dvd_goldbachS1ProdPrimes_iff hp).mp hpP |>.2
    have hp2 : 2 < p := by
      have hpne : p ≠ 2 := by
        intro hpEq
        apply hpN
        rw [hpEq]
        exact even_iff_two_dvd.mp hEven
      exact lt_of_le_of_ne hp.two_le (by simpa using hpne.symm)
    exact AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hp hp2

theorem goldbachS2SwitchedBoundingSieve_multSum_eq_divCount
    (N : ℕ) (hEven : Even N) (T Z : ℝ) (d : ℕ) :
    (goldbachS2SwitchedBoundingSieve N hEven T Z).multSum d =
      (goldbachS2SwitchedDivCount N T d : ℝ) := by
  let A := goldbachS2SwitchedLabels N T
  let out := goldbachS2SwitchedOutput N
  calc
    (goldbachS2SwitchedBoundingSieve N hEven T Z).multSum d
        = ∑ n ∈ (A.image out).filter (fun n => d ∣ n),
            (((A.filter fun x => out x = n).card : ℕ) : ℝ) := by
              simp [goldbachS2SwitchedBoundingSieve, goldbachS2SwitchedSupport,
                goldbachS2SwitchedWeight, BoundingSieve.multSum, A, out, Finset.sum_filter]
    _ = (((A.filter fun x => d ∣ out x).card : ℕ) : ℝ) := by
          simpa [A, out] using
            S2Switched_pushforward_sum_eq_card_filter A out (fun n => d ∣ n)
    _ = (goldbachS2SwitchedDivCount N T d : ℝ) := by
          rw [show A.filter (fun x => d ∣ out x) = goldbachS2SwitchedDivisorLabels N T d by
            ext x
            simp [A, out, goldbachS2SwitchedDivisorLabels],
            goldbachS2SwitchedDivCount]

theorem goldbachS2SwitchedBoundingSieve_siftedSum_eq
    (N : ℕ) (hEven : Even N) (T Z : ℝ) :
    (goldbachS2SwitchedBoundingSieve N hEven T Z).siftedSum =
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) := by
  let A := goldbachS2SwitchedLabels N T
  let out := goldbachS2SwitchedOutput N
  let P := goldbachS1ProdPrimes N Z
  calc
    (goldbachS2SwitchedBoundingSieve N hEven T Z).siftedSum
        = ∑ n ∈ (A.image out).filter (fun n => Nat.Coprime P n),
            (((A.filter fun x => out x = n).card : ℕ) : ℝ) := by
              rw [goldbachS2SwitchedBoundingSieve, BoundingSieve.siftedSum, ← Finset.sum_filter]
              rfl
    _ = (((A.filter fun x => Nat.Coprime P (out x)).card : ℕ) : ℝ) := by
          simpa [A, out, P] using
            S2Switched_pushforward_sum_eq_card_filter A out (fun n => Nat.Coprime P n)
    _ = (((A.filter fun x => SurvivesSieve N Z (out x)).card : ℕ) : ℝ) := by
          rw [show A.filter (fun x => Nat.Coprime P (out x)) =
            A.filter (fun x => SurvivesSieve N Z (out x)) by
              ext x
              simp [P, out, goldbachS2Switched_coprime_prodPrimes_iff_survivesSieve]]
    _ = (goldbachS2SwitchedSiftedCount N T Z : ℝ) := by
          rw [show A.filter (fun x => SurvivesSieve N Z (out x)) =
            goldbachS2SwitchedSiftedLabels N T Z by
              ext x
              simp [A, out, goldbachS2SwitchedSiftedLabels],
            goldbachS2SwitchedSiftedCount]

theorem goldbachS2SwitchedBoundingSieve_nu_eq_inv_totient
    {N : ℕ} (hEven : Even N) {T Z : ℝ} {d : ℕ}
    (hd : d ∣ goldbachS1ProdPrimes N Z) :
    (goldbachS2SwitchedBoundingSieve N hEven T Z).nu d =
      (1 : ℝ) / Nat.totient d := by
  have hd' : d ∣ (goldbachS2SwitchedBoundingSieve N hEven T Z).prodPrimes := by
    simpa [goldbachS2SwitchedBoundingSieve] using hd
  exact AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient
    (BoundingSieve.squarefree_of_dvd_prodPrimes
      (s := goldbachS2SwitchedBoundingSieve N hEven T Z) hd')

theorem goldbachS2SwitchedBoundingSieve_mainSum_eq_totientSum
    {N : ℕ} (hEven : Even N) (T Z : ℝ) (μ : ℕ → ℝ) :
    (goldbachS2SwitchedBoundingSieve N hEven T Z).mainSum μ =
      ∑ d ∈ (goldbachS1ProdPrimes N Z).divisors, μ d / Nat.totient d := by
  unfold BoundingSieve.mainSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [goldbachS2SwitchedBoundingSieve_nu_eq_inv_totient (N := N) (hEven := hEven)
    (T := T) (Z := Z) ((Nat.mem_divisors.mp hd).1)]
  ring

theorem goldbachS2SwitchedBoundingSieve_rem_eq_divCount_sub
    {N : ℕ} (hEven : Even N) {T Z : ℝ} {d : ℕ}
    (hd : d ∣ goldbachS1ProdPrimes N Z) :
    (goldbachS2SwitchedBoundingSieve N hEven T Z).rem d =
      (goldbachS2SwitchedDivCount N T d : ℝ) -
        goldbachS2SwitchedMainMass N T / Nat.totient d := by
  unfold BoundingSieve.rem
  rw [goldbachS2SwitchedBoundingSieve_multSum_eq_divCount,
    goldbachS2SwitchedBoundingSieve_nu_eq_inv_totient
      (N := N) (hEven := hEven) (T := T) (Z := Z) hd]
  simp [goldbachS2SwitchedBoundingSieve, goldbachS2SwitchedMainMass,
    div_eq_mul_inv, mul_comm]

private theorem S2Switched_output_survives_of_prime
    {N p : ℕ} {Z : ℝ}
    (hpPrime : p.Prime)
    (hZ : Z ≤ (p : ℝ)) :
    SurvivesSieve N Z p := by
  intro ℓ hℓPrime hℓdvd _
  have hEq : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓPrime hpPrime).mp hℓdvd
  exact hEq.symm ▸ hZ

/-- The actual small-partner loss keeps the original ordered prime pairs whose
prime partner lies below the switched sieve cutoff. -/
noncomputable def goldbachS2SwitchedSmallPartnerLoss
    (N : ℕ) (ε T Z : ℝ) : ℕ :=
  ((goldbachS2PrimePairs N ε T).filter fun rq => ((N - rq.1 * rq.2 : ℕ) : ℝ) < Z).card

private noncomputable def S2SwitchedPrimePairsAboveCutoff
    (N : ℕ) (ε T Z : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachS2PrimePairs N ε T).filter fun rq => Z ≤ ((N - rq.1 * rq.2 : ℕ) : ℝ)

private theorem S2SwitchedPrimePairsAboveCutoff_mem_sifted
    {N : ℕ} {ε T Z : ℝ} {rq : ℕ × ℕ}
    (hrq : rq ∈ S2SwitchedPrimePairsAboveCutoff N ε T Z) :
    Sigma.mk rq.1 rq.2 ∈ goldbachS2SwitchedSiftedLabels N T Z := by
  rcases Finset.mem_filter.mp hrq with ⟨hrqMem, hZ⟩
  rcases mem_goldbachS2PrimePairs_iff.mp hrqMem with
    ⟨hrPrime, hqPrime, hrT, hrqOrd, hrSqN, hrCop, _hεProd, hprodLt, hpPrime⟩
  have hrMem : rq.1 ∈ goldbachS2Primes N T := by
    have hrLeN : rq.1 ≤ N := by
      calc
        rq.1 ≤ rq.1 * rq.1 := Nat.le_mul_of_pos_right _ hrPrime.pos
        _ = rq.1 ^ 2 := by simp [pow_two]
        _ ≤ N := hrSqN
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrPrime, hrCop.coprime_dvd_left (dvd_mul_of_dvd_left (dvd_refl rq.1) rq.2),
      hrT, hrSqN⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hrLeN)
  refine mem_goldbachS2SwitchedSiftedLabels_iff.mpr ?_
  have hZ' : Z ≤ (((N - rq.1 * rq.2 : ℕ) : ℝ)) := hZ
  refine ⟨mem_goldbachS2SwitchedLabels_iff.mpr ⟨hrMem, hqPrime, ?_⟩, ?_⟩
  · exact_mod_cast hprodLt
  · simpa [goldbachS2SwitchedOutput] using S2Switched_output_survives_of_prime hpPrime hZ'

theorem goldbachS2PrimePairs_card_le_switchedSiftedCount_add_smallPartnerLoss
    (N : ℕ) (ε T Z : ℝ) :
    (goldbachS2PrimePairs N ε T).card ≤
      goldbachS2SwitchedSiftedCount N T Z +
        goldbachS2SwitchedSmallPartnerLoss N ε T Z := by
  let A := goldbachS2PrimePairs N ε T
  let B := S2SwitchedPrimePairsAboveCutoff N ε T Z
  let C := (goldbachS2PrimePairs N ε T).filter fun rq => ¬((N - rq.1 * rq.2 : ℕ) : ℝ) < Z
  have hBC : B = C := by
    ext rq
    simp [B, C, S2SwitchedPrimePairsAboveCutoff, not_lt]
  have hsplit :
      (goldbachS2SwitchedSmallPartnerLoss N ε T Z) + C.card = A.card := by
    dsimp [goldbachS2SwitchedSmallPartnerLoss, A, C]
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := goldbachS2PrimePairs N ε T)
        (p := fun rq => ((N - rq.1 * rq.2 : ℕ) : ℝ) < Z))
  have hmap : Set.MapsTo (fun rq : ℕ × ℕ => (⟨rq.1, rq.2⟩ : Sigma fun _r : ℕ => ℕ)) (↑C)
      (↑(goldbachS2SwitchedSiftedLabels N T Z) : Set (Sigma fun _r : ℕ => ℕ)) := by
    intro rq hrq
    have hrq' : rq ∈ B := by simpa [hBC] using hrq
    exact S2SwitchedPrimePairsAboveCutoff_mem_sifted hrq'
  have hinj : Set.InjOn (fun rq : ℕ × ℕ => (⟨rq.1, rq.2⟩ : Sigma fun _r : ℕ => ℕ)) (↑C) := by
    intro a ha b hb hEq
    cases a
    cases b
    cases hEq
    rfl
  have hcardC : C.card ≤ (goldbachS2SwitchedSiftedLabels N T Z).card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  calc
    (goldbachS2PrimePairs N ε T).card
        = goldbachS2SwitchedSmallPartnerLoss N ε T Z + C.card := by
            simpa [A] using hsplit.symm
    _ ≤ goldbachS2SwitchedSmallPartnerLoss N ε T Z +
          (goldbachS2SwitchedSiftedLabels N T Z).card := by
            exact Nat.add_le_add_left hcardC _
    _ = goldbachS2SwitchedSiftedCount N T Z +
          goldbachS2SwitchedSmallPartnerLoss N ε T Z := by
            simp [goldbachS2SwitchedSiftedCount, Nat.add_comm]

private theorem S2Switched_primePair_eq_of_prod_eq
    {N : ℕ} {ε T : ℝ} {x y : ℕ × ℕ}
    (hx : x ∈ goldbachS2PrimePairs N ε T)
    (hy : y ∈ goldbachS2PrimePairs N ε T)
    (hprod : x.1 * x.2 = y.1 * y.2) :
    x = y := by
  rcases x with ⟨r, q⟩
  rcases y with ⟨s, t⟩
  rcases mem_goldbachS2PrimePairs_iff.mp hx with
    ⟨hrPrime, hqPrime, _, hrq, _, _, _, _, _⟩
  rcases mem_goldbachS2PrimePairs_iff.mp hy with
    ⟨hsPrime, htPrime, _, hst, _, _, _, _, _⟩
  have hrqNat : r ≤ q := by exact_mod_cast hrq
  have hstNat : s ≤ t := by exact_mod_cast hst
  have hdiv : r ∣ s * t := hprod ▸ dvd_mul_right _ _
  rcases hrPrime.dvd_mul.mp hdiv with hrs | hrt
  · have hrsEq : r = s := (Nat.prime_dvd_prime_iff_eq hrPrime hsPrime).mp hrs
    subst s
    have hqtEq : q = t := Nat.mul_left_cancel hrPrime.pos hprod
    simp [hqtEq]
  · have hrtEq : r = t := (Nat.prime_dvd_prime_iff_eq hrPrime htPrime).mp hrt
    have hsqEq : s = q := by
      apply Nat.mul_right_cancel hrPrime.pos
      simpa [hrtEq, Nat.mul_comm] using hprod.symm
    have hrqEq : r = q := by
      have : q ≤ r := by simpa [hsqEq, hrtEq] using hstNat
      omega
    subst q
    subst s
    subst t
    rfl

private theorem S2Switched_primePairPartner_injOn
    {N : ℕ} {ε T Z : ℝ} :
    Set.InjOn (fun rq : ℕ × ℕ => N - rq.1 * rq.2)
      (↑((goldbachS2PrimePairs N ε T).filter fun rq => ((N - rq.1 * rq.2 : ℕ) : ℝ) < Z) :
        Set (ℕ × ℕ)) := by
  intro x hx y hy hEq
  apply S2Switched_primePair_eq_of_prod_eq
    (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
  rcases mem_goldbachS2PrimePairs_iff.mp (Finset.mem_filter.mp hx).1 with
    ⟨_, _, _, _, _, _, _, hxlt, _⟩
  rcases mem_goldbachS2PrimePairs_iff.mp (Finset.mem_filter.mp hy).1 with
    ⟨_, _, _, _, _, _, _, hylt, _⟩
  have hxadd : x.1 * x.2 + (N - x.1 * x.2) = N := Nat.add_sub_of_le (Nat.le_of_lt (by exact_mod_cast hxlt))
  have hyadd : y.1 * y.2 + (N - y.1 * y.2) = N := Nat.add_sub_of_le (Nat.le_of_lt (by exact_mod_cast hylt))
  have hxadd' : x.1 * x.2 + (N - y.1 * y.2) = N := by simpa [hEq] using hxadd
  exact Nat.add_right_cancel (hxadd'.trans hyadd.symm)

theorem goldbachS2SwitchedSmallPartnerLoss_le_ceil
    (N : ℕ) (ε T Z : ℝ) :
    goldbachS2SwitchedSmallPartnerLoss N ε T Z ≤ Nat.ceil Z := by
  let A := (goldbachS2PrimePairs N ε T).filter fun rq => ((N - rq.1 * rq.2 : ℕ) : ℝ) < Z
  have hmap : Set.MapsTo (fun rq : ℕ × ℕ => N - rq.1 * rq.2) A (range (Nat.ceil Z)) := by
    intro rq hrq
    rcases Finset.mem_filter.mp hrq with ⟨hrqMem, hlt⟩
    rcases mem_goldbachS2PrimePairs_iff.mp hrqMem with
      ⟨_, _, _, _, _, _, _, _, hpPrime⟩
    refine Finset.mem_range.mpr ?_
    exact Nat.lt_ceil.mpr hlt
  have hinj : Set.InjOn (fun rq : ℕ × ℕ => N - rq.1 * rq.2) A :=
    S2Switched_primePairPartner_injOn
  have hcard :
      A.card ≤ (range (Nat.ceil Z)).card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  simpa [goldbachS2SwitchedSmallPartnerLoss, A] using hcard

theorem goldbachS2PrimePairs_card_le_switchedSiftedCount_add_ceil
    (N : ℕ) (ε T Z : ℝ) :
    (goldbachS2PrimePairs N ε T).card ≤
      goldbachS2SwitchedSiftedCount N T Z + Nat.ceil Z := by
  calc
    (goldbachS2PrimePairs N ε T).card ≤
        goldbachS2SwitchedSiftedCount N T Z +
          goldbachS2SwitchedSmallPartnerLoss N ε T Z :=
      goldbachS2PrimePairs_card_le_switchedSiftedCount_add_smallPartnerLoss N ε T Z
    _ ≤ goldbachS2SwitchedSiftedCount N T Z + Nat.ceil Z := by
      gcongr
      exact goldbachS2SwitchedSmallPartnerLoss_le_ceil N ε T Z

theorem goldbachS2_le_switchedSiftedCount_add_smallPartnerLoss_add_primeFactors
    (N : ℕ) (ε T Z : ℝ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hε1 : ε < 1) (hT : 0 < T)
    (hcube : (N : ℝ) < T ^ 3) (hsqrt : Real.sqrt N ≤ ε * N) :
    goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
      (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
        (goldbachS2SwitchedSmallPartnerLoss N ε T Z : ℤ) +
        (N.primeFactors.card : ℤ) := by
  obtain ⟨_, hbridge⟩ :=
    goldbachS2PrimePairs_bridge N ε T hN hε hε1 hT hcube hsqrt
  have hpair :
      ((goldbachS2PrimePairs N ε T).card : ℤ) ≤
        (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
          (goldbachS2SwitchedSmallPartnerLoss N ε T Z : ℤ) := by
    exact_mod_cast
      goldbachS2PrimePairs_card_le_switchedSiftedCount_add_smallPartnerLoss N ε T Z
  omega

theorem goldbachS2_le_switchedSiftedCount_add_ceil_add_primeFactors
    (N : ℕ) (ε T Z : ℝ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hε1 : ε < 1) (hT : 0 < T)
    (hcube : (N : ℝ) < T ^ 3) (hsqrt : Real.sqrt N ≤ ε * N) :
    goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
      (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
        (Nat.ceil Z : ℤ) +
        (N.primeFactors.card : ℤ) := by
  calc
    goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
        (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
          (goldbachS2SwitchedSmallPartnerLoss N ε T Z : ℤ) +
          (N.primeFactors.card : ℤ) :=
      goldbachS2_le_switchedSiftedCount_add_smallPartnerLoss_add_primeFactors
        N ε T Z hN hε hε1 hT hcube hsqrt
    _ ≤ (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
          (Nat.ceil Z : ℤ) +
          (N.primeFactors.card : ℤ) := by
            gcongr
            exact_mod_cast goldbachS2SwitchedSmallPartnerLoss_le_ceil N ε T Z

/-- The threshold is uniform in the later sieve cutoff, including moving cutoffs. -/
theorem goldbachS2_le_switchedSiftedCount_add_smallPartnerLoss_add_primeFactors_eventually
    (ε : ℝ) (hε : 0 < ε) (hε15 : ε < (2 / 15 : ℝ)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Z : ℝ,
      let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
      goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
        (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
          (goldbachS2SwitchedSmallPartnerLoss N ε T Z : ℤ) +
          (N.primeFactors.card : ℤ) := by
  obtain ⟨N₀, hpair⟩ := goldbachS2PrimePairs_bridge_eventually ε hε hε15
  refine ⟨N₀, ?_⟩
  intro N hN Z
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  have hp : ((goldbachS2PrimePairs N ε T).card : ℤ) ≤
      (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
        (goldbachS2SwitchedSmallPartnerLoss N ε T Z : ℤ) := by
    exact_mod_cast goldbachS2PrimePairs_card_le_switchedSiftedCount_add_smallPartnerLoss N ε T Z
  dsimp only [T] at hp
  exact (hpair N hN).2.trans (by omega)

/-- Uniform-cutoff form with the actual small-partner cardinality paid by ceil Z. -/
theorem goldbachS2_le_switchedSiftedCount_add_ceil_add_primeFactors_eventually
    (ε : ℝ) (hε : 0 < ε) (hε15 : ε < (2 / 15 : ℝ)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Z : ℝ,
      let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
      goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
        (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
          (Nat.ceil Z : ℤ) + (N.primeFactors.card : ℤ) := by
  obtain ⟨N₀, hN₀⟩ :=
    goldbachS2_le_switchedSiftedCount_add_smallPartnerLoss_add_primeFactors_eventually ε hε hε15
  refine ⟨N₀, ?_⟩
  intro N hN Z
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  have hsmall : (goldbachS2SwitchedSmallPartnerLoss N ε T Z : ℤ) ≤ (Nat.ceil Z : ℤ) := by
    exact_mod_cast goldbachS2SwitchedSmallPartnerLoss_le_ceil N ε T Z
  dsimp only [T] at hsmall
  exact (hN₀ N hN Z).trans (by omega)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig