import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibNt.SieveTheory.LiLiuGoldbachBadBound
import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG10Cofactor

open scoped BigOperators

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

noncomputable local instance instDecidableGoldbachS2PrimePairs (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The actual ordered prime-pair carrier attached to `S2` on the literal
difference set: `n = r*q` with `r ≤ q`, both primes retained as labels, and
`N - r*q` a strict prime partner. -/
noncomputable def goldbachS2PrimePairs (N : ℕ) (ε T : ℝ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)).product (range (N + 1))).filter fun rq =>
    rq.1.Prime ∧ rq.2.Prime ∧
      T ≤ (rq.1 : ℝ) ∧ (rq.1 : ℝ) ≤ rq.2 ∧ rq.1 ^ 2 ≤ N ∧
      Nat.Coprime (rq.1 * rq.2) N ∧
      ε * (N : ℝ) < (rq.1 * rq.2 : ℝ) ∧ (rq.1 * rq.2 : ℝ) < N ∧
      (N - rq.1 * rq.2).Prime

theorem mem_goldbachS2PrimePairs_iff
    {N : ℕ} {ε T : ℝ} {rq : ℕ × ℕ} :
    rq ∈ goldbachS2PrimePairs N ε T ↔
      rq.1.Prime ∧ rq.2.Prime ∧
        T ≤ (rq.1 : ℝ) ∧ (rq.1 : ℝ) ≤ rq.2 ∧ rq.1 ^ 2 ≤ N ∧
        Nat.Coprime (rq.1 * rq.2) N ∧
        ε * (N : ℝ) < (rq.1 * rq.2 : ℝ) ∧ (rq.1 * rq.2 : ℝ) < N ∧
        (N - rq.1 * rq.2).Prime := by
  simp only [goldbachS2PrimePairs, Finset.mem_filter]
  constructor
  · rintro ⟨_, hrq⟩
    exact hrq
  · rintro ⟨hrPrime, hqPrime, hrT, hrq, hrsqN, hcop, hεlt, hltN, hpPrime⟩
    refine ⟨?_, hrPrime, hqPrime, hrT, hrq, hrsqN, hcop, hεlt, hltN, hpPrime⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
    · apply Nat.lt_succ_of_le
      calc
        rq.1 ≤ rq.1 * rq.2 := Nat.le_mul_of_pos_right _ hqPrime.pos
        _ ≤ N := by exact_mod_cast hltN.le
    · apply Nat.lt_succ_of_le
      calc
        rq.2 ≤ rq.1 * rq.2 := Nat.le_mul_of_pos_left _ hrPrime.pos
        _ ≤ N := by exact_mod_cast hltN.le

private noncomputable def S2PrimePairsActualAtoms (N : ℕ) (ε T : ℝ) : Finset (Σ _r : ℕ, ℕ) :=
  (goldbachS2Primes N T).sigma fun r =>
    (goldbachDifferenceCarrier N ε).filter (literalHPoint N r r)

private theorem mem_S2PrimePairsActualAtoms_iff
    {N : ℕ} {ε T : ℝ} {x : Σ _r : ℕ, ℕ} :
    x ∈ S2PrimePairsActualAtoms N ε T ↔
      x.1 ∈ goldbachS2Primes N T ∧
        x.2 ∈ goldbachDifferenceCarrier N ε ∧
        literalHPoint N x.1 x.1 x.2 := by
  simp [S2PrimePairsActualAtoms]

private noncomputable def S2PrimePairsGoodActualAtoms (N : ℕ) (ε T : ℝ) :
    Finset (Σ _r : ℕ, ℕ) :=
  (S2PrimePairsActualAtoms N ε T).filter fun x => Nat.Coprime x.2 N

private theorem mem_S2PrimePairsGoodActualAtoms_iff
    {N : ℕ} {ε T : ℝ} {x : Σ _r : ℕ, ℕ} :
    x ∈ S2PrimePairsGoodActualAtoms N ε T ↔
      x ∈ S2PrimePairsActualAtoms N ε T ∧ Nat.Coprime x.2 N := by
  simp [S2PrimePairsGoodActualAtoms]

private noncomputable def S2PrimePairsBadActualAtoms (N : ℕ) (ε T : ℝ) :
    Finset (Σ _r : ℕ, ℕ) :=
  (S2PrimePairsActualAtoms N ε T).filter fun x => ¬Nat.Coprime x.2 N

private theorem mem_S2PrimePairsBadActualAtoms_iff
    {N : ℕ} {ε T : ℝ} {x : Σ _r : ℕ, ℕ} :
    x ∈ S2PrimePairsBadActualAtoms N ε T ↔
      x ∈ S2PrimePairsActualAtoms N ε T ∧ ¬Nat.Coprime x.2 N := by
  simp [S2PrimePairsBadActualAtoms]

private theorem S2PrimePairs_label_eq_of_points
    {N n r s : ℕ} {T : ℝ}
    (hr : r ∈ goldbachS2Primes N T)
    (hs : s ∈ goldbachS2Primes N T)
    (hrPoint : literalHPoint N r r n)
    (hsPoint : literalHPoint N s s n) :
    r = s := by
  rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, hrCop, _, _⟩
  rcases Finset.mem_filter.mp hs with ⟨_, hsPrime, hsCop, _, _⟩
  by_contra hrs
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · have hrNotDvd : ¬r ∣ N := hrPrime.coprime_iff_not_dvd.mp hrCop
    have hsLe : (s : ℝ) ≤ r := hsPoint.2 r hrPrime hrPoint.1 hrNotDvd
    have hsLeNat : s ≤ r := by exact_mod_cast hsLe
    exact (not_le_of_gt hlt) hsLeNat
  · have hsNotDvd : ¬s ∣ N := hsPrime.coprime_iff_not_dvd.mp hsCop
    have hrLe : (r : ℝ) ≤ s := hrPoint.2 s hsPrime hsPoint.1 hsNotDvd
    have hrLeNat : r ≤ s := by exact_mod_cast hrLe
    exact (not_le_of_gt hgt) hrLeNat

theorem goldbachS2PrimePairs_point_le_one (N n : ℕ) (T : ℝ) :
    goldbachS2Point N T n ≤ 1 := by
  classical
  let S := (goldbachS2Primes N T).filter fun r => literalHPoint N r r n
  have hcard : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro r hr s hs
    exact S2PrimePairs_label_eq_of_points
      ((Finset.mem_filter.mp hr).1) ((Finset.mem_filter.mp hs).1)
      ((Finset.mem_filter.mp hr).2) ((Finset.mem_filter.mp hs).2)
  unfold goldbachS2Point
  exact_mod_cast hcard

private theorem S2PrimePairs_actualAtoms_eq_of_snd_eq
    {N : ℕ} {ε T : ℝ} {x y : Σ _r : ℕ, ℕ}
    (hx : x ∈ S2PrimePairsActualAtoms N ε T)
    (hy : y ∈ S2PrimePairsActualAtoms N ε T)
    (hxy : x.2 = y.2) :
    x = y := by
  have hrEq : x.1 = y.1 := S2PrimePairs_label_eq_of_points
    (mem_S2PrimePairsActualAtoms_iff.mp hx).1
    (mem_S2PrimePairsActualAtoms_iff.mp hy).1
    (mem_S2PrimePairsActualAtoms_iff.mp hx).2.2
    (by simpa [hxy] using (mem_S2PrimePairsActualAtoms_iff.mp hy).2.2)
  cases x
  cases y
  simp at hrEq hxy ⊢
  subst hrEq
  simpa using hxy

private theorem S2PrimePairs_actualAtoms_card_eq_goldbachS2
    (N : ℕ) (ε T : ℝ) :
    ((S2PrimePairsActualAtoms N ε T).card : ℤ) =
      goldbachS2 (goldbachDifferenceCarrier N ε) N T := by
  simp [S2PrimePairsActualAtoms, goldbachS2, literalH]

private theorem S2PrimePairs_badActualAtoms_card_le_badCount
    (N : ℕ) (ε T : ℝ) :
    ((S2PrimePairsBadActualAtoms N ε T).card : ℤ) ≤
      goldbachBadCount (goldbachDifferenceCarrier N ε) N := by
  let B : Finset ℕ := (goldbachDifferenceCarrier N ε).filter fun n => ¬Nat.Coprime n N
  have hmap : Set.MapsTo (fun x : Σ _r : ℕ, ℕ => x.2) (S2PrimePairsBadActualAtoms N ε T) B := by
    intro x hx
    rcases mem_S2PrimePairsBadActualAtoms_iff.mp hx with ⟨hxActual, hxBad⟩
    exact Finset.mem_filter.mpr ⟨(mem_S2PrimePairsActualAtoms_iff.mp hxActual).2.1, hxBad⟩
  have hinj : Set.InjOn (fun x : Σ _r : ℕ, ℕ => x.2) (S2PrimePairsBadActualAtoms N ε T) := by
    intro x hx y hy hEq
    exact S2PrimePairs_actualAtoms_eq_of_snd_eq
      (mem_S2PrimePairsBadActualAtoms_iff.mp hx).1
      (mem_S2PrimePairsBadActualAtoms_iff.mp hy).1 hEq
  have hcard : (S2PrimePairsBadActualAtoms N ε T).card ≤ B.card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  simpa [goldbachBadCount, B] using hcard

private theorem S2PrimePairs_diff_carrier_prod_mem
    {N : ℕ} {ε : ℝ} {r q : ℕ}
    (hε : 0 < ε) (_hε1 : ε < 1)
    (hpPrime : (N - r * q).Prime)
    (hprodLt : (r * q : ℝ) < N) :
    r * q ∈ goldbachDifferenceCarrier N ε ↔
      ε * (N : ℝ) < (r * q : ℝ) := by
  constructor
  · intro hn
    simpa [Nat.cast_mul] using
      (goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) hε hn).2.2
  · intro hprodGt
    have hprodLe : r * q ≤ N := by exact_mod_cast hprodLt.le
    have hpCut : ((N - r * q : ℕ) : ℝ) < (1 - ε) * N := by
      rw [Nat.cast_sub hprodLe]
      have hprodGt' : ε * (N : ℝ) < (r : ℝ) * q := by simpa [Nat.cast_mul] using hprodGt
      have htmp : (N : ℝ) - (r : ℝ) * q < (1 - ε) * N := by
        nlinarith
      simpa [Nat.cast_mul] using htmp
    have hpMem :
        N - r * q ∈ goldbachPrimeCarrier N ε :=
      (mem_goldbachPrimeCarrier_iff (N := N) (p := N - r * q) (ε := ε) (le_of_lt hε)).mpr
        ⟨hpPrime, hpCut⟩
    apply Finset.mem_image.mpr
    refine ⟨N - r * q, hpMem, ?_⟩
    omega

private theorem S2PrimePairs_prime_divisor_lower
    {N n r q ℓ : ℕ}
    (hcop : Nat.Coprime n N)
    (hpoint : literalHPoint N r r n)
    (hnmul : r * q = n)
    (hℓPrime : ℓ.Prime)
    (hℓdvd : ℓ ∣ q) :
    (r : ℝ) ≤ ℓ := by
  have hqdvdn : q ∣ n := ⟨r, by simpa [Nat.mul_comm] using hnmul.symm⟩
  have hℓdvdn : ℓ ∣ n := dvd_trans hℓdvd hqdvdn
  have hℓNotDvd : ¬ℓ ∣ N := prime_not_dvd_of_coprime hcop hℓPrime hℓdvdn
  exact hpoint.2 ℓ hℓPrime hℓdvdn hℓNotDvd

private noncomputable def S2PrimePairsEncode (x : Σ _r : ℕ, ℕ) : ℕ × ℕ :=
  (x.1, x.2 / x.1)

private theorem S2PrimePairs_goodActualAtoms_encode_mem
    {N : ℕ} {ε T : ℝ}
    (hN : 2 ≤ N) (hε : 0 < ε) (hT : 0 < T)
    (hcube : (N : ℝ) < T ^ 3) (hsqrt : Real.sqrt N ≤ ε * N)
    {x : Σ _r : ℕ, ℕ}
    (hx : x ∈ S2PrimePairsGoodActualAtoms N ε T) :
    S2PrimePairsEncode x ∈ goldbachS2PrimePairs N ε T := by
  rcases mem_S2PrimePairsGoodActualAtoms_iff.mp hx with ⟨hxActual, hxCop⟩
  rcases mem_S2PrimePairsActualAtoms_iff.mp hxActual with ⟨hrMem, hnA, hpoint⟩
  rcases Finset.mem_filter.mp hrMem with ⟨_, hrPrime, hrCop, hrT, hrSqN⟩
  obtain ⟨p, hpPrime, _, hpEq⟩ := goldbachDifferenceCarrier_prime_data (N := N) (n := x.2)
    (ε := ε) hε hnA
  have hnBounds := goldbachG10DifferenceCarrier_bounds (N := N) (n := x.2) (ε := ε) hε hnA
  have hxDiv : x.1 ∣ x.2 := hpoint.1
  have hmul : x.1 * (x.2 / x.1) = x.2 := Nat.mul_div_cancel' hxDiv
  have hcastDiv : (((x.2 / x.1 : ℕ) : ℝ)) = (x.2 : ℝ) / x.1 := by
    rw [Nat.cast_div hxDiv (Nat.cast_ne_zero.mpr hrPrime.ne_zero)]
  have hmulR : (x.1 : ℝ) * (((x.2 / x.1 : ℕ) : ℝ)) = x.2 := by
    exact_mod_cast hmul
  have hrSqrtSq : ((x.1 : ℝ) ^ 2) ≤ N := by exact_mod_cast hrSqN
  have hrLeSqrt : (x.1 : ℝ) ≤ Real.sqrt N := by
    by_contra hlt
    have hsqrtLt : Real.sqrt N < x.1 := lt_of_not_ge hlt
    have hsqLt : N < (x.1 : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [Real.sq_sqrt hNnonneg, Real.sqrt_nonneg (N : ℝ), hsqrtLt]
    exact not_lt_of_ge hrSqrtSq hsqLt
  have hrLtN : (x.1 : ℝ) < x.2 := by
    exact lt_of_le_of_lt (le_trans hrLeSqrt hsqrt) hnBounds.2.2
  have hquotGtOne : 1 < x.2 / x.1 := by
    have hquotPos : 0 < x.2 / x.1 := by
      refine Nat.pos_of_ne_zero ?_
      intro hzero
      have : x.2 = 0 := by simpa [hzero] using hmul.symm
      omega
    by_contra hq
    have hqle : x.2 / x.1 ≤ 1 := Nat.not_lt.mp hq
    have hx1Pos : 0 < x.1 := hrPrime.pos
    have hxLe : x.2 ≤ x.1 := by
      calc
        x.2 = x.1 * (x.2 / x.1) := hmul.symm
        _ ≤ x.1 * 1 := Nat.mul_le_mul_left _ hqle
        _ = x.1 := by simp
    have hrLtNNat : x.1 < x.2 := by exact_mod_cast hrLtN
    exact (not_le_of_gt hrLtNNat) hxLe
  have hqPrime : (x.2 / x.1).Prime := by
    by_contra hqPrime
    have hquotPos : 0 < x.2 / x.1 := by
      refine Nat.pos_of_ne_zero ?_
      intro hzero
      have : x.2 = 0 := by simpa [hzero] using hmul.symm
      omega
    have hquotMinPrime : (x.2 / x.1).minFac.Prime :=
      Nat.minFac_prime (by omega)
    have hquotMinDvd : (x.2 / x.1).minFac ∣ x.2 / x.1 :=
      Nat.minFac_dvd (x.2 / x.1)
    have hquotMinGe : x.1 ≤ (x.2 / x.1).minFac := by
      have h := S2PrimePairs_prime_divisor_lower hxCop hpoint hmul hquotMinPrime hquotMinDvd
      exact_mod_cast h
    have hquotGeSq : x.1 ^ 2 ≤ x.2 / x.1 := by
      calc
        x.1 ^ 2 ≤ (x.2 / x.1).minFac ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hquotMinGe hquotMinGe
        _ ≤ x.2 / x.1 := Nat.minFac_sq_le_self hquotPos hqPrime
    have hrCubeLe : x.1 ^ 3 ≤ x.2 := by
      calc
        x.1 ^ 3 = x.1 * x.1 ^ 2 := by rw [pow_succ, pow_two, Nat.mul_assoc]
        _ ≤ x.1 * (x.2 / x.1) := Nat.mul_le_mul_left _ hquotGeSq
        _ = x.2 := hmul
    have hrCubeLt : ((x.1 : ℝ) ^ 3) < N := by
      exact_mod_cast lt_of_le_of_lt hrCubeLe hnBounds.2.1
    have hTN : T ^ 3 ≤ (x.1 : ℝ) ^ 3 := by
      exact pow_le_pow_left₀ hT.le hrT 3
    linarith
  have hqGe : (x.1 : ℝ) ≤ x.2 / x.1 := by
    simpa [hcastDiv] using
      S2PrimePairs_prime_divisor_lower hxCop hpoint hmul hqPrime (dvd_refl _)
  let q : ℕ := x.2 / x.1
  have hmulNat : x.1 * q = x.2 := by simpa [q] using hmul
  have hmulReal : (x.1 * q : ℝ) = x.2 := by exact_mod_cast hmulNat
  have hqGe' : (x.1 : ℝ) ≤ q := by simpa [q, hcastDiv] using hqGe
  have hprodLt : (x.1 * q : ℝ) < N := by
    simpa [hmulReal] using (show (x.2 : ℝ) < N by exact_mod_cast hnBounds.2.1)
  have hεProd : ε * (N : ℝ) < (x.1 * q : ℝ) := by
    simpa [hmulReal] using hnBounds.2.2
  have hpPrime' : (N - x.1 * q).Prime := by
    have hmulNat' : x.1 * q = N - p := by simpa [q, hpEq] using hmul
    have hxLtN : x.2 < N := hnBounds.2.1
    have hsub : N - x.1 * q = p := by omega
    simpa [hsub] using hpPrime
  have hPair : (x.1, q) ∈ goldbachS2PrimePairs N ε T := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp hrMem).1
    · exact Finset.mem_range.mpr <|
        lt_of_le_of_lt (Nat.div_le_self _ _) <| Nat.lt_succ_of_lt hnBounds.2.1
    · exact ⟨hrPrime, by simpa [q] using hqPrime, hrT, hqGe', hrSqN,
        by simpa [q, hmulNat] using hxCop,
        hεProd, hprodLt, hpPrime'⟩
  simpa [S2PrimePairsEncode, q] using hPair

private theorem S2PrimePairs_prod_survives
    {N r q : ℕ}
    (hrPrime : r.Prime) (hqPrime : q.Prime)
    (hrq : (r : ℝ) ≤ q) :
    SurvivesSieve N r (r * q) := by
  intro ℓ hℓPrime hℓdvd _
  rcases hℓPrime.dvd_mul.mp hℓdvd with hℓr | hℓq
  · have hEq : ℓ = r := (Nat.prime_dvd_prime_iff_eq hℓPrime hrPrime).mp hℓr
    cases hEq
    exact le_rfl
  · have hEq : ℓ = q := (Nat.prime_dvd_prime_iff_eq hℓPrime hqPrime).mp hℓq
    exact hEq.symm ▸ hrq

private theorem S2PrimePairs_mem_image_encode
    {N : ℕ} {ε T : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    {rq : ℕ × ℕ}
    (hrqMem : rq ∈ goldbachS2PrimePairs N ε T) :
    rq ∈ (S2PrimePairsGoodActualAtoms N ε T).image S2PrimePairsEncode := by
  rcases mem_goldbachS2PrimePairs_iff.mp hrqMem with
    ⟨hrPrime, hqPrime, hrT, hrq, hrSqN, hcop, hεProd, hprodLt, hpPrime⟩
  have hprodLe : rq.1 * rq.2 ≤ N := by exact_mod_cast hprodLt.le
  have hrCop : Nat.Coprime rq.1 N :=
    hcop.coprime_dvd_left (dvd_mul_of_dvd_left (dvd_refl rq.1) rq.2)
  have hrMem : rq.1 ∈ goldbachS2Primes N T := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrPrime, hrCop, hrT, hrSqN⟩
    exact Finset.mem_range.mpr (by
      apply Nat.lt_succ_of_le
      exact le_trans (Nat.le_mul_of_pos_right _ hqPrime.pos) hprodLe)
  have hnA : rq.1 * rq.2 ∈ goldbachDifferenceCarrier N ε := by
    exact (S2PrimePairs_diff_carrier_prod_mem (N := N) (ε := ε) (r := rq.1) (q := rq.2)
      hε hε1 hpPrime hprodLt).2 hεProd
  have hpoint : literalHPoint N rq.1 rq.1 (rq.1 * rq.2) := by
    refine ⟨dvd_mul_right rq.1 rq.2, ?_⟩
    exact S2PrimePairs_prod_survives hrPrime hqPrime hrq
  have hgood :
      Sigma.mk rq.1 (rq.1 * rq.2) ∈ S2PrimePairsGoodActualAtoms N ε T := by
    refine Finset.mem_filter.mpr ⟨?_, hcop⟩
    exact mem_S2PrimePairsActualAtoms_iff.mpr ⟨hrMem, hnA, hpoint⟩
  refine Finset.mem_image.mpr ⟨Sigma.mk rq.1 (rq.1 * rq.2), hgood, ?_⟩
  dsimp [S2PrimePairsEncode]
  congr 1
  calc
    (rq.1 * rq.2) / rq.1 = rq.2 := by
      simpa [Nat.mul_comm] using (Nat.mul_div_right rq.2 hrPrime.pos)

private theorem S2PrimePairs_goodActualAtoms_image_encode
    (N : ℕ) (ε T : ℝ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hε1 : ε < 1)
    (hT : 0 < T) (hcube : (N : ℝ) < T ^ 3) (hsqrt : Real.sqrt N ≤ ε * N) :
    (S2PrimePairsGoodActualAtoms N ε T).image S2PrimePairsEncode =
      goldbachS2PrimePairs N ε T := by
  ext rq
  constructor
  · intro hrqMem
    rcases Finset.mem_image.mp hrqMem with ⟨x, hx, rfl⟩
    exact S2PrimePairs_goodActualAtoms_encode_mem hN hε hT hcube hsqrt hx
  · intro hrqMem
    exact S2PrimePairs_mem_image_encode hε hε1 hrqMem

private theorem S2PrimePairs_encode_injOn
    {N : ℕ} {ε T : ℝ} :
    Set.InjOn S2PrimePairsEncode (S2PrimePairsGoodActualAtoms N ε T) := by
  intro x hx y hy hEq
  have hfst : x.1 = y.1 := congrArg Prod.fst hEq
  have hdiv : x.2 / x.1 = y.2 / y.1 := congrArg Prod.snd hEq
  have hxDiv : x.1 ∣ x.2 := (mem_S2PrimePairsActualAtoms_iff.mp
    (mem_S2PrimePairsGoodActualAtoms_iff.mp hx).1).2.2.1
  have hyDiv : y.1 ∣ y.2 := (mem_S2PrimePairsActualAtoms_iff.mp
    (mem_S2PrimePairsGoodActualAtoms_iff.mp hy).1).2.2.1
  have hxySnd : x.2 = y.2 := by
    have hdiv' : x.2 / y.1 = y.2 / y.1 := by simpa [hfst] using hdiv
    calc
      x.2 = x.1 * (x.2 / x.1) := (Nat.mul_div_cancel' hxDiv).symm
      _ = y.1 * (x.2 / y.1) := by rw [hfst]
      _ = y.1 * (y.2 / y.1) := by rw [hdiv']
      _ = y.2 := Nat.mul_div_cancel' hyDiv
  exact S2PrimePairs_actualAtoms_eq_of_snd_eq
    (mem_S2PrimePairsGoodActualAtoms_iff.mp hx).1
    (mem_S2PrimePairsGoodActualAtoms_iff.mp hy).1 hxySnd

private theorem S2PrimePairs_goodActualAtoms_card_eq
    (N : ℕ) (ε T : ℝ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hε1 : ε < 1)
    (hT : 0 < T) (hcube : (N : ℝ) < T ^ 3) (hsqrt : Real.sqrt N ≤ ε * N) :
    (S2PrimePairsGoodActualAtoms N ε T).card = (goldbachS2PrimePairs N ε T).card := by
  calc
    (S2PrimePairsGoodActualAtoms N ε T).card =
        ((S2PrimePairsGoodActualAtoms N ε T).image S2PrimePairsEncode).card := by
          symm
          exact Finset.card_image_of_injOn (S2PrimePairs_encode_injOn (N := N) (ε := ε) (T := T))
    _ = (goldbachS2PrimePairs N ε T).card := by
          rw [S2PrimePairs_goodActualAtoms_image_encode N ε T hN hε hε1 hT hcube hsqrt]

theorem goldbachS2PrimePairs_bridge
    (N : ℕ) (ε T : ℝ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hε1 : ε < 1) (hT : 0 < T)
    (hcube : (N : ℝ) < T ^ 3) (hsqrt : Real.sqrt N ≤ ε * N) :
    ((goldbachS2PrimePairs N ε T).card : ℤ) ≤
        goldbachS2 (goldbachDifferenceCarrier N ε) N T ∧
      goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
        ((goldbachS2PrimePairs N ε T).card : ℤ) + (N.primeFactors.card : ℤ) := by
  let A := S2PrimePairsActualAtoms N ε T
  let G := S2PrimePairsGoodActualAtoms N ε T
  let B := S2PrimePairsBadActualAtoms N ε T
  have hDisj : Disjoint G B := by
    classical
    refine Finset.disjoint_left.mpr ?_
    intro x hxG hxB
    exact (mem_S2PrimePairsBadActualAtoms_iff.mp hxB).2
      ((mem_S2PrimePairsGoodActualAtoms_iff.mp hxG).2)
  have hUnion : G ∪ B = A := by
    classical
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxG | hxB
      · exact (mem_S2PrimePairsGoodActualAtoms_iff.mp hxG).1
      · exact (mem_S2PrimePairsBadActualAtoms_iff.mp hxB).1
    · intro hxA
      by_cases hcop : Nat.Coprime x.2 N
      · exact Finset.mem_union.mpr <|
          Or.inl <| mem_S2PrimePairsGoodActualAtoms_iff.mpr ⟨hxA, hcop⟩
      · exact Finset.mem_union.mpr <|
          Or.inr <| mem_S2PrimePairsBadActualAtoms_iff.mpr ⟨hxA, hcop⟩
  have hcardNat : A.card = G.card + B.card := by
    rw [← hUnion]
    exact Finset.card_union_eq_card_add_card.mpr hDisj
  have hActual :
      ((A.card : ℕ) : ℤ) = goldbachS2 (goldbachDifferenceCarrier N ε) N T := by
    simpa [A] using S2PrimePairs_actualAtoms_card_eq_goldbachS2 N ε T
  have hGood :
      G.card = (goldbachS2PrimePairs N ε T).card := by
    simpa [G] using S2PrimePairs_goodActualAtoms_card_eq N ε T hN hε hε1 hT hcube hsqrt
  have hGoodZ : (G.card : ℤ) = ((goldbachS2PrimePairs N ε T).card : ℤ) := by
    exact_mod_cast hGood
  have hBad :
      ((B.card : ℕ) : ℤ) ≤ goldbachBadCount (goldbachDifferenceCarrier N ε) N := by
    simpa [B] using S2PrimePairs_badActualAtoms_card_le_badCount N ε T
  have hN0 : N ≠ 0 := by omega
  have hBadPf :
      ((B.card : ℕ) : ℤ) ≤ (N.primeFactors.card : ℤ) := by
    exact hBad.trans (goldbachBadCount_le_primeFactors N ε hN0)
  have hBadPfAdd :
      (G.card : ℤ) + (B.card : ℤ) ≤ (G.card : ℤ) + (N.primeFactors.card : ℤ) := by
    omega
  constructor
  · calc
      ((goldbachS2PrimePairs N ε T).card : ℤ) = (G.card : ℤ) := by simpa using hGoodZ.symm
      _ ≤ ((G.card + B.card : ℕ) : ℤ) := by exact_mod_cast Nat.le_add_right G.card B.card
      _ = (A.card : ℤ) := by exact_mod_cast hcardNat.symm
      _ = goldbachS2 (goldbachDifferenceCarrier N ε) N T := hActual
  · calc
      goldbachS2 (goldbachDifferenceCarrier N ε) N T = (A.card : ℤ) := hActual.symm
      _ = (G.card : ℤ) + (B.card : ℤ) := by exact_mod_cast hcardNat
      _ ≤ (G.card : ℤ) + (N.primeFactors.card : ℤ) := hBadPfAdd
      _ = ((goldbachS2PrimePairs N ε T).card : ℤ) + (N.primeFactors.card : ℤ) := by
            omega

theorem goldbachS2PrimePairs_bridge_eventually
    (ε : ℝ) (hε : 0 < ε) (hε15 : ε < (2 / 15 : ℝ)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
      ((goldbachS2PrimePairs N ε T).card : ℤ) ≤
          goldbachS2 (goldbachDifferenceCarrier N ε) N T ∧
        goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
          ((goldbachS2PrimePairs N ε T).card : ℤ) + (N.primeFactors.card : ℤ) := by
  let N₀ : ℕ := max 2 ⌈1 / ε ^ (2 : ℕ)⌉₊
  refine ⟨N₀, ?_⟩
  intro N hNN₀
  let β : ℝ := (9 : ℝ) / 19 - ε
  let T : ℝ := (N : ℝ) ^ β
  have hN : 2 ≤ N := (le_max_left _ _).trans hNN₀
  have hε1 : ε < 1 := by linarith
  have hβ : (1 : ℝ) / 3 < β := by
    dsimp [β]
    nlinarith
  have hT : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by positivity : 0 < (N : ℝ)) _
  have hceil : 1 / ε ^ (2 : ℕ) ≤ (N : ℝ) := by
    calc
      1 / ε ^ (2 : ℕ) ≤ (⌈1 / ε ^ (2 : ℕ)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ N := by
        exact_mod_cast (show ⌈1 / ε ^ (2 : ℕ)⌉₊ ≤ N from (le_max_right _ _).trans hNN₀)
  have hsqrt : Real.sqrt N ≤ ε * N := by
    have hmul :
        ε ^ (2 : ℕ) * (1 / ε ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ) * N :=
      mul_le_mul_of_nonneg_left hceil (by positivity)
    have hone : (1 : ℝ) ≤ ε ^ (2 : ℕ) * N := by
      have hεsqne : ε ^ (2 : ℕ) ≠ 0 := by positivity
      simpa [div_eq_mul_inv, hεsqne, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hsq : (N : ℝ) ≤ (ε * N) ^ 2 := by
      have hmulN := mul_le_mul_of_nonneg_right hone (show 0 ≤ (N : ℝ) by positivity)
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmulN
    have hsq' : (Real.sqrt N) ^ 2 ≤ (ε * N) ^ 2 := by
      simpa [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)] using hsq
    have hright : 0 ≤ ε * N := by positivity
    nlinarith [Real.sqrt_nonneg (N : ℝ), hsq']
  have hcube : (N : ℝ) < T ^ 3 := by
    have hN1 : (1 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hN)
    have hpow :
        (N : ℝ) ^ (1 : ℝ) < (N : ℝ) ^ (β * (3 : ℝ)) := by
      exact Real.rpow_lt_rpow_of_exponent_lt hN1 (by nlinarith)
    have hpow3 : T ^ 3 = (N : ℝ) ^ (β * (3 : ℝ)) := by
      dsimp [T]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
      norm_num
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by simp
      _ < (N : ℝ) ^ (β * (3 : ℝ)) := hpow
      _ = T ^ 3 := hpow3.symm
  exact goldbachS2PrimePairs_bridge N ε T hN hε hε1 hT hcube hsqrt

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig