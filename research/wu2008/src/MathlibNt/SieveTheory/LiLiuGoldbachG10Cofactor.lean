import MathlibNt.SieveTheory.LiLiuGoldbachErrorFoundations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorization.Basic

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachG10Cofactor (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The corrected closed pair carrier for the finite G10 switch. -/
noncomputable def goldbachC10Pairs (N : ℕ) (b c : ℝ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)).product (range (N + 1))).filter fun rs =>
    rs.1.Prime ∧ rs.2.Prime ∧ Nat.Coprime (rs.1 * rs.2) N ∧
      b ≤ (rs.1 : ℝ) ∧ (rs.1 : ℝ) ≤ c ∧ c ≤ (rs.2 : ℝ) ∧ rs.1 * rs.2 ^ 2 ≤ N

theorem mem_goldbachC10Pairs_iff {N : ℕ} {b c : ℝ} {rs : ℕ × ℕ} :
    rs ∈ goldbachC10Pairs N b c ↔
      rs.1.Prime ∧ rs.2.Prime ∧ Nat.Coprime (rs.1 * rs.2) N ∧
        b ≤ (rs.1 : ℝ) ∧ (rs.1 : ℝ) ≤ c ∧ c ≤ (rs.2 : ℝ) ∧ rs.1 * rs.2 ^ 2 ≤ N := by
  simp only [goldbachC10Pairs, Finset.mem_filter]
  constructor
  · rintro ⟨_, hrs⟩
    exact hrs
  · intro hrs
    refine ⟨?_, hrs⟩
    simp [Finset.mem_product, Finset.mem_range]
    constructor
    · exact Nat.le_trans (Nat.le_mul_of_pos_right rs.1 (pow_pos hrs.2.1.pos 2)) hrs.2.2.2.2.2.2
    · have hsleSq : rs.2 ≤ rs.2 ^ 2 := by
        calc
          rs.2 = rs.2 * 1 := by simp
          _ ≤ rs.2 * rs.2 := by gcongr; exact hrs.2.1.one_le
          _ = rs.2 ^ 2 := by rw [pow_two]
      exact le_trans hsleSq <|
        le_trans (Nat.le_mul_of_pos_left (rs.2 ^ 2) hrs.1.pos) hrs.2.2.2.2.2.2

/-- The product label attached to a corrected G10 pair. -/
def goldbachC10Prod (rs : ℕ × ℕ) : ℕ := rs.1 * rs.2

/-- The literal square-root cutoff attached to a corrected G10 pair. -/
noncomputable def goldbachC10Cutoff (N : ℕ) (rs : ℕ × ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) / (goldbachC10Prod rs : ℝ))

/-- The corrected literal finite G10 sum, keeping the modulus `N*r*s`. -/
noncomputable def goldbachG10Corrected (A : Finset ℕ) (N : ℕ) (b c : ℝ) : ℤ :=
  ∑ rs ∈ goldbachC10Pairs N b c,
    literalH A (N * goldbachC10Prod rs) (goldbachC10Prod rs) (goldbachC10Cutoff N rs)

/-- The corrected G10 fibre above a fixed pair label. -/
noncomputable def goldbachG10CorrectedFiber (A : Finset ℕ) (N : ℕ) (rs : ℕ × ℕ) : Finset ℕ :=
  A.filter (literalHPoint (N * goldbachC10Prod rs) (goldbachC10Prod rs) (goldbachC10Cutoff N rs))

/-- Pair-labelled corrected G10 atoms. -/
noncomputable def goldbachG10CorrectedAtoms
    (A : Finset ℕ) (N : ℕ) (b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachC10Pairs N b c).sigma (goldbachG10CorrectedFiber A N)

theorem goldbachG10Corrected_eq_card_atoms (A : Finset ℕ) (N : ℕ) (b c : ℝ) :
    goldbachG10Corrected A N b c = ((goldbachG10CorrectedAtoms A N b c).card : ℤ) := by
  simp [goldbachG10Corrected, goldbachG10CorrectedAtoms, goldbachG10CorrectedFiber, literalH]

theorem mem_goldbachG10CorrectedAtoms_iff
    {A : Finset ℕ} {N : ℕ} {b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10CorrectedAtoms A N b c ↔
      x.1 ∈ goldbachC10Pairs N b c ∧
        x.2 ∈ A ∧
        literalHPoint (N * goldbachC10Prod x.1) (goldbachC10Prod x.1)
          (goldbachC10Cutoff N x.1) x.2 := by
  simp [goldbachG10CorrectedAtoms, goldbachG10CorrectedFiber]

/-- The pair-labelled actual corrected G10 atoms, with the literal difference carrier. -/
noncomputable def goldbachG10ActualAtoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  goldbachG10CorrectedAtoms (goldbachDifferenceCarrier N ε) N b c

theorem mem_goldbachG10ActualAtoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10ActualAtoms N ε b c ↔
      x.1 ∈ goldbachC10Pairs N b c ∧
        x.2 ∈ goldbachDifferenceCarrier N ε ∧
        literalHPoint (N * goldbachC10Prod x.1) (goldbachC10Prod x.1)
          (goldbachC10Cutoff N x.1) x.2 := by
  simpa [goldbachG10ActualAtoms] using
    (mem_goldbachG10CorrectedAtoms_iff
      (A := goldbachDifferenceCarrier N ε) (N := N) (b := b) (c := c) (x := x))

theorem mem_goldbachDifferenceCarrier_iff_exists
    {N : ℕ} {ε : ℝ} {n : ℕ} :
    n ∈ goldbachDifferenceCarrier N ε ↔
      ∃ p ∈ goldbachPrimeCarrier N ε, n = N - p := by
  classical
  rw [goldbachDifferenceCarrier, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem goldbachDifferenceCarrier_prime_data
    {N n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn : n ∈ goldbachDifferenceCarrier N ε) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) < (1 - ε) * N ∧ n = N - p := by
  rcases mem_goldbachDifferenceCarrier_iff_exists.mp hn with ⟨p, hp, rfl⟩
  rcases (mem_goldbachPrimeCarrier_iff (N := N) (p := p) (ε := ε) (le_of_lt hε)).mp hp with
    ⟨hpPrime, hpCut⟩
  exact ⟨p, hpPrime, hpCut, rfl⟩

theorem goldbachG10DifferenceCarrier_bounds
    {N n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn : n ∈ goldbachDifferenceCarrier N ε) :
    1 ≤ n ∧ n < N ∧ ε * N < (n : ℝ) := by
  rcases goldbachDifferenceCarrier_prime_data hε hn with ⟨p, hpPrime, hpCut, rfl⟩
  have hpNreal : (p : ℝ) < N := by
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have hpN : p < N := by exact_mod_cast hpNreal
  constructor
  · exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt hpN)
  constructor
  · exact Nat.sub_lt (lt_trans hpPrime.pos hpN) hpPrime.pos
  · rw [Nat.cast_sub hpN.le]
    nlinarith

/-- The strict actual bad atoms in the corrected G10 carrier. -/
noncomputable def goldbachG10BadActualAtoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachG10ActualAtoms N ε b c).filter fun x => ¬Nat.Coprime x.2 N

/-- The actual non-bad corrected G10 atoms. -/
noncomputable def goldbachG10NonbadActualAtoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachG10ActualAtoms N ε b c).filter fun x => Nat.Coprime x.2 N

/-- The corrected G10 atoms with an `r²`-exception removed from the actual carrier. -/
noncomputable def goldbachG10RSquareActualAtoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachG10NonbadActualAtoms N ε b c).filter fun x => x.1.1 ^ 2 ∣ x.2

/-- The actual corrected G10 atoms remaining after the `r²` split. -/
noncomputable def goldbachG10NoRSquareActualAtoms
    (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachG10NonbadActualAtoms N ε b c).filter fun x => ¬x.1.1 ^ 2 ∣ x.2

/-- The corrected G10 atoms with an `s²`-exception removed from the actual carrier. -/
noncomputable def goldbachG10SSquareActualAtoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachG10NoRSquareActualAtoms N ε b c).filter fun x => x.1.2 ^ 2 ∣ x.2

/-- The good actual corrected G10 atoms. -/
noncomputable def goldbachG10GoodActualAtoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachG10NoRSquareActualAtoms N ε b c).filter fun x => ¬x.1.2 ^ 2 ∣ x.2

theorem mem_goldbachG10BadActualAtoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10BadActualAtoms N ε b c ↔
      x ∈ goldbachG10ActualAtoms N ε b c ∧ ¬Nat.Coprime x.2 N := by
  simp [goldbachG10BadActualAtoms]

theorem mem_goldbachG10NonbadActualAtoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10NonbadActualAtoms N ε b c ↔
      x ∈ goldbachG10ActualAtoms N ε b c ∧ Nat.Coprime x.2 N := by
  simp [goldbachG10NonbadActualAtoms]

theorem mem_goldbachG10RSquareActualAtoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10RSquareActualAtoms N ε b c ↔
      x ∈ goldbachG10ActualAtoms N ε b c ∧
        Nat.Coprime x.2 N ∧ x.1.1 ^ 2 ∣ x.2 := by
  constructor <;> intro hx <;>
    simpa [goldbachG10RSquareActualAtoms, goldbachG10NonbadActualAtoms, and_assoc] using hx

theorem mem_goldbachG10NoRSquareActualAtoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10NoRSquareActualAtoms N ε b c ↔
      x ∈ goldbachG10ActualAtoms N ε b c ∧
        Nat.Coprime x.2 N ∧ ¬x.1.1 ^ 2 ∣ x.2 := by
  constructor <;> intro hx <;>
    simpa [goldbachG10NoRSquareActualAtoms, goldbachG10NonbadActualAtoms, and_assoc] using hx

theorem mem_goldbachG10SSquareActualAtoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10SSquareActualAtoms N ε b c ↔
      x ∈ goldbachG10ActualAtoms N ε b c ∧
        Nat.Coprime x.2 N ∧ ¬x.1.1 ^ 2 ∣ x.2 ∧ x.1.2 ^ 2 ∣ x.2 := by
  constructor <;> intro hx <;>
    simpa [goldbachG10SSquareActualAtoms, goldbachG10NoRSquareActualAtoms,
      goldbachG10NonbadActualAtoms, and_assoc] using hx

theorem mem_goldbachG10GoodActualAtoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachG10GoodActualAtoms N ε b c ↔
      x ∈ goldbachG10ActualAtoms N ε b c ∧
        Nat.Coprime x.2 N ∧ ¬x.1.1 ^ 2 ∣ x.2 ∧ ¬x.1.2 ^ 2 ∣ x.2 := by
  constructor <;> intro hx <;>
    simpa [goldbachG10GoodActualAtoms, goldbachG10NoRSquareActualAtoms,
      goldbachG10NonbadActualAtoms, and_assoc] using hx

/-- The actual cofactor attached to a corrected G10 atom. -/
def goldbachG10Cofactor (x : Σ _rs : ℕ × ℕ, ℕ) : ℕ :=
  x.2 / goldbachC10Prod x.1

theorem goldbachG10ActualAtom_eq_prod_mul_cofactor
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachG10ActualAtoms N ε b c) :
    x.2 = goldbachC10Prod x.1 * goldbachG10Cofactor x := by
  exact (Nat.mul_div_cancel' (mem_goldbachG10ActualAtoms_iff.mp hx).2.2.1).symm

private theorem fst_dvd_of_prod_dvd {a b n : ℕ} (h : a * b ∣ n) : a ∣ n :=
  dvd_trans (dvd_mul_of_dvd_left (dvd_refl a) b) h

private theorem snd_dvd_of_prod_dvd {a b n : ℕ} (h : a * b ∣ n) : b ∣ n :=
  dvd_trans (dvd_mul_of_dvd_right (dvd_refl b) a) h

theorem goldbachG10ActualAtom_fst_mem_largePrimeDivisors
    {N n : ℕ} {ε β γ : ℝ} (hε : 0 < ε) {rs : ℕ × ℕ}
    (hx : Sigma.mk rs n ∈ goldbachG10ActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    rs.1 ∈ largePrimeDivisors n ((N : ℝ) ^ β) := by
  rcases mem_goldbachG10ActualAtoms_iff.mp hx with ⟨hrsMem, hnA, hpoint⟩
  have hrs := mem_goldbachC10Pairs_iff.mp hrsMem
  have hdiv : rs.1 ∣ n := fst_dvd_of_prod_dvd hpoint.1
  have hn1 : 1 ≤ n := (goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := n) hε hnA).1
  have hn0 : n ≠ 0 := by omega
  simp [largePrimeDivisors, Nat.mem_primeFactors, hrs.1, hdiv, hn0, hrs.2.2.2.1]

theorem goldbachG10ActualAtom_snd_mem_largePrimeDivisors
    {N n : ℕ} {ε β γ : ℝ} (hε : 0 < ε) {rs : ℕ × ℕ}
    (hx : Sigma.mk rs n ∈ goldbachG10ActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    rs.2 ∈ largePrimeDivisors n ((N : ℝ) ^ β) := by
  rcases mem_goldbachG10ActualAtoms_iff.mp hx with ⟨hrsMem, hnA, hpoint⟩
  have hrs := mem_goldbachC10Pairs_iff.mp hrsMem
  have hdiv : rs.2 ∣ n := snd_dvd_of_prod_dvd hpoint.1
  have hn1 : 1 ≤ n := (goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := n) hε hnA).1
  have hn0 : n ≠ 0 := by omega
  have hβle : (N : ℝ) ^ β ≤ (rs.2 : ℝ) := by
    exact le_trans hrs.2.2.2.1 (le_trans hrs.2.2.2.2.1 hrs.2.2.2.2.2.1)
  simp [largePrimeDivisors, Nat.mem_primeFactors, hrs.2.1,
    hdiv, hn0, hβle]

/-- The strictly labelled prime source counted fibrewise over the corrected pair carrier. -/
def goldbachPi10Point (N : ℕ) (ε : ℝ) (rs : ℕ × ℕ) (q : ℕ) : Prop :=
  q.Prime ∧
    ε * (N : ℝ) / (goldbachC10Prod rs : ℝ) < (q : ℝ) ∧
    (q : ℝ) < (N : ℝ) / (goldbachC10Prod rs : ℝ) ∧
    (N - goldbachC10Prod rs * q).Prime

/-- The corrected Pi10 fibre above a fixed pair label. -/
noncomputable def goldbachPi10Fiber (N : ℕ) (ε : ℝ) (rs : ℕ × ℕ) : Finset ℕ :=
  (range (N + 1)).filter (goldbachPi10Point N ε rs)

/-- Pair-labelled corrected Pi10 atoms. -/
noncomputable def goldbachPi10Atoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachC10Pairs N b c).sigma (goldbachPi10Fiber N ε)

/-- The actual labelled prime source attached to the corrected pair carrier. -/
noncomputable def goldbachPi10 (N : ℕ) (ε b c : ℝ) : ℤ :=
  ∑ rs ∈ goldbachC10Pairs N b c, ((goldbachPi10Fiber N ε rs).card : ℤ)

theorem goldbachPi10_eq_card_atoms (N : ℕ) (ε b c : ℝ) :
    goldbachPi10 N ε b c = ((goldbachPi10Atoms N ε b c).card : ℤ) := by
  simp [goldbachPi10, goldbachPi10Atoms, goldbachPi10Fiber]

theorem mem_goldbachPi10Atoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachPi10Atoms N ε b c ↔
      x.1 ∈ goldbachC10Pairs N b c ∧
        x.2 ∈ range (N + 1) ∧ goldbachPi10Point N ε x.1 x.2 := by
  simp [goldbachPi10Atoms, goldbachPi10Fiber]

theorem goldbachG10GoodActualAtom_pair_ne
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachG10GoodActualAtoms N ε b c) :
    x.1.1 ≠ x.1.2 := by
  intro hEq
  have hdiv : x.1.1 ^ 2 ∣ x.2 := by
    rcases mem_goldbachG10GoodActualAtoms_iff.mp hx with ⟨hActual, _, _, _⟩
    have hprod : goldbachC10Prod x.1 ∣ x.2 := (mem_goldbachG10ActualAtoms_iff.mp hActual).2.2.1
    simpa [goldbachC10Prod, hEq, pow_two] using hprod
  exact (mem_goldbachG10GoodActualAtoms_iff.mp hx).2.2.1 hdiv

theorem goldbachG10Cofactor_coprime
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachG10GoodActualAtoms N ε b c) :
    Nat.Coprime (goldbachG10Cofactor x) (N * goldbachC10Prod x.1) := by
  apply Nat.coprime_of_dvd'
  intro p hpPrime hpq hpNm
  rcases mem_goldbachG10GoodActualAtoms_iff.mp hx with ⟨hActual, hcop, hnotr, hnots⟩
  have hPair := mem_goldbachC10Pairs_iff.mp (mem_goldbachG10ActualAtoms_iff.mp hActual).1
  have hxEq := goldbachG10ActualAtom_eq_prod_mul_cofactor (N := N) (ε := ε) (b := b) (c := c) hActual
  have hpn : p ∣ x.2 := by
    rw [hxEq]
    exact dvd_mul_of_dvd_right hpq (goldbachC10Prod x.1)
  have hpnotN : ¬p ∣ N := prime_not_dvd_of_coprime hcop hpPrime hpn
  have hpnotProd : ¬p ∣ goldbachC10Prod x.1 := by
    intro hpProd
    rcases hpPrime.dvd_mul.mp hpProd with hpr | hps
    · have hpeq : p = x.1.1 := by
        exact ((hPair.1.dvd_iff_eq hpPrime.ne_one).mp hpr).symm
      have hq' : x.1.1 ∣ goldbachG10Cofactor x := hpeq ▸ hpq
      have hr2 : x.1.1 ^ 2 ∣ x.2 := by
        rcases hq' with ⟨k, hk⟩
        rw [hxEq]
        refine ⟨x.1.2 * k, ?_⟩
        simp [goldbachC10Prod, hk, pow_two, mul_left_comm, mul_comm]
      exact hnotr hr2
    · have hpeq : p = x.1.2 := by
        exact ((hPair.2.1.dvd_iff_eq hpPrime.ne_one).mp hps).symm
      have hq' : x.1.2 ∣ goldbachG10Cofactor x := hpeq ▸ hpq
      have hs2 : x.1.2 ^ 2 ∣ x.2 := by
        rcases hq' with ⟨k, hk⟩
        rw [hxEq]
        refine ⟨x.1.1 * k, ?_⟩
        simp [goldbachC10Prod, hk, pow_two, mul_left_comm, mul_comm]
      exact hnots hs2
  rcases hpPrime.dvd_mul.mp hpNm with hpN | hpProd
  · exact (hpnotN hpN).elim
  · exact (hpnotProd hpProd).elim

theorem goldbachG10Cofactor_primeDivisor_ge_cutoff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} {p : ℕ}
    (hx : x ∈ goldbachG10GoodActualAtoms N ε b c)
    (hpPrime : p.Prime) (hpdvd : p ∣ goldbachG10Cofactor x) :
    goldbachC10Cutoff N x.1 ≤ (p : ℝ) := by
  rcases mem_goldbachG10GoodActualAtoms_iff.mp hx with ⟨hActual, _, _, _⟩
  have hxEq := goldbachG10ActualAtom_eq_prod_mul_cofactor (N := N) (ε := ε) (b := b) (c := c) hActual
  have hpn : p ∣ x.2 := by
    rw [hxEq]
    exact dvd_mul_of_dvd_right hpdvd (goldbachC10Prod x.1)
  have hpnot : ¬p ∣ N * goldbachC10Prod x.1 :=
    prime_not_dvd_of_coprime (goldbachG10Cofactor_coprime hx) hpPrime hpdvd
  exact (mem_goldbachG10ActualAtoms_iff.mp hActual).2.2.2 p hpPrime hpn hpnot

theorem goldbachG10Cofactor_prime_of_lt_sq
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachG10GoodActualAtoms N ε b c)
    (hq2 : 2 ≤ goldbachG10Cofactor x)
    (hSq :
      ((goldbachG10Cofactor x : ℕ) : ℝ) <
        goldbachC10Cutoff N x.1 ^ 2) :
    (goldbachG10Cofactor x).Prime := by
  by_contra hPrime
  have hminSq : (Nat.minFac (goldbachG10Cofactor x)) ^ 2 ≤ goldbachG10Cofactor x :=
    Nat.minFac_sq_le_self (Nat.pos_of_ne_zero (by omega)) hPrime
  have hfacPrime : (Nat.minFac (goldbachG10Cofactor x)).Prime :=
    Nat.minFac_prime (by omega)
  have hfacDvd : Nat.minFac (goldbachG10Cofactor x) ∣ goldbachG10Cofactor x :=
    Nat.minFac_dvd _
  have hceil :
      ⌈goldbachC10Cutoff N x.1⌉₊ ≤ Nat.minFac (goldbachG10Cofactor x) := by
    exact Nat.ceil_le.mpr (goldbachG10Cofactor_primeDivisor_ge_cutoff hx hfacPrime hfacDvd)
  have hceilSq :
      goldbachC10Cutoff N x.1 ^ 2 ≤ ((⌈goldbachC10Cutoff N x.1⌉₊ : ℕ) : ℝ) ^ 2 := by
    have hceilLe : goldbachC10Cutoff N x.1 ≤ (⌈goldbachC10Cutoff N x.1⌉₊ : ℝ) := Nat.le_ceil _
    have hnonneg : 0 ≤ goldbachC10Cutoff N x.1 := Real.sqrt_nonneg _
    gcongr
  have hNatLt :
      goldbachG10Cofactor x < (⌈goldbachC10Cutoff N x.1⌉₊ : ℕ) ^ 2 := by
    have hRealLt :
        (goldbachG10Cofactor x : ℝ) <
          (((⌈goldbachC10Cutoff N x.1⌉₊ : ℕ) ^ 2 : ℕ) : ℝ) := by
      calc
        (goldbachG10Cofactor x : ℝ) < goldbachC10Cutoff N x.1 ^ 2 := hSq
        _ ≤ ((⌈goldbachC10Cutoff N x.1⌉₊ : ℕ) : ℝ) ^ 2 := hceilSq
        _ = (((⌈goldbachC10Cutoff N x.1⌉₊ : ℕ) ^ 2 : ℕ) : ℝ) := by norm_num
    exact_mod_cast hRealLt
  have hle1 : (⌈goldbachC10Cutoff N x.1⌉₊ : ℕ) ^ 2 ≤ (Nat.minFac (goldbachG10Cofactor x)) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hceil hceil
  exact (not_lt_of_ge (le_trans hle1 hminSq)) hNatLt

private theorem one_sixth_lt_of_parameter_window
    {β γ : ℝ}
    (_hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ) :
    (1 : ℝ) / 6 < γ := by
  nlinarith

theorem goldbachG10Cofactor_prime
    {N : ℕ} {ε β γ : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hε : 0 < ε)
    (hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (hcut : 1 < ε * (N : ℝ) ^ ((1 : ℝ) / 6))
    (hx : x ∈ goldbachG10GoodActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    (goldbachG10Cofactor x).Prime := by
  rcases mem_goldbachG10GoodActualAtoms_iff.mp hx with ⟨hActual, _, _, _⟩
  rcases mem_goldbachG10ActualAtoms_iff.mp hActual with ⟨hrsMem, hnA, _⟩
  have hrs := mem_goldbachC10Pairs_iff.mp hrsMem
  have hxEq := goldbachG10ActualAtom_eq_prod_mul_cofactor
    (N := N) (ε := ε) (b := (N : ℝ) ^ β) (c := (N : ℝ) ^ γ) hActual
  have hbounds := goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := x.2) hε hnA
  have hmpos : 0 < goldbachC10Prod x.1 := by
    exact Nat.mul_pos hrs.1.pos hrs.2.1.pos
  have hmposReal : 0 < (goldbachC10Prod x.1 : ℝ) := by exact_mod_cast hmpos
  have hN1Nat : 1 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN1Nat
  have hsLower :
      (N : ℝ) ^ ((1 : ℝ) / 6) < (x.1.2 : ℝ) := by
    have hγ16 : (1 : ℝ) / 6 < γ := one_sixth_lt_of_parameter_window hβ hβγ hγ
    have hpow : (N : ℝ) ^ ((1 : ℝ) / 6) < (N : ℝ) ^ γ :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 hγ16
    exact lt_of_lt_of_le hpow hrs.2.2.2.2.2.1
  have hprodLe :
      ((x.1.2 : ℝ) * (goldbachC10Prod x.1 : ℝ)) ≤ N := by
    calc
      (x.1.2 : ℝ) * (goldbachC10Prod x.1 : ℝ)
          = ((x.1.1 * x.1.2 ^ 2 : ℕ) : ℝ) := by
              simp [goldbachC10Prod, pow_two, mul_left_comm]
      _ ≤ N := by exact_mod_cast hrs.2.2.2.2.2.2
  have hNdiv :
      (N : ℝ) ^ ((1 : ℝ) / 6) < (N : ℝ) / (goldbachC10Prod x.1 : ℝ) := by
    have hmul :
        (N : ℝ) ^ ((1 : ℝ) / 6) * (goldbachC10Prod x.1 : ℝ) <
          (x.1.2 : ℝ) * (goldbachC10Prod x.1 : ℝ) := by
      gcongr
    rw [lt_div_iff₀ hmposReal]
    exact lt_of_lt_of_le hmul hprodLe
  have hLowerReal :
      1 < ε * (N : ℝ) / (goldbachC10Prod x.1 : ℝ) := by
    have hmul : ε * (N : ℝ) ^ ((1 : ℝ) / 6) <
        ε * ((N : ℝ) / (goldbachC10Prod x.1 : ℝ)) := by
      gcongr
    have hmul' : ε * (N : ℝ) ^ ((1 : ℝ) / 6) <
        ε * (N : ℝ) / (goldbachC10Prod x.1 : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact lt_trans hcut hmul'
  have hqLower :
      ε * (N : ℝ) / (goldbachC10Prod x.1 : ℝ) < (goldbachG10Cofactor x : ℝ) := by
    have hxReal : (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ) = x.2 := by
      calc
        (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ)
            = ((goldbachC10Prod x.1 * goldbachG10Cofactor x : ℕ) : ℝ) := by
                simp [goldbachC10Prod, mul_assoc, mul_comm]
        _ = x.2 := by exact_mod_cast hxEq.symm
    have hxlt : ε * N < ((goldbachG10Cofactor x : ℕ) : ℝ) * (goldbachC10Prod x.1 : ℝ) := by
      simpa [hxReal] using hbounds.2.2
    rw [div_lt_iff₀ hmposReal]
    simpa [mul_comm, mul_assoc] using hxlt
  have hq2 : 2 ≤ goldbachG10Cofactor x := by
    have : (1 : ℝ) < (goldbachG10Cofactor x : ℝ) := lt_trans hLowerReal hqLower
    exact Nat.succ_le_of_lt (by exact_mod_cast this)
  have hqUpper :
      ((goldbachG10Cofactor x : ℕ) : ℝ) < (N : ℝ) / (goldbachC10Prod x.1 : ℝ) := by
    have hxReal : (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ) = x.2 := by
      calc
        (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ)
            = ((goldbachC10Prod x.1 * goldbachG10Cofactor x : ℕ) : ℝ) := by
                simp [goldbachC10Prod, mul_assoc, mul_comm]
        _ = x.2 := by exact_mod_cast hxEq.symm
    have hxlt : (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ) < N := by
      simpa [hxReal] using (show (x.2 : ℝ) < N by exact_mod_cast hbounds.2.1)
    rw [lt_div_iff₀ hmposReal]
    simpa [mul_comm, mul_assoc] using hxlt
  have hSq :
      ((goldbachG10Cofactor x : ℕ) : ℝ) <
        goldbachC10Cutoff N x.1 ^ 2 := by
    have hnonneg : 0 ≤ (N : ℝ) / (goldbachC10Prod x.1 : ℝ) := by positivity
    calc
      ((goldbachG10Cofactor x : ℕ) : ℝ) < (N : ℝ) / (goldbachC10Prod x.1 : ℝ) := hqUpper
      _ = goldbachC10Cutoff N x.1 ^ 2 := by
          unfold goldbachC10Cutoff
          rw [Real.sq_sqrt hnonneg]
  exact goldbachG10Cofactor_prime_of_lt_sq hx hq2 hSq

/-- The actual good corrected G10 atoms inject into the pair-labelled Pi10 source. -/
theorem goldbachG10GoodActualAtoms_card_le_goldbachPi10
    {N : ℕ} {ε β γ : ℝ}
    (hε : 0 < ε)
    (hβ : (1 : ℝ) / 18 < β)
    (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ)
    (hcut : 1 < ε * (N : ℝ) ^ ((1 : ℝ) / 6)) :
    ((goldbachG10GoodActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ) ≤
      goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) := by
  let f : (Σ _rs : ℕ × ℕ, ℕ) → (Σ _rs : ℕ × ℕ, ℕ) :=
    fun x => ⟨x.1, goldbachG10Cofactor x⟩
  have hmap :
      Set.MapsTo f
        (goldbachG10GoodActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ))
        (goldbachPi10Atoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) := by
    intro x hx
    rcases mem_goldbachG10GoodActualAtoms_iff.mp hx with ⟨hActual, _, _, _⟩
    rcases mem_goldbachG10ActualAtoms_iff.mp hActual with ⟨hrsMem, hnA, _⟩
    have hrs := mem_goldbachC10Pairs_iff.mp hrsMem
    have hqPrime := goldbachG10Cofactor_prime hε hβ hβγ hγ hcut hx
    have hxEq := goldbachG10ActualAtom_eq_prod_mul_cofactor
      (N := N) (ε := ε) (b := (N : ℝ) ^ β) (c := (N : ℝ) ^ γ) hActual
    have hbounds := goldbachG10DifferenceCarrier_bounds (N := N) (ε := ε) (n := x.2) hε hnA
    have hmpos : 0 < goldbachC10Prod x.1 := by
      exact Nat.mul_pos hrs.1.pos hrs.2.1.pos
    have hmposReal : 0 < (goldbachC10Prod x.1 : ℝ) := by exact_mod_cast hmpos
    have hqRange :
        goldbachG10Cofactor x ∈ range (N + 1) := by
      refine Finset.mem_range.mpr (Nat.lt_succ_of_lt ?_)
      exact lt_of_le_of_lt (Nat.div_le_self x.2 (goldbachC10Prod x.1)) hbounds.2.1
    have hqLower :
        ε * (N : ℝ) / (goldbachC10Prod x.1 : ℝ) < (goldbachG10Cofactor x : ℝ) := by
      have hxReal : (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ) = x.2 := by
        calc
          (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ)
              = ((goldbachC10Prod x.1 * goldbachG10Cofactor x : ℕ) : ℝ) := by
                  simp [goldbachC10Prod, mul_assoc, mul_comm]
          _ = x.2 := by exact_mod_cast hxEq.symm
      have hxlt : ε * N < ((goldbachG10Cofactor x : ℕ) : ℝ) * (goldbachC10Prod x.1 : ℝ) := by
        simpa [hxReal] using hbounds.2.2
      rw [div_lt_iff₀ hmposReal]
      simpa [mul_comm, mul_assoc] using hxlt
    have hqUpper :
        ((goldbachG10Cofactor x : ℕ) : ℝ) < (N : ℝ) / (goldbachC10Prod x.1 : ℝ) := by
      have hxReal : (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ) = x.2 := by
        calc
          (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ)
              = ((goldbachC10Prod x.1 * goldbachG10Cofactor x : ℕ) : ℝ) := by
                  simp [goldbachC10Prod, mul_assoc, mul_comm]
          _ = x.2 := by exact_mod_cast hxEq.symm
      have hxlt : (goldbachG10Cofactor x : ℝ) * (goldbachC10Prod x.1 : ℝ) < N := by
        simpa [hxReal] using (show (x.2 : ℝ) < N by exact_mod_cast hbounds.2.1)
      rw [lt_div_iff₀ hmposReal]
      simpa [mul_comm, mul_assoc] using hxlt
    rcases goldbachDifferenceCarrier_prime_data (N := N) (n := x.2) (ε := ε) hε hnA with
      ⟨p, hpPrime, _, hpEq⟩
    have hpOut : (N - goldbachC10Prod x.1 * goldbachG10Cofactor x).Prime := by
      have hEqOut : N - goldbachC10Prod x.1 * goldbachG10Cofactor x = p := by
        rw [← hxEq, hpEq, Nat.sub_eq_iff_eq_add (Nat.sub_le N p)]
        omega
      simpa [hEqOut] using hpPrime
    exact mem_goldbachPi10Atoms_iff.mpr
      ⟨hrsMem, hqRange, hqPrime, hqLower, hqUpper, hpOut⟩
  have hinj :
      Set.InjOn f (goldbachG10GoodActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) := by
    intro x hx y hy hxy
    have hxEq := goldbachG10ActualAtom_eq_prod_mul_cofactor
      (N := N) (ε := ε) (b := (N : ℝ) ^ β) (c := (N : ℝ) ^ γ)
      ((mem_goldbachG10GoodActualAtoms_iff.mp hx).1)
    have hyEq := goldbachG10ActualAtom_eq_prod_mul_cofactor
      (N := N) (ε := ε) (b := (N : ℝ) ^ β) (c := (N : ℝ) ^ γ)
      ((mem_goldbachG10GoodActualAtoms_iff.mp hy).1)
    have h1 : x.1 = y.1 := by simpa [f] using congrArg Sigma.fst hxy
    have h2 : goldbachG10Cofactor x = goldbachG10Cofactor y := by
      have := congrArg Sigma.snd hxy
      simpa [f] using this
    cases x with
    | mk rsx nx =>
      cases y with
      | mk rsy ny =>
        simp at h1 h2 ⊢
        subst h1
        have hEqxy : nx = ny := by
          calc
            nx = goldbachC10Prod rsx * goldbachG10Cofactor ⟨rsx, nx⟩ := by simpa using hxEq
            _ = goldbachC10Prod rsx * goldbachG10Cofactor ⟨rsx, ny⟩ := by simp [h2]
            _ = ny := by simpa using hyEq.symm
        exact ⟨rfl, hEqxy⟩
  calc
    ((goldbachG10GoodActualAtoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ)
        ≤ ((goldbachPi10Atoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).card : ℤ) := by
            exact_mod_cast Finset.card_le_card_of_injOn f hmap hinj
    _ = goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) :=
      (goldbachPi10_eq_card_atoms N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)).symm

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig