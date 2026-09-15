import MathlibNt.SieveTheory.LiLiuGoldbachS4SwitchedCarrier
import MathlibNt.SieveTheory.LiuLogarithmicIntegral

open scoped BigOperators
open Finset
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB8FibreSieve (P : Prop) : Decidable P :=
  Classical.propDecidable P

noncomputable def goldbachB8PlusSupport (N : ℕ) : Finset ℕ :=
  (goldbachB8PlusAtoms N).image (goldbachB8PlusOutput N)

/-- Every output carries its full labelled fibre, not unit weight. -/
noncomputable def goldbachB8PlusWeight (N p : ℕ) : ℝ :=
  (goldbachB8PlusOutputFiber N p).card

noncomputable def goldbachB8PlusDivCount (N d : ℕ) : ℕ :=
  ((goldbachB8PlusAtoms N).filter fun x => d ∣ goldbachB8PlusOutput N x).card

noncomputable def goldbachB8PlusMainMass (N : ℕ) : ℝ :=
  ∑ m ∈ goldbachC8ProductSupport N,
    liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / m)

theorem goldbachC8ProductSupport_one_lt_and_coprime {N m : ℕ}
    (hm : m ∈ goldbachC8ProductSupport N) : 1 < m ∧ Nat.Coprime m N := by
  obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp hm
  have h := mem_goldbachS4Pairs_iff.mp hrs
  refine ⟨?_, h.2.2.1⟩
  have hfour := Nat.mul_le_mul h.1.two_le h.2.1.two_le
  change 1 < rs.1 * rs.2
  omega

theorem goldbachC8ProductSupport_two_le_quotient {N m : ℕ}
    (hm : m ∈ goldbachC8ProductSupport N) : (2 : ℝ) ≤ (N : ℝ) / m := by
  obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp hm
  have h := mem_goldbachS4Pairs_iff.mp hrs
  have hmpos : (0 : ℝ) < goldbachC8Prod rs := by
    exact_mod_cast goldbachC8Prod_pos hrs
  rw [le_div_iff₀ hmpos]
  have hmul : 2 * goldbachC8Prod rs ≤ N := by
    calc
      2 * goldbachC8Prod rs ≤ rs.2 * goldbachC8Prod rs :=
        Nat.mul_le_mul_right _ h.2.1.two_le
      _ = rs.1 * rs.2 ^ 2 := by unfold goldbachC8Prod; ring
      _ ≤ N := h.2.2.2.2.2
  exact_mod_cast hmul

theorem goldbachB8PlusMainMass_nonneg (N : ℕ) :
    0 ≤ goldbachB8PlusMainMass N := by
  apply Finset.sum_nonneg
  intro m hm
  exact liuLogarithmicIntegral_nonneg _ (by positivity)
    (goldbachC8ProductSupport_two_le_quotient hm)

private theorem B8FibreSieve_pushforward_sum
    {α : Type*} [DecidableEq α] (A : Finset α) (out : α → ℕ)
    (P : ℕ → Prop) [DecidablePred P] :
    ∑ n ∈ (A.image out).filter P, ((A.filter fun x => out x = n).card : ℝ) =
      ((A.filter fun x => P (out x)).card : ℝ) := by
  have h := Finset.sum_fiberwise_eq_sum_filter A ((A.image out).filter P) out
    (fun _ => (1 : ℝ))
  have heq : A.filter (fun x => out x ∈ (A.image out).filter P) =
      A.filter (fun x => P (out x)) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, Finset.mem_image.mpr ⟨x, hx.1, rfl⟩, hx.2⟩
  rw [heq] at h
  simpa using h

theorem goldbachB8PlusWeight_sum_eq_card_atoms (N : ℕ) :
    ∑ p ∈ goldbachB8PlusSupport N, goldbachB8PlusWeight N p =
      ((goldbachB8PlusAtoms N).card : ℝ) := by
  simpa [goldbachB8PlusSupport, goldbachB8PlusWeight, goldbachB8PlusOutputFiber] using
    B8FibreSieve_pushforward_sum (goldbachB8PlusAtoms N) (goldbachB8PlusOutput N)
      (fun _ => True)

/-- Reciprocal totient on all moduli; it agrees with `goldbachNu` on squarefree moduli. -/
noncomputable def goldbachB8PlusNu : ArithmeticFunction ℝ :=
  ⟨fun d => 1 / (Nat.totient d : ℝ), by simp⟩

theorem goldbachB8PlusNu_isMultiplicative : goldbachB8PlusNu.IsMultiplicative := by
  refine ⟨by simp [goldbachB8PlusNu], ?_⟩
  intro m n hmn
  change 1 / (Nat.totient (m * n) : ℝ) =
    (1 / (Nat.totient m : ℝ)) * (1 / (Nat.totient n : ℝ))
  rw [Nat.totient_mul hmn, Nat.cast_mul]
  simp [one_div, mul_comm]

theorem goldbachB8PlusNu_eq_goldbachNu_of_squarefree {d : ℕ} (hd : Squarefree d) :
    goldbachB8PlusNu d = goldbachNu d :=
  (goldbachNu_squarefree_eq_inv_totient hd).symm

noncomputable def goldbachB8PlusBoundingSieve
    (N : ℕ) (hEven : Even N) (Z : ℝ) : BoundingSieve where
  support := goldbachB8PlusSupport N
  weights := goldbachB8PlusWeight N
  weights_nonneg := fun _ => Nat.cast_nonneg _
  prodPrimes := goldbachB10ProdPrimes N Z
  prodPrimes_squarefree := goldbachB10ProdPrimes_squarefree N Z
  totalMass := goldbachB8PlusMainMass N
  nu := goldbachB8PlusNu
  nu_mult := goldbachB8PlusNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _
    rw [goldbachB8PlusNu_eq_goldbachNu_of_squarefree hp.squarefree]
    exact goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hpP
    have hpN := ((prime_dvd_goldbachB10ProdPrimes_iff hp).mp hpP).2
    have hpne : p ≠ 2 := by
      intro heq
      exact hpN (heq ▸ even_iff_two_dvd.mp hEven)
    rw [goldbachB8PlusNu_eq_goldbachNu_of_squarefree hp.squarefree]
    exact goldbachNu_lt_one_of_prime hp (lt_of_le_of_ne hp.two_le (Ne.symm hpne))

theorem goldbachB8PlusBoundingSieve_multSum_eq_divCount
    (N : ℕ) (hEven : Even N) (Z : ℝ) (d : ℕ) :
    (goldbachB8PlusBoundingSieve N hEven Z).multSum d =
      (goldbachB8PlusDivCount N d : ℝ) := by
  simpa [goldbachB8PlusBoundingSieve, BoundingSieve.multSum, goldbachB8PlusSupport,
    goldbachB8PlusWeight, goldbachB8PlusOutputFiber, goldbachB8PlusDivCount,
    Finset.sum_filter] using
    B8FibreSieve_pushforward_sum (goldbachB8PlusAtoms N) (goldbachB8PlusOutput N)
      (fun p => d ∣ p)

theorem goldbachB8PlusBoundingSieve_siftedSum_eq_card
    (N : ℕ) (hEven : Even N) (Z : ℝ) :
    (goldbachB8PlusBoundingSieve N hEven Z).siftedSum =
      ((goldbachB8PlusSiftedAtoms N Z).card : ℝ) := by
  rw [goldbachB8PlusSiftedAtoms_eq_coprime_filter]
  calc
    _ = ∑ p ∈ ((goldbachB8PlusAtoms N).image (goldbachB8PlusOutput N)).filter
        (fun p => Nat.Coprime (goldbachB10ProdPrimes N Z) p),
        (((goldbachB8PlusAtoms N).filter fun x => goldbachB8PlusOutput N x = p).card : ℝ) := by
      rw [goldbachB8PlusBoundingSieve, BoundingSieve.siftedSum, ← Finset.sum_filter]
      rfl
    _ = _ := B8FibreSieve_pushforward_sum (goldbachB8PlusAtoms N) (goldbachB8PlusOutput N)
      (fun p => Nat.Coprime (goldbachB10ProdPrimes N Z) p)

theorem goldbachB8PlusBoundingSieve_nu_eq_inv_totient
    (N : ℕ) (hEven : Even N) (Z : ℝ) (d : ℕ) :
    (goldbachB8PlusBoundingSieve N hEven Z).nu d = 1 / (Nat.totient d : ℝ) := rfl

theorem goldbachB8PlusBoundingSieve_rem_eq_divCount_sub
    (N : ℕ) (hEven : Even N) (Z : ℝ) (d : ℕ) :
    (goldbachB8PlusBoundingSieve N hEven Z).rem d =
      (goldbachB8PlusDivCount N d : ℝ) - goldbachB8PlusMainMass N / Nat.totient d := by
  rw [BoundingSieve.rem, goldbachB8PlusBoundingSieve_multSum_eq_divCount,
    goldbachB8PlusBoundingSieve_nu_eq_inv_totient]
  change _ - _ * goldbachB8PlusMainMass N = _
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig