import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherBandFormulas
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherBandLabels

/-! # Arbitrary-length ordered labels and the complete Gamma source dictionary -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

noncomputable def secondFunctionalMotherColour (b c e : ℝ) (p : ℕ) : ℕ :=
  if (p : ℝ) < b then 0 else if (p : ℝ) < c then 1
  else if (p : ℝ) < e then 2 else 3

theorem secondFunctionalMother_colour_monotone (b c e : ℝ) :
    Monotone (secondFunctionalMotherColour b c e) := by
  intro p q hpq
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  unfold secondFunctionalMotherColour
  split_ifs <;> first | omega | linarith

theorem secondFunctionalMother_colour_le_three (b c e : ℝ) (p : ℕ) :
    secondFunctionalMotherColour b c e p ≤ 3 := by
  unfold secondFunctionalMotherColour
  split_ifs <;> omega

/-- Every strict ordered tuple, without a maximum length. -/
noncomputable def secondFunctionalMotherTuples (P : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | r+1 => P.biUnion fun p =>
      (secondFunctionalMotherTuples (P.filter fun q => p < q) r).image (List.cons p)

theorem secondFunctionalMother_tuple_mem (P : Finset ℕ) (r : ℕ) (l : List ℕ) :
    l ∈ secondFunctionalMotherTuples P r ↔
      l.length = r ∧ l.Pairwise (· < ·) ∧ ∀ p ∈ l, p ∈ P := by
  induction r generalizing P l with
  | zero => cases l <;> simp [secondFunctionalMotherTuples]
  | succ r ih =>
      cases l with
      | nil => simp [secondFunctionalMotherTuples]
      | cons p l =>
          simp only [secondFunctionalMotherTuples, mem_biUnion, mem_image,
            List.cons.injEq, existsAndEq, ih, List.length_cons,
            Nat.add_right_cancel_iff, List.pairwise_cons, List.mem_cons,
            forall_eq_or_imp, mem_filter, forall_and]
          tauto

/-- The original cutoff and the product of the first r-2 labels are both retained. -/
noncomputable abbrev secondFunctionalMotherPrefixCarrier := fourthRowMotherPrefixCarrier

noncomputable def secondFunctionalMotherPrefixTerm (N d M : ℕ)
    (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs then
      ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ) else 0

noncomputable def secondFunctionalMotherGamma (N d M : ℕ) (a b c e f : ℝ) : ℕ → ℝ
  | 1 => 4 * (sourceSieveCount N d (d*N) a : ℝ) +
      (sourceSieveCount N d (d*N) b : ℝ)
  | 2 => fourthRowMotherSingle N d M a f
  | 3 => fourthRowMotherSingle N d M a c
  | 4 => fourthRowMotherSingle N d M a e
  | 5 => fourthRowMotherPair N d M a c a c
  | 6 => fourthRowMotherPair N d M a b c e
  | i => ((secondFunctionalMotherGammaWords i).map
      (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum

noncomputable def secondFunctionalMotherLocal (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  secondFunctionalMotherGamma N d M a b c e f 1 -
    secondFunctionalMotherGamma N d M a b c e f 2 -
    secondFunctionalMotherGamma N d M a b c e f 3 -
    secondFunctionalMotherGamma N d M a b c e f 4 +
    ∑ i ∈ Finset.Icc 5 21, secondFunctionalMotherGamma N d M a b c e f i

theorem secondFunctionalMother_prefix_arity_five (N d : ℕ) (p q r s t : ℕ) :
    secondFunctionalMotherPrefixCarrier N d [p,q,r,s,t] =
      sourceSieveCarrier N (d*(p*q*r*s*t)) (d*(p*q*r)*N) s := by
  simp [fourthRowMotherPrefixCarrier, mul_assoc]

theorem secondFunctionalMother_prefix_arity_six (N d : ℕ) (p q r s t u : ℕ) :
    secondFunctionalMotherPrefixCarrier N d [p,q,r,s,t,u] =
      sourceSieveCarrier N (d*(p*q*r*s*t*u)) (d*(p*q*r*s)*N) t := by
  simp [fourthRowMotherPrefixCarrier, mul_assoc]

end Wu2008DoubleSieve
