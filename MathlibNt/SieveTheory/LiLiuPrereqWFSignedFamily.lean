import MathlibNt.SieveTheory.LiLiuPrereqWFBoxCoefficients
import MathlibNt.SieveTheory.LiLiuPrereqWFBoxProfiles

/-!
# A fixed occurrence-aware normalized signed geometric family

The index set is an image of a powerset, so one multiplicity profile occurs
once, regardless of how many prime subsets realize it. Each member is one
full-integer divided-power box product with the actual small Rosser weight.
The family, the sign, and the small weight are fixed before every level split.

The favourable signs use lower endpoints; the opposite signs require distinct
boxes and the strict upper-endpoint tests. This is the normalized convention
of `SignedRounding`, not Iwaniec's factorial-copy labelled-slot sum.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction LiLiuPrereqWFAdmissibility
open scoped Classical

/-- Upper/even and lower/odd are the loose lower-endpoint sides. -/
def LooseSign (upper : Bool) (r : ℕ) : Prop :=
  if upper then Even r else ¬ Even r

/-- Exact lower-endpoint source admissibility, with the redundant product
cutoff retained explicitly. The other sign uses strict upper-endpoint tests. -/
def SignedTagAccepted (upper : Bool) (b c : ℕ → ℝ) (D : ℝ) (t : List ℕ) : Prop :=
  Admissible upper b D t ∧
    if LooseSign upper t.length then (t.map b).prod < D
    else t.Nodup ∧ (t.map c).prod < D ∧ CubicPrefixBound upper c D t

noncomputable def signedTags (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) : Finset (List ℕ) :=
  (((P \ geometricSmallPrimes P D ε).powerset).image (boxProfile label)).filter
    (SignedTagAccepted upper (geometricLower D ε (ε ^ 9))
      (fun j => geometricLower D ε (ε ^ 9) (j + 1)) D)

/-- The actual small Rosser choice in (25)--(26): loose signs use the upper
small weight and tight signs use the lower small weight. -/
noncomputable def signedSmallWeight (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (r : ℕ) : ArithmeticFunction ℝ :=
  if LooseSign upper r then SmallRosser.upperSmallWeight P D ε
  else SmallRosser.lowerSmallWeight P D ε

noncomputable def signedFamilyTerm (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (t : List ℕ) : ArithmeticFunction ℝ :=
  (-1 : ℝ) ^ t.length •
    geometricBoxTerm P D ε (ε ^ 9) t (signedSmallWeight upper P D ε t.length)

noncomputable def signedFamilyAggregate (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) : ArithmeticFunction ℝ :=
  ∑ t ∈ signedTags upper P D ε label, signedFamilyTerm upper P D ε t

theorem signedFamilyAggregate_apply (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) (n : ℕ) :
    signedFamilyAggregate upper P D ε label n =
      ∑ t ∈ signedTags upper P D ε label, signedFamilyTerm upper P D ε t n := by
  unfold signedFamilyAggregate
  generalize signedTags upper P D ε label = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih => simp [Finset.sum_insert ht, ih, ArithmeticFunction.add_apply]

theorem wellFactorable_smul_of_abs_le_one {f : ArithmeticFunction ℝ} {Q r : ℝ}
    (hf : WellFactorable f Q) (hr : |r| ≤ 1) :
    WellFactorable (r • f) Q := by
  have hbound : ∀ g : ArithmeticFunction ℝ, BoundedOne g → BoundedOne (r • g) := by
    intro g hg n
    simpa only [smul_map, smul_eq_mul, abs_mul, one_mul] using
      mul_le_mul hr (hg n) (abs_nonneg _) zero_le_one
  refine ⟨hf.1, hbound f hf.2.1, supportedAt_smul _ hf.2.2.1, ?_⟩
  intro Q₁ Q₂ hQ₁ hQ₂ hsplit
  obtain ⟨a, b, ha, hsa, hb, hsb, heq⟩ := hf.2.2.2 Q₁ Q₂ hQ₁ hQ₂ hsplit
  exact ⟨r • a, b, hbound a ha, supportedAt_smul _ hsa, hb, hsb,
    by rw [heq, smul_mul_assoc]⟩

theorem signedSmallWeight_primeSupported (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (r : ℕ) :
    PrimeSupported (geometricSmallPrimes P D ε) (signedSmallWeight upper P D ε r) := by
  unfold signedSmallWeight
  split
  · exact SmallRosser.upperSmallWeight_primeSupported P D ε
  · exact SmallRosser.lowerSmallWeight_primeSupported P D ε

theorem signedFamilyTerm_primeSupported (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (t : List ℕ) :
    PrimeSupported P (signedFamilyTerm upper P D ε t) := by
  apply primeSupported_smul
  apply primeSupported_mono
    (primeSupported_mul (signedSmallWeight_primeSupported upper P D ε t.length)
      (boxProduct_primeSupported t.toFinset (geometricPrimeBox P D ε (ε ^ 9)) t.count))
  intro p hp
  rcases Finset.mem_union.mp hp with hs | hb
  · exact (Finset.mem_filter.mp hs).1
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hb
    exact ((mem_geometricPrimeBox _ _ _ _ _ _).mp hj).1

theorem signedFamilyAggregate_eq_zero_of_not_subset (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (label : ℕ → ℕ) {n : ℕ} (hsub : ¬ n.primeFactors ⊆ P) :
    signedFamilyAggregate upper P D ε label n = 0 := by
  rw [signedFamilyAggregate_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_contra h
  exact hsub (signedFamilyTerm_primeSupported upper P D ε t n h)

/-- One concrete signed term, on all integers, works for every real split of
the same enlarged level. There is no supplied coefficient or factorization. -/
theorem signedFamilyTerm_wellFactorable (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (t : List ℕ) (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hadm : Admissible upper (geometricLower D ε (ε ^ 9)) D t) :
    WellFactorable (signedFamilyTerm upper P D ε t) (D ^ (1 + ε + ε ^ 9)) := by
  apply wellFactorable_smul_of_abs_le_one
  · unfold signedSmallWeight
    split
    · exact SmallRosser.iwaniec_upperBoxTerm_wellFactorable P t hD hε hεsmall hadm
    · exact SmallRosser.iwaniec_lowerBoxTerm_wellFactorable P t hD hε hεsmall hadm
  · simp

/-- Finite family membership is decided numerically before all splits.
Duplicate prime realizations do not add additional family members. -/
theorem signedTags_common_wellFactorable (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    ∀ t ∈ signedTags upper P D ε label,
      WellFactorable (signedFamilyTerm upper P D ε t) (D ^ (1 + ε + ε ^ 9)) := by
  intro t ht
  exact signedFamilyTerm_wellFactorable upper P t hD hε hεsmall
    (Finset.mem_filter.mp ht).2.1

theorem signedFamilyTerm_squarefree (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (t : List ℕ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    {n : ℕ} (hn : Squarefree n) :
    signedFamilyTerm upper P D ε t n =
      if n.primeFactors ⊆ geometricSmallPrimes P D ε ∪
          t.toFinset.biUnion (geometricPrimeBox P D ε (ε ^ 9)) ∧
        (∀ j ∈ t.toFinset,
          (n.primeFactors ∩ geometricPrimeBox P D ε (ε ^ 9) j).card = t.count j)
      then (-1 : ℝ) ^ t.length *
        signedSmallWeight upper P D ε t.length
          ((n.primeFactors ∩ geometricSmallPrimes P D ε).prod id)
      else 0 := by
  rw [signedFamilyTerm, smul_map, smul_eq_mul, geometricBoxTerm,
    smallWeight_boxProduct_squarefree_eq_indicator t.toFinset
      (geometricPrimeBox P D ε (ε ^ 9)) t.count
      (fun _ _ _ _ hij => geometricPrimeBox_disjoint P hD (pow_nonneg hε _) hij)
      (geometricSmallPrimes P D ε) (signedSmallWeight upper P D ε t.length)
      (geometricSmallPrimes_disjoint P hD (pow_nonneg hε _) _)
      (signedSmallWeight_primeSupported upper P D ε t.length) hn]
  split_ifs <;> simp

theorem geometricLower_strictMono {D ε θ : ℝ}
    (hD : 1 < D) (hε : 0 < ε) (hθ : 0 < θ) :
    StrictMono (geometricLower D ε θ) := by
  intro i j hij
  apply Real.rpow_lt_rpow_of_exponent_lt hD
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by linarith) hij) (sq_pos_of_pos hε)

/-- Actual membership in half-open geometric boxes forces the label order.
No monotonicity of a supplied labelling is an additional assumption. -/
theorem geometric_boxLabel_monotoneOn (P S : Finset ℕ) {D ε θ : ℝ}
    (label : ℕ → ℕ) (hD : 1 ≤ D) (hθ : 0 ≤ θ)
    (hlabel : ∀ p ∈ S, p ∈ geometricPrimeBox P D ε θ (label p)) :
    ∀ p ∈ S, ∀ q ∈ S, p ≤ q → label p ≤ label q := by
  intro p hp q hq hpq
  by_contra h
  have hqp : label q + 1 ≤ label p := by omega
  have hlo := ((mem_geometricPrimeBox _ _ _ _ _ _).mp (hlabel p hp)).2.2.1
  have hhi := ((mem_geometricPrimeBox _ _ _ _ _ _).mp (hlabel q hq)).2.2.2
  have hm := geometricLower_monotone (ε := ε) hD hθ hqp
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  linarith

/-- Numerical identification of the source tag tests with the concrete
normalized set convention, retaining the source head restriction. -/
theorem signedTagAccepted_boxProfile_iff (upper : Bool) (label : ℕ → ℕ)
    (b c : ℕ → ℝ) (D : ℝ) (S : Finset ℕ)
    (hmono : ∀ p ∈ S, ∀ q ∈ S, p ≤ q → label p ≤ label q)
    (hbmono : Monotone b) (hbinj : Function.Injective b)
    (hone : ∀ p ∈ S, 1 ≤ b (label p))
    (hhead : ∀ p ∈ S, b (label p) ^ 2 < D)
    (hbc : ∀ p ∈ S, b (label p) ≤ c (label p)) :
    SignedTagAccepted upper b c D (boxProfile label S) ↔
      if LooseSign upper S.card then RoundedSupport upper (fun p => b (label p)) D S
      else TightRoundedSupport upper (fun p => b (label p)) (fun p => c (label p)) D S := by
  have hbase : Admissible upper b D (boxProfile label S) ↔
      RoundedSetAdmissible upper (fun p => b (label p)) D S := by
    rw [boxProfile_eq_map_sort label S hmono, admissible_map_iff]
    exact (roundedSetAdmissible_iff_admissible hone
      (fun p hp q hq hpq => hbmono (hmono p hp q hq hpq)) hhead).symm
  have hnodup : (boxProfile label S).Nodup ↔
      Set.InjOn (fun p => b (label p)) (↑S : Set ℕ) := by
    rw [boxProfile_nodup_iff]
    constructor
    · intro h p hp q hq heq
      exact h hp hq (hbinj heq)
    · intro h p hp q hq heq
      exact h hp hq (congrArg b heq)
  rw [SignedTagAccepted, boxProfile_length, hbase]
  by_cases hloose : LooseSign upper S.card
  · rw [if_pos hloose, if_pos hloose, boxProfile_prod, RoundedSupport]
    exact and_comm
  · rw [if_neg hloose, if_neg hloose, hnodup, TightRoundedSupport,
      ← roundedSupport_boxProfile_iff upper label c D S hmono]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨(roundedSupport_mono (fun p hp => (by norm_num : (0 : ℝ) ≤ 1).trans
        (hone p hp)) hbc h.2).2, h⟩

noncomputable def normalizedSignedSet (upper : Bool) (b c : ℕ → ℝ)
    (D : ℝ) (S : Finset ℕ) : ℝ :=
  if upper then normalizedUpperSet b c D S else normalizedLowerSet b c D S

theorem normalizedSignedSet_eq_profile_indicator (upper : Bool) (label : ℕ → ℕ)
    (b c : ℕ → ℝ) (D : ℝ) (S : Finset ℕ)
    (hmono : ∀ p ∈ S, ∀ q ∈ S, p ≤ q → label p ≤ label q)
    (hbmono : Monotone b) (hbinj : Function.Injective b)
    (hone : ∀ p ∈ S, 1 ≤ b (label p))
    (hhead : ∀ p ∈ S, b (label p) ^ 2 < D)
    (hbc : ∀ p ∈ S, b (label p) ≤ c (label p)) :
    normalizedSignedSet upper (fun p => b (label p)) (fun p => c (label p)) D S =
      if SignedTagAccepted upper b c D (boxProfile label S)
      then (-1 : ℝ) ^ S.card else 0 := by
  rw [signedTagAccepted_boxProfile_iff upper label b c D S hmono hbmono hbinj
    hone hhead hbc]
  cases upper <;> by_cases heven : Even S.card <;>
    simp [normalizedSignedSet, normalizedUpperSet, normalizedLowerSet, LooseSign,
      heven, neg_one_pow_eq_ite]

/-- The aggregate has exactly one possible squarefree contribution: the
canonical large-prime profile. This proves the absence of factorial copies. -/
theorem signedFamilyAggregate_squarefree_profile (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    {n : ℕ} (hn : Squarefree n) (hsub : n.primeFactors ⊆ P) :
    signedFamilyAggregate upper P D ε label n =
      if SignedTagAccepted upper (geometricLower D ε (ε ^ 9))
          (fun j => geometricLower D ε (ε ^ 9) (j + 1)) D
          (boxProfile label (n.primeFactors \ geometricSmallPrimes P D ε))
      then (-1 : ℝ) ^ (n.primeFactors \ geometricSmallPrimes P D ε).card *
        signedSmallWeight upper P D ε (n.primeFactors \ geometricSmallPrimes P D ε).card
          ((n.primeFactors ∩ geometricSmallPrimes P D ε).prod id)
      else 0 := by
  let S := n.primeFactors \ geometricSmallPrimes P D ε
  let t₀ := boxProfile label S
  let v := (-1 : ℝ) ^ S.card * signedSmallWeight upper P D ε S.card
    ((n.primeFactors ∩ geometricSmallPrimes P D ε).prod id)
  have hS : S ⊆ P \ geometricSmallPrimes P D ε := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hp).1,
      (Finset.mem_sdiff.mp hp).2⟩
  have hterm : ∀ t ∈ signedTags upper P D ε label,
      signedFamilyTerm upper P D ε t n = if t = t₀ then v else 0 := by
    intro t ht
    have htimage := (Finset.mem_filter.mp ht).1
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp htimage
    rw [signedFamilyTerm_squarefree upper P _ hD hε hn]
    simp only [boxProfile_matches_iff label (geometricPrimeBox P D ε (ε ^ 9))
        (geometricSmallPrimes P D ε) n.primeFactors _ (boxProfile_pairwise _ _)
        (fun _ _ hij => geometricPrimeBox_disjoint P hD (pow_nonneg hε _) hij)
        (fun j => by
          simpa using (geometricSmallPrimes_disjoint (ε := ε) P hD
            (pow_nonneg hε 9) {j}))
        (fun p hp => hlabel p (hS hp))]
    change (if boxProfile label T = t₀ then _ else 0) =
      if boxProfile label T = t₀ then v else 0
    split_ifs with heq
    · rw [heq]
      simp only [t₀, boxProfile_length, v]
    · rfl
  rw [signedFamilyAggregate_apply, Finset.sum_congr rfl hterm]
  have ht₀ : t₀ ∈ ((P \ geometricSmallPrimes P D ε).powerset.image (boxProfile label)) :=
    Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hS, rfl⟩
  simp only [Finset.sum_ite_eq', signedTags, Finset.mem_filter, ht₀, true_and]
  rfl

/-- Identification with the SAME normalized upper/lower set coefficients.
The factors are the actual small Rosser weights selected in (25)--(26).
Only the geometric labelling and the source head bound are numerical inputs. -/
theorem signedFamilyAggregate_squarefree_normalized (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D)
    {n : ℕ} (hn : Squarefree n) (hsub : n.primeFactors ⊆ P) :
    signedFamilyAggregate upper P D ε label n =
      normalizedSignedSet upper (fun p => geometricLower D ε (ε ^ 9) (label p))
        (fun p => geometricLower D ε (ε ^ 9) (label p) ^ (1 + ε ^ 9)) D
        (n.primeFactors \ geometricSmallPrimes P D ε) *
      signedSmallWeight upper P D ε (n.primeFactors \ geometricSmallPrimes P D ε).card
        ((n.primeFactors ∩ geometricSmallPrimes P D ε).prod id) := by
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hθ : 0 ≤ ε ^ 9 := pow_nonneg hε.le _
  let S := n.primeFactors \ geometricSmallPrimes P D ε
  have hS : S ⊆ P \ geometricSmallPrimes P D ε := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hp).1,
      (Finset.mem_sdiff.mp hp).2⟩
  have hnorm := normalizedSignedSet_eq_profile_indicator upper label
    (geometricLower D ε (ε ^ 9)) (fun j => geometricLower D ε (ε ^ 9) (j + 1)) D S
    (geometric_boxLabel_monotoneOn P S label hD1 hθ (fun p hp => hlabel p (hS hp)))
    (geometricLower_monotone hD1 hθ)
    (geometricLower_strictMono (by linarith) hε (pow_pos hε _)).injective
    (fun _ _ => geometricLower_one_le hD1 hθ _)
    (fun p hp => hhead p (hS hp))
    (fun p _ => geometricLower_monotone (ε := ε) hD1 hθ (Nat.le_succ (label p)))
  simp only [geometricLower_succ hD0] at hnorm
  rw [signedFamilyAggregate_squarefree_profile upper P label hD1 hε.le hlabel hn hsub]
  change _ = normalizedSignedSet _ _ _ _ S * _
  rw [hnorm]
  simp only [← geometricLower_succ hD0]
  split_ifs <;> simp [S]

/-- The normalized identification at every squarefree integer, including
integers outside the fixed sieve-prime support. It is not a squarefree mask
definition: the left side remains the common full-integer family. -/
theorem signedFamilyAggregate_squarefree (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D)
    {n : ℕ} (hn : Squarefree n) :
    signedFamilyAggregate upper P D ε label n =
      if n.primeFactors ⊆ P then
        normalizedSignedSet upper (fun p => geometricLower D ε (ε ^ 9) (label p))
          (fun p => geometricLower D ε (ε ^ 9) (label p) ^ (1 + ε ^ 9)) D
          (n.primeFactors \ geometricSmallPrimes P D ε) *
        signedSmallWeight upper P D ε (n.primeFactors \ geometricSmallPrimes P D ε).card
          ((n.primeFactors ∩ geometricSmallPrimes P D ε).prod id)
      else 0 := by
  by_cases hsub : n.primeFactors ⊆ P
  · rw [if_pos hsub]
    exact signedFamilyAggregate_squarefree_normalized upper P label hD hε hlabel hhead hn hsub
  · rw [if_neg hsub]
    exact signedFamilyAggregate_eq_zero_of_not_subset upper P D ε label hsub

#check signedTags_common_wellFactorable
#check signedFamilyTerm_squarefree
#check signedFamilyAggregate_squarefree_profile
#check signedFamilyAggregate_squarefree_normalized
#check signedFamilyAggregate_squarefree
#print axioms signedTags_common_wellFactorable
#print axioms signedFamilyTerm_squarefree
#print axioms signedFamilyAggregate_squarefree_profile
#print axioms signedFamilyAggregate_squarefree_normalized
#print axioms signedFamilyAggregate_squarefree

end MathlibNt.SieveTheory.LiLiuPrereqWF
