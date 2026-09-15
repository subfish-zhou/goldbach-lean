import MathlibNt.SieveTheory.LiLiuGoldbachG10Cofactor

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachPi10Sifted (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The labelled `B10` point keeps the genuine `Pi10` prime `q` and interval
constraints, and drops only the primality of `N - rsq`. -/
def goldbachB10Point (N : ℕ) (ε : ℝ) (rs : ℕ × ℕ) (q : ℕ) : Prop :=
  q.Prime ∧
    ε * (N : ℝ) / (goldbachC10Prod rs : ℝ) < (q : ℝ) ∧
    (q : ℝ) < (N : ℝ) / (goldbachC10Prod rs : ℝ)

/-- The pair-labelled `B10` fibre above a fixed corrected `C10` pair. -/
noncomputable def goldbachB10Fiber (N : ℕ) (ε : ℝ) (rs : ℕ × ℕ) : Finset ℕ :=
  (range (N + 1)).filter (goldbachB10Point N ε rs)

/-- Pair-labelled `B10` atoms. -/
noncomputable def goldbachB10Atoms (N : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachC10Pairs N b c).sigma (goldbachB10Fiber N ε)

theorem mem_goldbachB10Atoms_iff
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB10Atoms N ε b c ↔
      x.1 ∈ goldbachC10Pairs N b c ∧
        x.2 ∈ range (N + 1) ∧ goldbachB10Point N ε x.1 x.2 := by
  simp [goldbachB10Atoms, goldbachB10Fiber]

/-- The literal output prime candidate attached to a labelled `Pi10/B10` atom. -/
def goldbachPi10Output (N : ℕ) (x : Σ _rs : ℕ × ℕ, ℕ) : ℕ :=
  N - goldbachC10Prod x.1 * x.2

/-- The sifted `B10` fibre keeps the same labels and additionally requires the
literal sieve condition on the output `N - rsq`. -/
noncomputable def goldbachB10SiftedFiber
    (N : ℕ) (ε Z : ℝ) (rs : ℕ × ℕ) : Finset ℕ :=
  (goldbachB10Fiber N ε rs).filter
    (fun q => literalHPoint N 1 Z (N - goldbachC10Prod rs * q))

/-- Pair-labelled sifted `B10` atoms. -/
noncomputable def goldbachB10SiftedAtoms
    (N : ℕ) (ε b c Z : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachC10Pairs N b c).sigma (goldbachB10SiftedFiber N ε Z)

/-- The sifted labelled `B10` count. -/
noncomputable def goldbachB10SiftedCount
    (N : ℕ) (ε b c Z : ℝ) : ℤ :=
  ∑ rs ∈ goldbachC10Pairs N b c, ((goldbachB10SiftedFiber N ε Z rs).card : ℤ)

theorem goldbachB10SiftedCount_eq_card_atoms
    (N : ℕ) (ε b c Z : ℝ) :
    goldbachB10SiftedCount N ε b c Z =
      ((goldbachB10SiftedAtoms N ε b c Z).card : ℤ) := by
  simp [goldbachB10SiftedCount, goldbachB10SiftedAtoms, goldbachB10SiftedFiber]

theorem mem_goldbachB10SiftedAtoms_iff
    {N : ℕ} {ε b c Z : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB10SiftedAtoms N ε b c Z ↔
      x.1 ∈ goldbachC10Pairs N b c ∧
        x.2 ∈ range (N + 1) ∧
        goldbachB10Point N ε x.1 x.2 ∧
        literalHPoint N 1 Z (goldbachPi10Output N x) := by
  simp [goldbachB10SiftedAtoms, goldbachB10SiftedFiber, goldbachB10Fiber,
    goldbachPi10Output, and_assoc]

/-- The labelled `Pi10` fibre over a fixed output value `p = N - rsq`. -/
noncomputable def goldbachPi10OutputFiber
    (N : ℕ) (ε b c : ℝ) (p : ℕ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachPi10Atoms N ε b c).filter fun x => goldbachPi10Output N x = p

theorem mem_goldbachPi10OutputFiber_iff
    {N : ℕ} {ε b c : ℝ} {p : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachPi10OutputFiber N ε b c p ↔
      x ∈ goldbachPi10Atoms N ε b c ∧ goldbachPi10Output N x = p := by
  simp [goldbachPi10OutputFiber]

private theorem Pi10Sifted_prod_pos_of_pair_mem
    {N : ℕ} {b c : ℝ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N b c) :
    0 < goldbachC10Prod rs := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, _⟩
  exact Nat.mul_pos hrPrime.pos hsPrime.pos

private theorem Pi10Sifted_prod_lt_N_of_B10Atom
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachB10Atoms N ε b c) :
    goldbachC10Prod x.1 * x.2 < N := by
  rcases mem_goldbachB10Atoms_iff.mp hx with ⟨hrsMem, _, _, _, hqUpper⟩
  have hmpos : 0 < goldbachC10Prod x.1 := Pi10Sifted_prod_pos_of_pair_mem hrsMem
  have hmposReal : 0 < (goldbachC10Prod x.1 : ℝ) := by exact_mod_cast hmpos
  have hreal : (x.2 : ℝ) * (goldbachC10Prod x.1 : ℝ) < N := by
    rw [lt_div_iff₀ hmposReal] at hqUpper
    simpa [mul_comm] using hqUpper
  have hnat : x.2 * goldbachC10Prod x.1 < N := by
    exact_mod_cast hreal
  simpa [goldbachC10Prod, mul_comm] using hnat

private theorem Pi10Sifted_prod_lt_N_of_Pi10Atom
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachPi10Atoms N ε b c) :
    goldbachC10Prod x.1 * x.2 < N := by
  rcases mem_goldbachPi10Atoms_iff.mp hx with
    ⟨hrsMem, hqRange, hqPrime, hqLower, hqUpper, _⟩
  exact Pi10Sifted_prod_lt_N_of_B10Atom
    (mem_goldbachB10Atoms_iff.mpr ⟨hrsMem, hqRange, hqPrime, hqLower, hqUpper⟩)

private theorem Pi10Sifted_literalHPoint_of_prime_ge
    {N p : ℕ} {Z : ℝ}
    (hpPrime : p.Prime) (hZp : Z ≤ (p : ℝ)) :
    literalHPoint N 1 Z p := by
  refine ⟨by simp, ?_⟩
  intro ℓ hℓPrime hℓdvd hℓN
  have hEq : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓPrime hpPrime).mp hℓdvd
  simpa [hEq] using hZp

private theorem Pi10Sifted_fst_dvd_of_prod_dvd {a b n : ℕ} (h : a * b ∣ n) : a ∣ n :=
  dvd_trans (dvd_mul_right a b) h

private theorem Pi10Sifted_snd_dvd_of_prod_dvd {a b n : ℕ} (h : a * b ∣ n) : b ∣ n :=
  dvd_trans (dvd_mul_left b a) h

private theorem Pi10Sifted_prod_eq_sub_of_outputFiber
    {N : ℕ} {ε b c : ℝ} {p : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachPi10OutputFiber N ε b c p) :
    goldbachC10Prod x.1 * x.2 = N - p := by
  have hxPi : x ∈ goldbachPi10Atoms N ε b c := (mem_goldbachPi10OutputFiber_iff.mp hx).1
  have hprod : goldbachC10Prod x.1 * x.2 < N := Pi10Sifted_prod_lt_N_of_Pi10Atom hxPi
  have hxp : goldbachPi10Output N x = p := (mem_goldbachPi10OutputFiber_iff.mp hx).2
  unfold goldbachPi10Output at hxp
  omega

private theorem Pi10Sifted_q_eq_div_of_outputFiber
    {N : ℕ} {ε b c : ℝ} {p : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachPi10OutputFiber N ε b c p) :
    x.2 = (N - p) / goldbachC10Prod x.1 := by
  have hxPi : x ∈ goldbachPi10Atoms N ε b c := (mem_goldbachPi10OutputFiber_iff.mp hx).1
  have hrsMem : x.1 ∈ goldbachC10Pairs N b c := (mem_goldbachPi10Atoms_iff.mp hxPi).1
  have hmpos : 0 < goldbachC10Prod x.1 := Pi10Sifted_prod_pos_of_pair_mem hrsMem
  have hEq : goldbachC10Prod x.1 * x.2 = N - p := Pi10Sifted_prod_eq_sub_of_outputFiber hx
  have hdiv :
      (x.2 * goldbachC10Prod x.1) / goldbachC10Prod x.1 = x.2 := by
    simpa [mul_comm] using (Nat.mul_div_cancel_left x.2 hmpos)
  calc
    x.2 = (x.2 * goldbachC10Prod x.1) / goldbachC10Prod x.1 := hdiv.symm
    _ = (N - p) / goldbachC10Prod x.1 := by rw [mul_comm, hEq]

private theorem Pi10Sifted_outputFiber_fst_mem_largePrimeDivisors
    {N : ℕ} {ε β c : ℝ} {p : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachPi10OutputFiber N ε ((N : ℝ) ^ β) c p) :
    x.1.1 ∈ largePrimeDivisors (N - p) ((N : ℝ) ^ β) := by
  have hxPi : x ∈ goldbachPi10Atoms N ε ((N : ℝ) ^ β) c :=
    (mem_goldbachPi10OutputFiber_iff.mp hx).1
  rcases mem_goldbachPi10Atoms_iff.mp hxPi with ⟨hrsMem, _, hqPrime, _, _, _⟩
  have hrs := mem_goldbachC10Pairs_iff.mp hrsMem
  have hEq : goldbachC10Prod x.1 * x.2 = N - p := Pi10Sifted_prod_eq_sub_of_outputFiber hx
  have hmpos : 0 < goldbachC10Prod x.1 := Pi10Sifted_prod_pos_of_pair_mem hrsMem
  have hmulPos : 0 < goldbachC10Prod x.1 * x.2 := Nat.mul_pos hmpos hqPrime.pos
  have hn0 : N - p ≠ 0 := by
    omega
  have hprodDvd : goldbachC10Prod x.1 ∣ N - p := ⟨x.2, hEq.symm⟩
  have hrdvd : x.1.1 ∣ N - p := Pi10Sifted_fst_dvd_of_prod_dvd hprodDvd
  change x.1.1 ∈ (N - p).primeFactors.filter (fun q : ℕ => (N : ℝ) ^ β ≤ (q : ℝ))
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hrs.1, hrdvd, hn0⟩, hrs.2.2.2.1⟩

private theorem Pi10Sifted_outputFiber_snd_mem_largePrimeDivisors
    {N : ℕ} {ε β c : ℝ} {p : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachPi10OutputFiber N ε ((N : ℝ) ^ β) c p) :
    x.1.2 ∈ largePrimeDivisors (N - p) ((N : ℝ) ^ β) := by
  have hxPi : x ∈ goldbachPi10Atoms N ε ((N : ℝ) ^ β) c :=
    (mem_goldbachPi10OutputFiber_iff.mp hx).1
  rcases mem_goldbachPi10Atoms_iff.mp hxPi with ⟨hrsMem, _, hqPrime, _, _, _⟩
  have hrs := mem_goldbachC10Pairs_iff.mp hrsMem
  have hEq : goldbachC10Prod x.1 * x.2 = N - p := Pi10Sifted_prod_eq_sub_of_outputFiber hx
  have hmpos : 0 < goldbachC10Prod x.1 := Pi10Sifted_prod_pos_of_pair_mem hrsMem
  have hmulPos : 0 < goldbachC10Prod x.1 * x.2 := Nat.mul_pos hmpos hqPrime.pos
  have hn0 : N - p ≠ 0 := by
    omega
  have hprodDvd : goldbachC10Prod x.1 ∣ N - p := ⟨x.2, hEq.symm⟩
  have hsdvd : x.1.2 ∣ N - p := Pi10Sifted_snd_dvd_of_prod_dvd hprodDvd
  have hβle : (N : ℝ) ^ β ≤ (x.1.2 : ℝ) := by
    exact le_trans hrs.2.2.2.1 <|
      le_trans hrs.2.2.2.2.1 hrs.2.2.2.2.2.1
  change x.1.2 ∈ (N - p).primeFactors.filter (fun q : ℕ => (N : ℝ) ^ β ≤ (q : ℝ))
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hrs.2.1, hsdvd, hn0⟩, hβle⟩

/-- Each fixed labelled `Pi10` output fibre is bounded by `400`. -/
theorem goldbachPi10OutputFiber_card_le_fourHundred
    {N : ℕ} {ε β c : ℝ}
    (hβ : (1 : ℝ) / 18 < β) (p : ℕ) :
    ((goldbachPi10OutputFiber N ε ((N : ℝ) ^ β) c p).card : ℤ) ≤ 400 := by
  let A := goldbachPi10OutputFiber N ε ((N : ℝ) ^ β) c p
  by_cases hA0 : A.card = 0
  · have hA : A = ∅ := Finset.card_eq_zero.mp hA0
    simp [A, hA]
  · have hA : A.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hA0)
    rcases hA with ⟨x, hx⟩
    have hxPi : x ∈ goldbachPi10Atoms N ε ((N : ℝ) ^ β) c :=
      (mem_goldbachPi10OutputFiber_iff.mp hx).1
    rcases mem_goldbachPi10Atoms_iff.mp hxPi with ⟨hrsMem, _, hqPrime, _, _, hpPrimeOut⟩
    have hxp : goldbachPi10Output N x = p := (mem_goldbachPi10OutputFiber_iff.mp hx).2
    have hpPrime : p.Prime := by
      have hpOut : (goldbachPi10Output N x).Prime := by
        simpa [goldbachPi10Output] using hpPrimeOut
      simpa [hxp] using hpOut
    let D := largePrimeDivisors (N - p) ((N : ℝ) ^ β)
    have hp1 : 1 ≤ p := hpPrime.one_lt.le
    have hEq : goldbachC10Prod x.1 * x.2 = N - p := Pi10Sifted_prod_eq_sub_of_outputFiber hx
    have hmpos : 0 < goldbachC10Prod x.1 := Pi10Sifted_prod_pos_of_pair_mem hrsMem
    have hmulPos : 0 < goldbachC10Prod x.1 * x.2 := Nat.mul_pos hmpos hqPrime.pos
    have hn1 : 1 ≤ N - p := by
      omega
    have hnN : N - p < N := by
      omega
    have hβ21 : (1 : ℝ) / 21 < β := by
      nlinarith
    have hcap : D.card ≤ 20 := by
      simpa [D] using largePrimeDivisors_card_le_twenty hn1 hnN hβ21
    have hmaps :
        Set.MapsTo (fun y : Σ _rs : ℕ × ℕ, ℕ => y.1) A (D.product D) := by
      intro y hy
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · simpa [D] using Pi10Sifted_outputFiber_fst_mem_largePrimeDivisors hy
      · simpa [D] using Pi10Sifted_outputFiber_snd_mem_largePrimeDivisors hy
    have hinj :
        Set.InjOn (fun y : Σ _rs : ℕ × ℕ, ℕ => y.1) A := by
      intro y hy z hz hyz
      have hyq := Pi10Sifted_q_eq_div_of_outputFiber hy
      have hzq := Pi10Sifted_q_eq_div_of_outputFiber hz
      cases y with
      | mk rsy qy =>
        cases z with
        | mk rsz qz =>
          simp at hyz hyq hzq ⊢
          subst hyz
          exact ⟨rfl, hyq.trans hzq.symm⟩
    have hcard : A.card ≤ (D.product D).card := Finset.card_le_card_of_injOn _ hmaps hinj
    have hnat : A.card ≤ 400 := by
      calc
        A.card ≤ (D.product D).card := hcard
        _ = D.card * D.card := by simp
        _ ≤ 20 * 20 := Nat.mul_le_mul hcap hcap
        _ = 400 := by norm_num
    exact_mod_cast hnat

private noncomputable def Pi10SiftedLowAtoms
    (N : ℕ) (ε b c Z : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachPi10Atoms N ε b c).filter fun x => (goldbachPi10Output N x : ℝ) < Z

private noncomputable def Pi10SiftedHighAtoms
    (N : ℕ) (ε b c Z : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachPi10Atoms N ε b c).filter fun x => Z ≤ (goldbachPi10Output N x : ℝ)

private theorem Pi10Sifted_mem_lowAtoms_iff
    {N : ℕ} {ε b c Z : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ Pi10SiftedLowAtoms N ε b c Z ↔
      x ∈ goldbachPi10Atoms N ε b c ∧ (goldbachPi10Output N x : ℝ) < Z := by
  simp [Pi10SiftedLowAtoms]

private theorem Pi10Sifted_mem_highAtoms_iff
    {N : ℕ} {ε b c Z : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ Pi10SiftedHighAtoms N ε b c Z ↔
      x ∈ goldbachPi10Atoms N ε b c ∧ Z ≤ (goldbachPi10Output N x : ℝ) := by
  simp [Pi10SiftedHighAtoms]

private theorem Pi10Sifted_high_subset_sifted
    {N : ℕ} {ε b c Z : ℝ} :
    Pi10SiftedHighAtoms N ε b c Z ⊆ goldbachB10SiftedAtoms N ε b c Z := by
  intro x hx
  rcases Pi10Sifted_mem_highAtoms_iff.mp hx with ⟨hxPi, hhigh⟩
  rcases mem_goldbachPi10Atoms_iff.mp hxPi with
    ⟨hrsMem, hqRange, hqPrime, hqLower, hqUpper, hpPrime⟩
  have hsifted : literalHPoint N 1 Z (goldbachPi10Output N x) :=
    Pi10Sifted_literalHPoint_of_prime_ge hpPrime hhigh
  exact mem_goldbachB10SiftedAtoms_iff.mpr
    ⟨hrsMem, hqRange, ⟨hqPrime, hqLower, hqUpper⟩, hsifted⟩

private theorem Pi10Sifted_high_card_le_siftedCount
    {N : ℕ} {ε b c Z : ℝ} :
    ((Pi10SiftedHighAtoms N ε b c Z).card : ℤ) ≤ goldbachB10SiftedCount N ε b c Z := by
  have hsubset : Pi10SiftedHighAtoms N ε b c Z ⊆ goldbachB10SiftedAtoms N ε b c Z :=
    Pi10Sifted_high_subset_sifted
  calc
    ((Pi10SiftedHighAtoms N ε b c Z).card : ℤ)
        ≤ ((goldbachB10SiftedAtoms N ε b c Z).card : ℤ) := by
            exact_mod_cast Finset.card_le_card hsubset
    _ = goldbachB10SiftedCount N ε b c Z :=
      (goldbachB10SiftedCount_eq_card_atoms N ε b c Z).symm

private abbrev Pi10SiftedLowTargetAtom := Σ _p : ℕ, Σ _rs : ℕ × ℕ, ℕ

private noncomputable def Pi10SiftedLowTargetShapes
    (N : ℕ) (ε b c Z : ℝ) : Finset Pi10SiftedLowTargetAtom :=
  (Finset.Icc 1 ⌊Z⌋₊).sigma (goldbachPi10OutputFiber N ε b c)

private def Pi10SiftedLowEncode
    (N : ℕ) (x : Σ _rs : ℕ × ℕ, ℕ) : Pi10SiftedLowTargetAtom :=
  ⟨goldbachPi10Output N x, x⟩

private theorem Pi10SiftedLowEncode_injective (N : ℕ) :
    Function.Injective (Pi10SiftedLowEncode N) := by
  intro x y hxy
  have := congrArg Sigma.snd hxy
  simpa [Pi10SiftedLowEncode] using this

private theorem Pi10SiftedLowEncode_mapsTo
    {N : ℕ} {ε b c Z : ℝ}
    (hZ : 1 ≤ Z) :
    Set.MapsTo (Pi10SiftedLowEncode N)
      (Pi10SiftedLowAtoms N ε b c Z)
      (Pi10SiftedLowTargetShapes N ε b c Z) := by
  intro x hx
  rcases Pi10Sifted_mem_lowAtoms_iff.mp hx with ⟨hxPi, hlow⟩
  rcases mem_goldbachPi10Atoms_iff.mp hxPi with ⟨_, _, _, _, _, hpPrime⟩
  have hp1 : 1 ≤ goldbachPi10Output N x := hpPrime.one_lt.le
  have hfloor : goldbachPi10Output N x ≤ ⌊Z⌋₊ := by
    exact (Nat.le_floor_iff (show 0 ≤ Z by linarith)).mpr hlow.le
  simp [Pi10SiftedLowTargetShapes, Pi10SiftedLowEncode, goldbachPi10OutputFiber,
    hp1, hfloor, hxPi]

private theorem Pi10Sifted_low_card_le_fourHundred_mul_floor
    {N : ℕ} {ε β c Z : ℝ}
    (hβ : (1 : ℝ) / 18 < β) (hZ : 1 ≤ Z) :
    ((Pi10SiftedLowAtoms N ε ((N : ℝ) ^ β) c Z).card : ℤ) ≤
      400 * (⌊Z⌋₊ : ℤ) := by
  let A := Pi10SiftedLowAtoms N ε ((N : ℝ) ^ β) c Z
  let T := Pi10SiftedLowTargetShapes N ε ((N : ℝ) ^ β) c Z
  have hinj :
      Set.InjOn (Pi10SiftedLowEncode N) A := by
    intro x hx y hy hxy
    exact Pi10SiftedLowEncode_injective N hxy
  have hcard : A.card ≤ T.card := by
    exact Finset.card_le_card_of_injOn _ (Pi10SiftedLowEncode_mapsTo hZ) hinj
  have htarget :
      ((T.card : ℕ) : ℤ) =
        ∑ p ∈ Finset.Icc 1 ⌊Z⌋₊,
          ((goldbachPi10OutputFiber N ε ((N : ℝ) ^ β) c p).card : ℤ) := by
    simp [T, Pi10SiftedLowTargetShapes]
  have hsum :
      (∑ p ∈ Finset.Icc 1 ⌊Z⌋₊,
          ((goldbachPi10OutputFiber N ε ((N : ℝ) ^ β) c p).card : ℤ))
        ≤
      ∑ p ∈ Finset.Icc 1 ⌊Z⌋₊, (400 : ℤ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact goldbachPi10OutputFiber_card_le_fourHundred (N := N) (ε := ε)
      (β := β) (c := c) hβ p
  have hcardIcc : (Finset.Icc 1 ⌊Z⌋₊).card = ⌊Z⌋₊ := by
    have hfloor1 : 1 ≤ ⌊Z⌋₊ := (Nat.one_le_floor_iff _).mpr hZ
    rw [Nat.card_Icc]
    omega
  calc
    ((A.card : ℕ) : ℤ) ≤ (T.card : ℤ) := by
      exact_mod_cast hcard
    _ = ∑ p ∈ Finset.Icc 1 ⌊Z⌋₊,
          ((goldbachPi10OutputFiber N ε ((N : ℝ) ^ β) c p).card : ℤ) := htarget
    _ ≤ ∑ p ∈ Finset.Icc 1 ⌊Z⌋₊, (400 : ℤ) := hsum
    _ = (((Finset.Icc 1 ⌊Z⌋₊).card : ℤ) * 400) := by simp
    _ = 400 * (⌊Z⌋₊ : ℤ) := by simp [hcardIcc, mul_comm]

private theorem Pi10Sifted_card_split
    (N : ℕ) (ε b c Z : ℝ) :
    ((goldbachPi10Atoms N ε b c).card : ℤ) =
      ((Pi10SiftedLowAtoms N ε b c Z).card : ℤ) +
        ((Pi10SiftedHighAtoms N ε b c Z).card : ℤ) := by
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachPi10Atoms N ε b c)
      (fun x : Σ _rs : ℕ × ℕ, ℕ => (goldbachPi10Output N x : ℝ) < Z)
      (fun _ => (1 : ℤ))
  simpa [Pi10SiftedLowAtoms, Pi10SiftedHighAtoms, not_lt] using hsplit.symm

/-- `Pi10` is bounded by the sifted labelled `B10` source plus the
`400 * floor(Z)` low-output error. -/
theorem goldbachPi10_le_goldbachB10SiftedCount_add_fourHundred_floor
    {N : ℕ} {ε β c Z : ℝ}
    (_hN : 2 ≤ N)
    (_hε : 0 < ε)
    (hβ : (1 : ℝ) / 18 < β)
    (hZ : 1 ≤ Z) :
    goldbachPi10 N ε ((N : ℝ) ^ β) c ≤
      goldbachB10SiftedCount N ε ((N : ℝ) ^ β) c Z +
        400 * (⌊Z⌋₊ : ℤ) := by
  calc
    goldbachPi10 N ε ((N : ℝ) ^ β) c
        = ((Pi10SiftedLowAtoms N ε ((N : ℝ) ^ β) c Z).card : ℤ) +
            ((Pi10SiftedHighAtoms N ε ((N : ℝ) ^ β) c Z).card : ℤ) := by
              rw [goldbachPi10_eq_card_atoms]
              exact Pi10Sifted_card_split N ε ((N : ℝ) ^ β) c Z
    _ ≤ 400 * (⌊Z⌋₊ : ℤ) + goldbachB10SiftedCount N ε ((N : ℝ) ^ β) c Z := by
          exact add_le_add
            (Pi10Sifted_low_card_le_fourHundred_mul_floor
              (N := N) (ε := ε) (β := β) (c := c) (Z := Z) hβ hZ)
            (Pi10Sifted_high_card_le_siftedCount
              (N := N) (ε := ε) (b := (N : ℝ) ^ β) (c := c) (Z := Z))
    _ = goldbachB10SiftedCount N ε ((N : ℝ) ^ β) c Z +
          400 * (⌊Z⌋₊ : ℤ) := by
            ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig