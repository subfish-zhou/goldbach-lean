import MathlibNt.SieveTheory.LiLiuGoldbachB10Support

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB10ProductCount (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The actual finite product support of the corrected `C10` carrier. -/
noncomputable def goldbachC10ProductSupport (N : ℕ) (b c : ℝ) : Finset ℕ :=
  (goldbachC10Pairs N b c).image goldbachC10Prod

theorem mem_goldbachC10ProductSupport_iff
    {N : ℕ} {b c : ℝ} {m : ℕ} :
    m ∈ goldbachC10ProductSupport N b c ↔
      ∃ rs ∈ goldbachC10Pairs N b c, goldbachC10Prod rs = m := by
  simp [goldbachC10ProductSupport]

theorem goldbachC10Coeff_eq_one_of_mem_productSupport
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c) :
    goldbachC10Coeff N b c m = 1 := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, hprod⟩
  have hnonempty : (goldbachC10ProductFiber N b c m).Nonempty := by
    exact ⟨rs, mem_goldbachC10ProductFiber_iff.mpr ⟨hrs, hprod⟩⟩
  have hpos : 0 < goldbachC10Coeff N b c m := by
    simpa [goldbachC10Coeff] using Finset.card_pos.mpr hnonempty
  have hle : goldbachC10Coeff N b c m ≤ 1 :=
    goldbachC10Coeff_le_one (N := N) (b := b) (c := c) (m := m)
  omega

/-- Exact finite reindexing of a sum over the corrected `C10` carrier by the
actual product support, with the genuine coefficient `α(m)`. -/
theorem goldbachC10_sum_nat_eq_sum_productSupport
    (N : ℕ) (b c : ℝ) (f : ℕ → ℕ) :
    (∑ rs ∈ goldbachC10Pairs N b c, f (goldbachC10Prod rs)) =
      ∑ m ∈ goldbachC10ProductSupport N b c, goldbachC10Coeff N b c m * f m := by
  classical
  have himage :
      (∑ m ∈ goldbachC10ProductSupport N b c, f m) =
        ∑ rs ∈ goldbachC10Pairs N b c, f (goldbachC10Prod rs) := by
    unfold goldbachC10ProductSupport
    rw [Finset.sum_image]
    intro rs hrs tu htu hEq
    exact goldbachC10Prod_injOn (N := N) (b := b) (c := c) hrs htu hEq
  calc
    ∑ rs ∈ goldbachC10Pairs N b c, f (goldbachC10Prod rs)
        = ∑ m ∈ goldbachC10ProductSupport N b c, f m := by
            simpa using himage.symm
    _ = ∑ m ∈ goldbachC10ProductSupport N b c, goldbachC10Coeff N b c m * f m := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [goldbachC10Coeff_eq_one_of_mem_productSupport hm, one_mul]

theorem goldbachC10_sum_int_eq_sum_productSupport
    (N : ℕ) (b c : ℝ) (f : ℕ → ℤ) :
    (∑ rs ∈ goldbachC10Pairs N b c, f (goldbachC10Prod rs)) =
      ∑ m ∈ goldbachC10ProductSupport N b c, (goldbachC10Coeff N b c m : ℤ) * f m := by
  classical
  have himage :
      (∑ m ∈ goldbachC10ProductSupport N b c, f m) =
        ∑ rs ∈ goldbachC10Pairs N b c, f (goldbachC10Prod rs) := by
    unfold goldbachC10ProductSupport
    rw [Finset.sum_image]
    intro rs hrs tu htu hEq
    exact goldbachC10Prod_injOn (N := N) (b := b) (c := c) hrs htu hEq
  calc
    ∑ rs ∈ goldbachC10Pairs N b c, f (goldbachC10Prod rs)
        = ∑ m ∈ goldbachC10ProductSupport N b c, f m := by
            simpa using himage.symm
    _ = ∑ m ∈ goldbachC10ProductSupport N b c, (goldbachC10Coeff N b c m : ℤ) * f m := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          simp [goldbachC10Coeff_eq_one_of_mem_productSupport hm]

/-- The literal `q`-carrier above a fixed product label `m = rs`, with the
actual `m`-dependent interval `εN/m < q < N/m`. -/
noncomputable def goldbachB10ProductQFiber (N : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun q =>
    q.Prime ∧ ε * (N : ℝ) / (m : ℝ) < (q : ℝ) ∧ (q : ℝ) < (N : ℝ) / (m : ℝ)

theorem mem_goldbachB10ProductQFiber_iff
    {N : ℕ} {ε : ℝ} {m q : ℕ} :
    q ∈ goldbachB10ProductQFiber N ε m ↔
      q ∈ range (N + 1) ∧
        q.Prime ∧ ε * (N : ℝ) / (m : ℝ) < (q : ℝ) ∧ (q : ℝ) < (N : ℝ) / (m : ℝ) := by
  simp [goldbachB10ProductQFiber]

theorem goldbachB10Fiber_eq_productQFiber
    (N : ℕ) (ε : ℝ) (rs : ℕ × ℕ) :
    goldbachB10Fiber N ε rs = goldbachB10ProductQFiber N ε (goldbachC10Prod rs) := by
  ext q
  simp [goldbachB10Fiber, goldbachB10ProductQFiber, goldbachB10Point]

theorem goldbachB10Atoms_card_eq_sum_productSupport
    (N : ℕ) (ε b c : ℝ) :
    (goldbachB10Atoms N ε b c).card =
      ∑ m ∈ goldbachC10ProductSupport N b c,
        goldbachC10Coeff N b c m * (goldbachB10ProductQFiber N ε m).card := by
  classical
  calc
    (goldbachB10Atoms N ε b c).card =
        ∑ rs ∈ goldbachC10Pairs N b c, (goldbachB10Fiber N ε rs).card := by
          simp [goldbachB10Atoms]
    _ = ∑ rs ∈ goldbachC10Pairs N b c,
          (goldbachB10ProductQFiber N ε (goldbachC10Prod rs)).card := by
            refine Finset.sum_congr rfl ?_
            intro rs hrs
            rw [goldbachB10Fiber_eq_productQFiber]
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
          goldbachC10Coeff N b c m * (goldbachB10ProductQFiber N ε m).card := by
            simpa using
              goldbachC10_sum_nat_eq_sum_productSupport
                (N := N) (b := b) (c := c)
                (f := fun m => (goldbachB10ProductQFiber N ε m).card)

/-- The literal sifted `q`-fibre above a fixed product label `m = rs`. -/
noncomputable def goldbachB10ProductSiftedQFiber
    (N : ℕ) (ε Z : ℝ) (m : ℕ) : Finset ℕ :=
  (goldbachB10ProductQFiber N ε m).filter
    (fun q => literalHPoint N 1 Z (N - m * q))

theorem goldbachB10SiftedFiber_eq_productSiftedQFiber
    (N : ℕ) (ε Z : ℝ) (rs : ℕ × ℕ) :
    goldbachB10SiftedFiber N ε Z rs =
      goldbachB10ProductSiftedQFiber N ε Z (goldbachC10Prod rs) := by
  rw [goldbachB10SiftedFiber, goldbachB10ProductSiftedQFiber, goldbachB10Fiber_eq_productQFiber]

theorem goldbachB10SiftedCount_eq_sum_productSupport
    (N : ℕ) (ε b c Z : ℝ) :
    goldbachB10SiftedCount N ε b c Z =
      ∑ m ∈ goldbachC10ProductSupport N b c,
        (goldbachC10Coeff N b c m : ℤ) *
          (((goldbachB10ProductQFiber N ε m).filter
            (fun q => literalHPoint N 1 Z (N - m * q))).card : ℤ) := by
  classical
  calc
    goldbachB10SiftedCount N ε b c Z =
        ∑ rs ∈ goldbachC10Pairs N b c,
          ((goldbachB10SiftedFiber N ε Z rs).card : ℤ) := by
            simp [goldbachB10SiftedCount]
    _ = ∑ rs ∈ goldbachC10Pairs N b c,
          ((goldbachB10ProductSiftedQFiber N ε Z (goldbachC10Prod rs)).card : ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro rs hrs
            rw [goldbachB10SiftedFiber_eq_productSiftedQFiber]
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
          (goldbachC10Coeff N b c m : ℤ) * ((goldbachB10ProductSiftedQFiber N ε Z m).card : ℤ) := by
            simpa using
              goldbachC10_sum_int_eq_sum_productSupport
                (N := N) (b := b) (c := c)
                (f := fun m => ((goldbachB10ProductSiftedQFiber N ε Z m).card : ℤ))
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
          (goldbachC10Coeff N b c m : ℤ) *
            (((goldbachB10ProductQFiber N ε m).filter
              (fun q => literalHPoint N 1 Z (N - m * q))).card : ℤ) := by
            rfl

/-- The inverse-residue `q`-filter above a fixed product label `m = rs`. -/
noncomputable def goldbachB10ProductResidueQFiber
    (N d : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  (goldbachB10ProductQFiber N ε m).filter
    (fun q => (q : ZMod d) = (N : ZMod d) * (m : ZMod d)⁻¹)

theorem goldbachB10ProductResidueQFiber_eq_filter
    (N d : ℕ) (ε : ℝ) (m : ℕ) :
    goldbachB10ProductResidueQFiber N d ε m =
      (goldbachB10ProductQFiber N ε m).filter
        (fun q : ℕ => (q : ZMod d) = (N : ZMod d) * (m : ZMod d)⁻¹) := by
  rfl

theorem mem_goldbachB10ProductResidueQFiber_iff
    {N d : ℕ} {ε : ℝ} {m q : ℕ} :
    q ∈ goldbachB10ProductResidueQFiber N d ε m ↔
      q ∈ goldbachB10ProductQFiber N ε m ∧
        (q : ZMod d) = (N : ZMod d) * (m : ZMod d)⁻¹ := by
  simp [goldbachB10ProductResidueQFiber]

private noncomputable def B10ProductCountDivisorPairFiber
    (N d : ℕ) (ε : ℝ) (rs : ℕ × ℕ) : Finset ℕ :=
  (goldbachB10Fiber N ε rs).filter fun q => d ∣ goldbachPi10Output N (Sigma.mk rs q)

private theorem B10ProductCount_divisorAtoms_eq_sigma
    (N d : ℕ) (ε b c : ℝ) :
    goldbachB10DivisorAtoms N d ε b c =
      (goldbachC10Pairs N b c).sigma (B10ProductCountDivisorPairFiber N d ε) := by
  ext x
  cases x with
  | mk rs q =>
      simp [goldbachB10DivisorAtoms, goldbachB10Atoms, B10ProductCountDivisorPairFiber,
        and_assoc]

private theorem B10ProductCount_divisorPairFiber_eq_if
    {N d : ℕ} {ε b c : ℝ} {rs : ℕ × ℕ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hrs : rs ∈ goldbachC10Pairs N b c) :
    B10ProductCountDivisorPairFiber N d ε rs =
      if Nat.Coprime (goldbachC10Prod rs) d then
        goldbachB10ProductResidueQFiber N d ε (goldbachC10Prod rs)
      else ∅ := by
  by_cases hcop : Nat.Coprime (goldbachC10Prod rs) d
  · rw [if_pos hcop, B10ProductCountDivisorPairFiber, goldbachB10Fiber_eq_productQFiber,
      goldbachB10ProductResidueQFiber]
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hqFiber, hdiv⟩
      have hqData : q ∈ range (N + 1) ∧ goldbachB10Point N ε rs q := by
        simpa [goldbachB10ProductQFiber, goldbachB10Point] using hqFiber
      have hxAtom : Sigma.mk rs q ∈ goldbachB10Atoms N ε b c :=
        mem_goldbachB10Atoms_iff.mpr ⟨hrs, hqData.1, hqData.2⟩
      have hres :
          goldbachB10DivisorResidueCondition N d (Sigma.mk rs q) :=
        (goldbachB10Atom_output_dvd_iff_residueCondition
          (x := Sigma.mk rs q) hd hdN hxAtom).mp hdiv
      exact Finset.mem_filter.mpr ⟨hqFiber, hres.2⟩
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hqFiber, hqResidue⟩
      have hqData : q ∈ range (N + 1) ∧ goldbachB10Point N ε rs q := by
        simpa [goldbachB10ProductQFiber, goldbachB10Point] using hqFiber
      have hxAtom : Sigma.mk rs q ∈ goldbachB10Atoms N ε b c :=
        mem_goldbachB10Atoms_iff.mpr ⟨hrs, hqData.1, hqData.2⟩
      have hdiv :
          d ∣ goldbachPi10Output N (Sigma.mk rs q) :=
        (goldbachB10Atom_output_dvd_iff_residueCondition
          (x := Sigma.mk rs q) hd hdN hxAtom).mpr ⟨hcop, hqResidue⟩
      exact Finset.mem_filter.mpr ⟨hqFiber, hdiv⟩
  · ext q
    constructor
    · intro hq
      exfalso
      rcases Finset.mem_filter.mp hq with ⟨hqFiber, hdiv⟩
      have hqData : q ∈ range (N + 1) ∧ goldbachB10Point N ε rs q := by
        simpa [goldbachB10Fiber] using hqFiber
      have hxAtom : Sigma.mk rs q ∈ goldbachB10Atoms N ε b c :=
        mem_goldbachB10Atoms_iff.mpr ⟨hrs, hqData.1, hqData.2⟩
      have hres :
          goldbachB10DivisorResidueCondition N d (Sigma.mk rs q) :=
        (goldbachB10Atom_output_dvd_iff_residueCondition
          (x := Sigma.mk rs q) hd hdN hxAtom).mp hdiv
      exact hcop hres.1
    · simp [if_neg hcop]

theorem goldbachB10DivisorAtoms_card_eq_sum_productSupport
    {N d : ℕ} (ε b c : ℝ)
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N) :
    (goldbachB10DivisorAtoms N d ε b c).card =
      ∑ m ∈ goldbachC10ProductSupport N b c,
        goldbachC10Coeff N b c m *
          (if Nat.Coprime m d then (goldbachB10ProductResidueQFiber N d ε m).card else 0) := by
  classical
  calc
    (goldbachB10DivisorAtoms N d ε b c).card =
        ∑ rs ∈ goldbachC10Pairs N b c, (B10ProductCountDivisorPairFiber N d ε rs).card := by
          rw [B10ProductCount_divisorAtoms_eq_sigma]
          simp [B10ProductCountDivisorPairFiber]
    _ = ∑ rs ∈ goldbachC10Pairs N b c,
          if Nat.Coprime (goldbachC10Prod rs) d then
            (goldbachB10ProductResidueQFiber N d ε (goldbachC10Prod rs)).card
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro rs hrs
            rw [B10ProductCount_divisorPairFiber_eq_if (b := b) (c := c) hd hdN hrs]
            split_ifs <;> simp
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
          goldbachC10Coeff N b c m *
            (if Nat.Coprime m d then (goldbachB10ProductResidueQFiber N d ε m).card else 0) := by
              simpa using
                goldbachC10_sum_nat_eq_sum_productSupport
                  (N := N) (b := b) (c := c)
                  (f := fun m =>
                    if Nat.Coprime m d then (goldbachB10ProductResidueQFiber N d ε m).card else 0)

theorem goldbachC10ProductSupport_pos
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c) :
    0 < m := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, hprod⟩
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, _⟩
  rw [← hprod]
  simpa [goldbachC10Prod] using Nat.mul_pos hrPrime.pos hsPrime.pos

theorem goldbachC10ProductSupport_le_rpow_half_and_lt_two_thirds
    {N : ℕ} {b γ : ℝ} {m : ℕ}
    (hN : 2 ≤ N)
    (hγ : γ < (1 : ℝ) / 3)
    (hm : m ∈ goldbachC10ProductSupport N b ((N : ℝ) ^ γ)) :
    (m : ℝ) ≤ (N : ℝ) ^ ((1 + γ) / 2) ∧
      (N : ℝ) ^ ((1 + γ) / 2) < (N : ℝ) ^ ((2 : ℝ) / 3) := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, hprod⟩
  simpa [hprod] using goldbachC10Prod_le_rpow_half_and_lt_two_thirds hN hγ hrs

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig