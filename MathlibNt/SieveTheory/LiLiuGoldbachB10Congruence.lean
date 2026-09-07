import MathlibNt.SieveTheory.LiLiuGoldbachPi10Sifted
import Mathlib.Data.Nat.ModEq

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB10Congruence (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The corrected `C10` product fibre over a fixed value `m = rs`. -/
noncomputable def goldbachC10ProductFiber (N : ℕ) (b c : ℝ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (goldbachC10Pairs N b c).filter fun rs => goldbachC10Prod rs = m

/-- The actual finite `C10` coefficient
`α(m) = #{rs ∈ C10 : rs = m}`. -/
noncomputable def goldbachC10Coeff (N : ℕ) (b c : ℝ) (m : ℕ) : ℕ :=
  (goldbachC10ProductFiber N b c m).card

theorem mem_goldbachC10ProductFiber_iff
    {N : ℕ} {b c : ℝ} {m : ℕ} {rs : ℕ × ℕ} :
    rs ∈ goldbachC10ProductFiber N b c m ↔
      rs ∈ goldbachC10Pairs N b c ∧ goldbachC10Prod rs = m := by
  simp [goldbachC10ProductFiber]

private theorem B10Congruence_pair_order
    {N : ℕ} {b c : ℝ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N b c) :
    rs.1 ≤ rs.2 := by
  have hrsData := mem_goldbachC10Pairs_iff.mp hrs
  exact_mod_cast le_trans hrsData.2.2.2.2.1 hrsData.2.2.2.2.2.1

/-- On the corrected `C10` carrier, the ordered prime-factor label `rs ↦ r*s`
is injective, even when `r = s`. -/
theorem goldbachC10Prod_injOn
    {N : ℕ} {b c : ℝ} :
    Set.InjOn goldbachC10Prod (goldbachC10Pairs N b c) := by
  intro rs hrs tu htu hprod
  rcases rs with ⟨r, s⟩
  rcases tu with ⟨t, u⟩
  have hrsData := mem_goldbachC10Pairs_iff.mp hrs
  have htuData := mem_goldbachC10Pairs_iff.mp htu
  have hrsLe : r ≤ s := B10Congruence_pair_order hrs
  have htuLe : t ≤ u := B10Congruence_pair_order htu
  dsimp [goldbachC10Prod] at hprod ⊢
  have hrdvd : r ∣ t * u := by
    rw [← hprod]
    exact dvd_mul_right r s
  have hrEq : r = t ∨ r = u := by
    rcases hrsData.1.dvd_mul.mp hrdvd with hrt | hru
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hrsData.1 htuData.1).mp hrt)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hrsData.1 htuData.2.1).mp hru)
  rcases hrEq with rfl | hru
  · have hrpos : 0 < r := hrsData.1.pos
    have : s = u := Nat.mul_left_cancel hrpos hprod
    simp [this]
  · have hrpos : 0 < r := hrsData.1.pos
    rw [← hru, mul_comm r s] at hprod
    have hsEq : s = t := Nat.mul_right_cancel hrpos hprod
    have hsr : s ≤ r := by
      simpa [hsEq, hru] using htuLe
    have hrst : r = s := le_antisymm hrsLe hsr
    have hut : u = t := by
      calc
        u = r := hru.symm
        _ = s := hrst
        _ = t := hsEq
    have hrt : r = t := by
      calc
        r = s := hrst
        _ = t := hsEq
    simp [hrt, hsEq, hut]

/-- The literal `C10` coefficient `α(m)` is at most `1`. -/
theorem goldbachC10Coeff_le_one
    {N : ℕ} {b c : ℝ} {m : ℕ} :
    goldbachC10Coeff N b c m ≤ 1 := by
  let A := goldbachC10ProductFiber N b c m
  have hmap : Set.MapsTo goldbachC10Prod A ({m} : Finset ℕ) := by
    intro rs hrs
    exact Finset.mem_singleton.mpr (mem_goldbachC10ProductFiber_iff.mp hrs).2
  have hinj : Set.InjOn goldbachC10Prod A := by
    intro rs hrs tu htu hEq
    exact goldbachC10Prod_injOn
      (N := N) (b := b) (c := c)
      (show rs ∈ goldbachC10Pairs N b c from (mem_goldbachC10ProductFiber_iff.mp hrs).1)
      (show tu ∈ goldbachC10Pairs N b c from (mem_goldbachC10ProductFiber_iff.mp htu).1)
      hEq
  have hcard : A.card ≤ ({m} : Finset ℕ).card := Finset.card_le_card_of_injOn _ hmap hinj
  simpa [goldbachC10Coeff, A] using hcard

private theorem B10Congruence_prod_pos_of_pair_mem
    {N : ℕ} {b c : ℝ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N b c) :
    0 < goldbachC10Prod rs := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, _⟩
  exact Nat.mul_pos hrPrime.pos hsPrime.pos

/-- A genuine labelled `B10` atom always satisfies the strict product bound
`mq < N`. -/
theorem goldbachB10Atom_prod_lt
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachB10Atoms N ε b c) :
    goldbachC10Prod x.1 * x.2 < N := by
  rcases mem_goldbachB10Atoms_iff.mp hx with ⟨hrsMem, _, _, _, hqUpper⟩
  have hmpos : 0 < goldbachC10Prod x.1 := B10Congruence_prod_pos_of_pair_mem hrsMem
  have hmposReal : 0 < (goldbachC10Prod x.1 : ℝ) := by exact_mod_cast hmpos
  have hreal : (x.2 : ℝ) * (goldbachC10Prod x.1 : ℝ) < N := by
    rw [lt_div_iff₀ hmposReal] at hqUpper
    simpa [mul_comm] using hqUpper
  have hnat : x.2 * goldbachC10Prod x.1 < N := by
    exact_mod_cast hreal
  simpa [goldbachC10Prod, mul_comm] using hnat

theorem goldbachB10Atom_output_eq_sub
    (N : ℕ) (x : Σ _rs : ℕ × ℕ, ℕ) :
    goldbachPi10Output N x = N - goldbachC10Prod x.1 * x.2 := by
  rfl

/-- For an actual labelled `B10` atom, the literal output `p = N - mq`
reconstructs `N` exactly as `mq + p = N`. -/
theorem goldbachB10Atom_prod_add_output
    {N : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachB10Atoms N ε b c) :
    goldbachC10Prod x.1 * x.2 + goldbachPi10Output N x = N := by
  have hlt : goldbachC10Prod x.1 * x.2 < N := goldbachB10Atom_prod_lt hx
  rw [goldbachB10Atom_output_eq_sub]
  omega

/-- On a genuine labelled `B10` atom, divisibility of the output `p = N - mq`
is equivalent to the natural-number congruence `mq ≡ N (mod d)`. -/
theorem goldbachB10Atom_output_dvd_iff_modEq
    {N d : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (_hd : 1 ≤ d)
    (hx : x ∈ goldbachB10Atoms N ε b c) :
    d ∣ goldbachPi10Output N x ↔ Nat.ModEq d (goldbachC10Prod x.1 * x.2) N := by
  have hle : goldbachC10Prod x.1 * x.2 ≤ N := (goldbachB10Atom_prod_lt hx).le
  rw [goldbachB10Atom_output_eq_sub, Nat.modEq_iff_dvd' hle]

/-- If the actual output `p = N - mq` is divisible by `d` and `d` is coprime to
`N`, then the product label `m = rs` is automatically coprime to `d`. -/
theorem goldbachB10Atom_prod_coprime_of_coprime_modulus
    {N d : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (_hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hx : x ∈ goldbachB10Atoms N ε b c)
    (hdp : d ∣ goldbachPi10Output N x) :
    Nat.Coprime (goldbachC10Prod x.1) d := by
  apply Nat.coprime_of_dvd'
  intro p hpPrime hpm hpd
  have hpp : p ∣ goldbachPi10Output N x := dvd_trans hpd hdp
  have hmq : p ∣ goldbachC10Prod x.1 * x.2 := dvd_mul_of_dvd_left hpm x.2
  have hN : p ∣ N := by
    simpa [goldbachB10Atom_prod_add_output hx] using Nat.dvd_add hmq hpp
  exact (prime_not_dvd_of_coprime hdN hpPrime hpd hN).elim

/-- The exact residue-class condition on a divisor fibre of genuine labelled
`B10` atoms. -/
def goldbachB10DivisorResidueCondition
    (N d : ℕ) (x : Σ _rs : ℕ × ℕ, ℕ) : Prop :=
  Nat.Coprime (goldbachC10Prod x.1) d ∧
    ((x.2 : ZMod d) = (N : ZMod d) * (goldbachC10Prod x.1 : ZMod d)⁻¹)

/-- On the actual divisor fibre with `d ≥ 1` and `(d, N) = 1`, divisibility of
the output `p = N - mq` is equivalent to the precise coprimality-plus-inverse
residue condition on the same label `((r,s),q)`. -/
theorem goldbachB10Atom_output_dvd_iff_residueCondition
    {N d : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hx : x ∈ goldbachB10Atoms N ε b c) :
    d ∣ goldbachPi10Output N x ↔ goldbachB10DivisorResidueCondition N d x := by
  constructor
  · intro hdp
    have hcopr :
        Nat.Coprime (goldbachC10Prod x.1) d :=
      goldbachB10Atom_prod_coprime_of_coprime_modulus hd hdN hx hdp
    have hmod : Nat.ModEq d (goldbachC10Prod x.1 * x.2) N :=
      (goldbachB10Atom_output_dvd_iff_modEq hd hx).mp hdp
    have hzprod :
        (((goldbachC10Prod x.1 * x.2 : ℕ) : ZMod d)) = (N : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff (goldbachC10Prod x.1 * x.2) N d).2 hmod
    have hzmul :
        ((goldbachC10Prod x.1 : ZMod d) * (x.2 : ZMod d)) = (N : ZMod d) := by
      simpa using hzprod
    refine ⟨hcopr, ?_⟩
    calc
      (x.2 : ZMod d) = (1 : ZMod d) * (x.2 : ZMod d) := by simp
      _ = (((goldbachC10Prod x.1 : ZMod d) * (goldbachC10Prod x.1 : ZMod d)⁻¹) *
            (x.2 : ZMod d)) := by
              rw [← ZMod.coe_mul_inv_eq_one (goldbachC10Prod x.1) hcopr]
      _ = (goldbachC10Prod x.1 : ZMod d)⁻¹ *
            ((goldbachC10Prod x.1 : ZMod d) * (x.2 : ZMod d)) := by
              ac_rfl
      _ = (goldbachC10Prod x.1 : ZMod d)⁻¹ * (N : ZMod d) := by rw [hzmul]
      _ = (N : ZMod d) * (goldbachC10Prod x.1 : ZMod d)⁻¹ := by
            simp [mul_comm]
  · rintro ⟨hcopr, hqeq⟩
    have hzmul :
        ((goldbachC10Prod x.1 : ZMod d) * (x.2 : ZMod d)) = (N : ZMod d) := by
      calc
        (goldbachC10Prod x.1 : ZMod d) * (x.2 : ZMod d)
            = (goldbachC10Prod x.1 : ZMod d) *
                ((N : ZMod d) * (goldbachC10Prod x.1 : ZMod d)⁻¹) := by
                  rw [hqeq]
        _ = (N : ZMod d) *
              ((goldbachC10Prod x.1 : ZMod d) * (goldbachC10Prod x.1 : ZMod d)⁻¹) := by
                ac_rfl
        _ = (N : ZMod d) * 1 := by
              rw [ZMod.coe_mul_inv_eq_one (goldbachC10Prod x.1) hcopr]
        _ = (N : ZMod d) := by simp
    have hzprod :
        (((goldbachC10Prod x.1 * x.2 : ℕ) : ZMod d)) = (N : ZMod d) := by
      simpa using hzmul
    have hmod : Nat.ModEq d (goldbachC10Prod x.1 * x.2) N :=
      (ZMod.natCast_eq_natCast_iff (goldbachC10Prod x.1 * x.2) N d).1 hzprod
    exact (goldbachB10Atom_output_dvd_iff_modEq hd hx).mpr hmod

/-- The labelled divisor fibre inside the genuine finite `B10` atoms. -/
noncomputable def goldbachB10DivisorAtoms
    (N d : ℕ) (ε b c : ℝ) : Finset (Σ _rs : ℕ × ℕ, ℕ) :=
  (goldbachB10Atoms N ε b c).filter fun x => d ∣ goldbachPi10Output N x

theorem mem_goldbachB10DivisorAtoms_iff
    {N d : ℕ} {ε b c : ℝ} {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB10DivisorAtoms N d ε b c ↔
      x ∈ goldbachB10Atoms N ε b c ∧ d ∣ goldbachPi10Output N x := by
  simp [goldbachB10DivisorAtoms]

/-- On each labelled atom, the divisor filter can be replaced exactly by the
coprimality-plus-inverse residue condition from
`goldbachB10Atom_output_dvd_iff_residueCondition`. -/
theorem goldbachB10DivisorAtoms_eq_residueFilter
    {N d : ℕ} {ε b c : ℝ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N) :
    goldbachB10DivisorAtoms N d ε b c =
      (goldbachB10Atoms N ε b c).filter
        (goldbachB10DivisorResidueCondition N d) := by
  ext x
  constructor
  · intro hx
    rcases mem_goldbachB10DivisorAtoms_iff.mp hx with ⟨hxB10, hdiv⟩
    exact Finset.mem_filter.mpr
      ⟨hxB10, (goldbachB10Atom_output_dvd_iff_residueCondition hd hdN hxB10).mp hdiv⟩
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxB10, hcond⟩
    exact mem_goldbachB10DivisorAtoms_iff.mpr
      ⟨hxB10, (goldbachB10Atom_output_dvd_iff_residueCondition hd hdN hxB10).mpr hcond⟩

theorem goldbachB10DivisorAtoms_card_eq_residueFilter_card
    {N d : ℕ} {ε b c : ℝ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N) :
    (goldbachB10DivisorAtoms N d ε b c).card =
      ((goldbachB10Atoms N ε b c).filter
        (goldbachB10DivisorResidueCondition N d)).card := by
  rw [goldbachB10DivisorAtoms_eq_residueFilter hd hdN]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig