import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitLimit
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeUnitFinite

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSource
open Finset SecondFunctionalUnitPrimeFibre LiLiuPrereqBuchstab

/-- The literal five- and six-colour source words. -/
def word20 : List ℕ := [2,3,3,3,3]
def word21 : List ℕ := [3,3,3,3,3,3]

theorem dictionary20 : secondFunctionalMotherGammaWords 20 = [word20] := rfl
theorem dictionary21 : secondFunctionalMotherGammaWords 21 = [word21] := rfl

theorem partition20 (N d : ℕ) (a B c e f : ℝ) :
    FourPrimeUnit.prefixTerm true N d a B c e f word20 +
      FourPrimeUnit.prefixTerm false N d a B c e f word20 =
      secondFunctionalMotherGamma N d N a B c e f 20 := by
  rw [FourPrimeUnit.prefix_partition]
  simp [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords, word20]

theorem partition21 (N d : ℕ) (a B c e f : ℝ) :
    FourPrimeUnit.prefixTerm true N d a B c e f word21 +
      FourPrimeUnit.prefixTerm false N d a B c e f word21 =
      secondFunctionalMotherGamma N d N a B c e f 21 := by
  rw [FourPrimeUnit.prefix_partition]
  simp [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords, word21]

/-- Fixed-d labels retain both the whole prime list and the original sieve atom. -/
noncomputable def atoms (N d : ℕ) (a B c e f : ℝ) (cs : List ℕ) :
    Finset (Σ _ : List ℕ, ℕ) :=
  ((secondFunctionalMotherTuples (primeWindow N a f) cs.length).filter
    fun l => l.map (secondFunctionalMotherColour B c e) = cs).sigma
    (secondFunctionalFourPrimeUnitCarrier N d)

theorem atoms_card (N d : ℕ) (a B c e f : ℝ) (cs : List ℕ) :
    ((atoms N d a B c e f cs).card : ℝ) =
      FourPrimeUnit.prefixTerm true N d a B c e f cs := by
  simp [atoms, card_sigma, sum_filter, FourPrimeUnit.prefixTerm]

/-- Reassemble every retained prime coordinate, including the last prime. -/
def fullList {n : ℕ} {R : ℝ} (y : Σ _ : Fin n → primeSlabPrimes R, ℕ) : List ℕ :=
  List.ofFn (fun j => (y.1 j).val) ++ [y.2]

/-- Unit uniqueness is used only after the complete prime list has been recovered. -/
theorem atoms_unique {N d : ℕ} {a B c e f : ℝ} {cs : List ℕ}
    {x x' : Σ _ : List ℕ, ℕ}
    (hx : x ∈ atoms N d a B c e f cs) (hx' : x' ∈ atoms N d a B c e f cs)
    (hl : x.1 = x'.1) : x = x' := by
  rcases x with ⟨l,ell⟩
  rcases x' with ⟨l',ell'⟩
  dsimp at hl
  subst l'
  have h := (mem_sigma.mp hx).2
  have h' := (mem_sigma.mp hx').2
  have he := secondFunctionalFourPrimeUnit_unique h h'
    (FourPrimeUnit.carrier_le h) (FourPrimeUnit.carrier_le h')
  change ell = ell' at he
  subst ell'
  rfl

/-- Label-preserving embedding; its domain carries original source membership. -/
theorem injection_of_geometry {N d n : ℕ} {a B c e f R : ℝ} {cs : List ℕ}
    (S : Finset (Fin n → primeSlabPrimes R)) (j : Fin n)
    (geometry : ∀ x ∈ atoms N d a B c e f cs,
      ∃ y ∈ S.sigma (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g j).val f),
        fullList y = x.1) :
    ∃ E : (atoms N d a B c e f cs) ↪
        (S.sigma (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g j).val f)),
      ∀ x, fullList (E x).val = x.val.1 := by
  let T := S.sigma (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g j).val f)
  let chooseY (x : atoms N d a B c e f cs) : T :=
    ⟨(geometry x.val x.property).choose, (geometry x.val x.property).choose_spec.1⟩
  have hlist (x : atoms N d a B c e f cs) : fullList (chooseY x).val = x.val.1 :=
    (geometry x.val x.property).choose_spec.2
  have hinj : Function.Injective chooseY := by
    intro x x' he
    apply Subtype.ext
    apply atoms_unique x.property x'.property
    exact (hlist x).symm.trans ((congrArg (fun y : T => fullList y.val) he).trans (hlist x'))
  exact ⟨⟨chooseY,hinj⟩,hlist⟩

/-- Generic counting mechanism; both concrete geometry producers supply all witnesses. -/
theorem count_of_geometry {N d n : ℕ} {a B c e f R : ℝ} {cs : List ℕ}
    (S : Finset (Fin n → primeSlabPrimes R)) (j : Fin n)
    (geometry : ∀ x ∈ atoms N d a B c e f cs,
      ∃ y ∈ S.sigma (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g j).val f),
        fullList y = x.1) :
    FourPrimeUnit.prefixTerm true N d a B c e f cs ≤
      ∑ g ∈ S, ((physical (prefixProduct g) ((N : ℝ)/d) (g j).val f).card : ℝ) := by
  obtain ⟨E,_⟩ := injection_of_geometry S j geometry
  have hc := Fintype.card_le_of_injective E E.injective
  simp only [Fintype.card_coe] at hc
  rw [← atoms_card]
  have hc' : ((atoms N d a B c e f cs).card : ℝ) ≤
      (S.sigma (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g j).val f)).card :=
    by exact_mod_cast hc
  simpa [card_sigma] using hc'

theorem colour_two {B c e : ℝ} {p : ℕ}
    (h : secondFunctionalMotherColour B c e p = 2) : c ≤ (p : ℝ) ∧ (p : ℝ) < e := by
  unfold secondFunctionalMotherColour at h
  split_ifs at h <;> first | omega | constructor <;> linarith

theorem colour_three {B c e : ℝ} {p : ℕ}
    (h : secondFunctionalMotherColour B c e p = 3) : e ≤ (p : ℝ) := by
  unfold secondFunctionalMotherColour at h
  split_ifs at h <;> first | omega | linarith

/-- Source window membership, not a new gcd screen, supplies primality and the strict cap. -/
theorem slab_of_window {N p : ℕ} {R a t b : ℝ}
    (hR : 1 < R) (ht : 1/10 ≤ t) (hb : b ≤ 1/2)
    (hp : p ∈ primeWindow N a (R^b)) (hl : R^t ≤ (p : ℝ)) :
    p ∈ primeSlabPrimes R := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR.le
  apply (mem_primesIcc (Real.rpow_nonneg hR0 _)).mpr
  exact ⟨(mem_primeWindow.mp hp).1,
    (Real.rpow_le_rpow_of_exponent_le hR.le ht).trans hl,
    (mem_primeWindow.mp hp).2.2.2.le.trans (Real.rpow_le_rpow_of_exponent_le hR.le hb)⟩

/-- Literal closed physical membership follows from the actual unit equation at X=N/d. -/
theorem physical_of_unit {N d ell n q : ℕ} {R H : ℝ}
    (hd : 0 < d) (hH : 0 ≤ H) (g : Fin n → primeSlabPrimes R) (j : Fin n)
    (hp : q.Prime) (hq : (g j).val < q) (hcap : (q : ℝ) ≤ H)
    (hu : ell ∈ secondFunctionalFourPrimeUnitCarrier N d (fullList ⟨g,q⟩)) :
    q ∈ physical (prefixProduct g) ((N : ℝ)/d) (g j).val H := by
  have he := (mem_filter.mp hu).2
  have hn : d * (fullList ⟨g,q⟩).prod ≤ N := he.symm.trans_le (Nat.sub_le _ _)
  have hr : (d : ℝ) * ((fullList ⟨g,q⟩).prod : ℝ) ≤ N := by exact_mod_cast hn
  have hprod : ((fullList ⟨g,q⟩).prod : ℝ) = prefixProduct g * q := by
    simp [fullList, List.prod_ofFn, prefixProduct, Nat.cast_prod]
  rw [hprod] at hr
  apply mem_filter.mpr
  refine ⟨(mem_primesIcc hH).mpr ⟨hp, Nat.cast_nonneg _, hcap⟩, ?_, ?_⟩
  · exact_mod_cast hq
  · apply (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
    simpa [mul_comm] using hr

end Wu2008DoubleSieve.HighUnitSource
