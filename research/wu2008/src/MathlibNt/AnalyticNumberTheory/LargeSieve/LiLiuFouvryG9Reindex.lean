import MathlibNt.SieveTheory.LiLiuGoldbachB9LowPositivePrefixTransport
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectC2

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Keep the second prime as a label after grouping the long product. -/
def fouvryG9Coordinates (x : Σ _rs : ℕ × ℕ, ℕ) : ℕ × ℕ × ℕ :=
  (x.1.2 * x.2, x.1.2, x.1.1)

def fouvryG9Carrier (N : ℕ) (eps : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (goldbachB9LowPositivePrefixAtoms N eps).image fouvryG9Coordinates

theorem fouvryG9Coordinates_injOn (N : ℕ) (eps : ℝ) :
    Set.InjOn fouvryG9Coordinates (goldbachB9LowPositivePrefixAtoms N eps : Set _) := by
  intro x hx y hy he
  have hxB := (mem_goldbachB9LowPositivePrefixAtoms_iff.mp hx).1
  have hxp := mem_goldbachC10Pairs_iff.mp (mem_goldbachB10Atoms_iff.mp hxB).1
  have hs : x.1.2 = y.1.2 := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) he
  have hr : x.1.1 = y.1.1 := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) he
  have hp : x.1.2 * x.2 = y.1.2 * y.2 := congrArg Prod.fst he
  have ht : x.2 = y.2 := by
    rw [← hs] at hp
    exact Nat.eq_of_mul_eq_mul_left hxp.2.1.pos hp
  obtain ⟨⟨r,s⟩,t⟩ := x
  obtain ⟨⟨r',s'⟩,t'⟩ := y
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at *
  subst r'; subst s'; subst t'
  exact ⟨⟨rfl,rfl⟩,HEq.rfl⟩

/-- Arbitrary kernels can be reindexed without merging two possible prime labels. -/
theorem fouvryG9_sum_reindex (N : ℕ) (eps : ℝ) (F : ℕ → ℕ → ℝ) :
    (∑ x ∈ goldbachB9LowPositivePrefixAtoms N eps, F x.1.1 (x.1.2*x.2)) =
      ∑ y ∈ fouvryG9Carrier N eps, F y.2.2 y.1 := by
  rw [fouvryG9Carrier, sum_image (fouvryG9Coordinates_injOn N eps)]
  rfl

theorem fouvryG9Carrier_geometry {N : ℕ} {eps : ℝ} {y : ℕ × ℕ × ℕ}
    (hy : y ∈ fouvryG9Carrier N eps) :
    y.2.1.Prime ∧ y.2.2.Prime ∧ y.2.1 ∣ y.1 ∧
    (y.1 / y.2.1).Prime ∧ (y.2.2*y.2.1).Coprime N ∧
    (N : ℝ)^(4/53 : ℝ) ≤ y.2.2 ∧ (y.2.2 : ℝ) < (N : ℝ)^(1/10 : ℝ) ∧
    (N : ℝ)^(1/3 : ℝ) ≤ y.2.1 ∧ y.2.2*y.2.1^2 ≤ N ∧
    eps*(N : ℝ) < (y.2.2*y.1 : ℕ) ∧ (y.2.2*y.1 : ℕ) < N := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
  obtain ⟨hxB,hlo⟩ := mem_goldbachB9LowPositivePrefixAtoms_iff.mp hx
  have hpair := mem_goldbachC10Pairs_iff.mp (mem_goldbachB10Atoms_iff.mp hxB).1
  obtain ⟨ht,heps,hupper⟩ := goldbachB9LowPositivePrefixAtoms_product_window hx
  refine ⟨hpair.2.1,hpair.1,⟨x.2,rfl⟩,?_,hpair.2.2.1,hpair.2.2.2.1,
    hlo,hpair.2.2.2.2.2.1,hpair.2.2.2.2.2.2,?_,?_⟩
  · simpa only [fouvryG9Coordinates, Nat.mul_div_right _ hpair.2.1.pos] using ht
  · simpa only [fouvryG9Coordinates, Nat.mul_assoc] using heps
  · have hnat : (x.1.1*x.1.2)*x.2 < N := by exact_mod_cast hupper
    simpa only [fouvryG9Coordinates, Nat.mul_assoc] using hnat

/-- The actual long-coordinate weight never exceeds the number of divisors. -/
def fouvryG9Multiplicity (N : ℕ) (eps : ℝ) (n m : ℕ) : ℕ :=
  ((fouvryG9Carrier N eps).filter (fun y => y.1=m ∧ y.2.2=n)).card

theorem fouvryG9Multiplicity_le_divisors (N : ℕ) (eps : ℝ) (n m : ℕ) :
    fouvryG9Multiplicity N eps n m ≤ m.divisors.card := by
  classical
  unfold fouvryG9Multiplicity
  apply card_le_card_of_injOn (fun y => y.2.1)
  · intro y hy
    obtain ⟨hy,hm,hn⟩ := mem_filter.mp hy
    have hg := fouvryG9Carrier_geometry hy
    apply Nat.mem_divisors.mpr
    refine ⟨hm ▸ hg.2.2.1, ?_⟩
    intro hz
    have hp := hg.2.2.2.1
    rw [hm,hz, Nat.zero_div] at hp
    exact Nat.not_prime_zero hp
  · intro x hx y hy he
    obtain ⟨_,hxm,hxn⟩ := mem_filter.mp hx
    obtain ⟨_,hym,hyn⟩ := mem_filter.mp hy
    exact Prod.ext (hxm.trans hym.symm) (Prod.ext he (hxn.trans hyn.symm))

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
