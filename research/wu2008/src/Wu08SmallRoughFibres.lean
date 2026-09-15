import Wu08SmallGridEpsilon

noncomputable section
open Finset Real LiLiuPrereqBuchstab
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace Wu08FirstPrimeFour.SmallGrid
open Normalization

abbrev Quad := ℕ × ℕ × ℕ × ℕ

def quadOf (p : Long × ℕ) : Quad := (p.2,p.1.1,p.1.2.1,p.1.2.2.1)
def quadProduct (q : Quad) : ℕ := q.1*q.2.1*q.2.2.1*q.2.2.2
def relaxedQuads (N : ℕ) (e : Bool) (ρ : ℝ) : Finset Quad :=
  (relaxedAtoms N e ρ).image quadOf
def roughX (N : ℕ) (ρ : ℝ) (q : Quad) : ℝ := ρ*N/(quadProduct q : ℝ)
def roughFibre (N : ℕ) (ρ : ℝ) (q : Quad) : Finset ℕ :=
  (roughNumbers (roughX N ρ q) q.2.1).erase 1
def quadWeight (N : ℕ) (ε : ℝ) (q : Quad) : ℝ :=
  (atomWeight N q.1+ε)*beta N q.1
def roughMass (N : ℕ) (e : Bool) (ρ ε : ℝ) : ℝ :=
  ∑ q ∈ relaxedQuads N e ρ, quadWeight N ε q*(roughFibre N ρ q).card

theorem relaxed_data {N : ℕ} {e : Bool} {ρ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ)
    {p : Long × ℕ} (hp : p ∈ relaxedAtoms N e ρ) :
    0 < p.2 ∧ p.1.1.Prime ∧ p.1.2.1.Prime ∧ p.1.2.2.1.Prime ∧
    1 < p.1.2.2.2 ∧ Rough (p.1.1 : ℝ) p.1.2.2.2 ∧
    0 < quadProduct (quadOf p) ∧ p.1.2.2.2 ∈ roughFibre N ρ (quadOf p) := by
  obtain ⟨hp,hz,_,_,hprod⟩ := mem_filter.mp hp
  obtain ⟨ht,_⟩ := mem_product.mp hp
  obtain ⟨_,hb,_,hc,_,hd,_,_,_,_,_,_,hn,hr⟩ := mem_filter.mp ht
  have hzpos : 0 < LastPrimeFour.z N/ρ :=
    div_pos (rpow_pos_of_pos (by linarith) _) (by linarith)
  have ha : 0 < p.2 := by exact_mod_cast hzpos.trans_le hz
  have hD : 0 < quadProduct (quadOf p) := by
    unfold quadProduct quadOf
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha hb.pos) hc.pos) hd.pos
  refine ⟨ha,hb,hc,hd,hn,hr,hD,?_⟩
  apply mem_erase.mpr
  refine ⟨by omega,mem_roughNumbers.mpr ⟨by omega,?_,hr⟩⟩
  unfold roughX
  apply (le_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < quadProduct (quadOf p))).mpr
  have he : (p.1.2.2.2 : ℝ)*(quadProduct (quadOf p) : ℝ) =
      (p.2 : ℝ)*(longProduct p.1 : ℝ) := by
    simp only [quadProduct,quadOf,longProduct,Nat.cast_mul]
    ring
  exact he.trans_le hprod.le

/-- The rough fibre injection keeps n itself and all four ordered labels. -/
theorem fibre_card_le {N : ℕ} {e : Bool} {ρ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (q : Quad) :
    ((relaxedAtoms N e ρ).filter fun p => quadOf p=q).card ≤ (roughFibre N ρ q).card := by
  apply card_le_card_of_injOn (fun p : Long × ℕ => p.1.2.2.2)
  · intro p hp
    obtain ⟨hp,he⟩ := mem_filter.mp hp
    change p.1.2.2.2 ∈ roughFibre N ρ q
    simpa only [he] using (relaxed_data hN hρ hp).2.2.2.2.2.2.2
  · rintro ⟨⟨b,c,d,n⟩,a⟩ hp ⟨⟨b',c',d',n'⟩,a'⟩ hp' hn
    have he := (mem_filter.mp hp).2.trans (mem_filter.mp hp').2.symm
    change (a,b,c,d)=(a',b',c',d') at he
    have ha := congrArg Prod.fst he
    have hb := congrArg (fun q : Quad => q.2.1) he
    have hc := congrArg (fun q : Quad => q.2.2.1) he
    have hd := congrArg (fun q : Quad => q.2.2.2) he
    dsimp only at ha hb hc hd
    change n=n' at hn
    subst a'; subst b'; subst c'; subst d'; subst n'
    rfl

/-- A genuine arithmetic upper bound: all long rough integers have been
collected into ordinary nonunit roughNumber counts, without primality of n. -/
theorem relaxedMass_le_roughMass {N : ℕ} {e : Bool} {ρ ε : ℝ}
    (hN : (4 : ℝ) ≤ N) (hρ : 1 < ρ) (hε : 0 ≤ ε) :
    relaxedMass N e ρ ε ≤ roughMass N e ρ ε := by
  have he := sum_fiberwise_of_maps_to' (s := relaxedAtoms N e ρ)
    (t := relaxedQuads N e ρ) (g := quadOf)
    (fun p hp => mem_image_of_mem quadOf hp) (quadWeight N ε)
  change (∑ q ∈ relaxedQuads N e ρ, ∑ _p ∈ (relaxedAtoms N e ρ).filter (fun p => quadOf p=q),
    quadWeight N ε q) = relaxedMass N e ρ ε at he
  rw [← he]
  unfold roughMass
  apply sum_le_sum
  intro q _
  rw [sum_const,nsmul_eq_mul,mul_comm]
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast fibre_card_le hN hρ q
  · exact mul_nonneg (add_nonneg (atomWeight_nonneg N q.1) hε) (beta_nonneg N q.1)

#print axioms fibre_card_le
#print axioms relaxedMass_le_roughMass
end Wu08FirstPrimeFour.SmallGrid
