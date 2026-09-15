import Wu08SmallGridGeometry

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace Wu08FirstPrimeFour.SmallGrid
open Normalization

abbrev GridAtom := Σ _k : Key, Long × ℕ

def gridAtoms (N : ℕ) (e : Bool) (ξ ρ : ℝ) : Finset GridAtom :=
  (occupied N e ξ ρ).sigma fun k => (longCell N e ξ ρ k) ×ˢ shortCell ρ k

/-- A literal enlarged finite labelled carrier, not a mass-bound premise.
The last long coordinate remains any nonunit b-rough integer. Coprimality
and primality of the short a remain in the actual beta factor. -/
def relaxedAtoms (N : ℕ) (e : Bool) (ρ : ℝ) : Finset (Long × ℕ) :=
  (longLabels N e ×ˢ range (⌈ρ*(N : ℝ)^(1/10 : ℝ)⌉₊+1)).filter fun p =>
    LastPrimeFour.z N/ρ ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ ρ*(N : ℝ)^(1/10 : ℝ) ∧
    (p.2 : ℝ) < ρ*p.1.1 ∧ (p.2 : ℝ)*(longProduct p.1 : ℝ) < ρ*N

def relaxedMass (N : ℕ) (e : Bool) (ρ ε : ℝ) : ℝ :=
  ∑ p ∈ relaxedAtoms N e ρ, (atomWeight N p.2+ε)*beta N p.2

theorem occupied_big {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hlarge : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2)
    {k : Key} (hk : k ∈ occupied N e ξ ρ) : 3 ≤ ρ^k.1 := by
  have hh := (occupied_geometry hξ hρ hρu hk).2.2.2.1
  linarith

theorem gridAtoms_injective {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hlarge : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2) :
    Set.InjOn (fun p : GridAtom => p.2) (gridAtoms N e ξ ρ) := by
  rintro ⟨k,t,a⟩ hx ⟨l,u,b⟩ hy h
  have hp : (t,a)=(u,b) := h
  cases hp
  obtain ⟨hk,hta⟩ := mem_sigma.mp hx
  obtain ⟨hl,hub⟩ := mem_sigma.mp hy
  obtain ⟨htk,hak⟩ := mem_product.mp hta
  obtain ⟨htl,hal⟩ := mem_product.mp hub
  have he := rectangle_key_unique hρ hρu (occupied_big hξ hρ hρu hlarge hk)
    (occupied_big hξ hρ hρu hlarge hl) htk htl hak hal
  change k=l at he
  subst l
  rfl

theorem gridAtoms_maps {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hlarge : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2) :
    (gridAtoms N e ξ ρ).image (fun p : GridAtom => p.2) ⊆ relaxedAtoms N e ρ := by
  rintro p hp
  obtain ⟨⟨k,t,a⟩,hx,rfl⟩ := mem_image.mp hp
  obtain ⟨hk,hta⟩ := mem_sigma.mp hx
  obtain ⟨ht,ha⟩ := mem_product.mp hta
  obtain ⟨hl,hu,hab,hprod,_⟩ := rectangle_faces hρ hρu hk
    (occupied_big hξ hρ hρu hlarge hk) ht ha
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨(mem_filter.mp ht).1,?_⟩,hl,hu.le,hab,hprod⟩
  have hceil : a ≤ ⌈ρ*(N : ℝ)^(1/10 : ℝ)⌉₊ := by
    exact_mod_cast hu.le.trans (Nat.le_ceil _)
  exact mem_range.mpr (Nat.lt_succ_of_le hceil)

/-- Actual occupied-grid normalization is transported with its full labels.
No output deduplication, unweighted-eight replacement, or mass hypothesis. -/
theorem gridMass_le_relaxed {N : ℕ} {e : Bool} {ξ ρ ε : ℝ}
    (hN : (4 : ℝ) ≤ N) (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hlarge : 4 ≤ (N : ℝ)^truncatedSixthLowerAlpha/2) (hε : 0 ≤ ε) :
    weightedGridMass N e ξ ρ+ε*plainGridMass N e ξ ρ ≤ relaxedMass N e ρ ε := by
  have heq : weightedGridMass N e ξ ρ+ε*plainGridMass N e ξ ρ =
      ∑ p ∈ gridAtoms N e ξ ρ, (cellWeight N ρ p.1+ε)*beta N p.2.2 := by
    unfold weightedGridMass plainGridMass
    rw [mul_sum,← sum_add_distrib]
    simp_rw [← add_mul,cellMass_labels,mul_sum]
    simp only [gridAtoms,sum_sigma,sum_product]
  rw [heq]
  calc
    _ ≤ ∑ p ∈ gridAtoms N e ξ ρ, (atomWeight N p.2.2+ε)*beta N p.2.2 := by
      apply sum_le_sum
      rintro ⟨k,t,a⟩ hp
      obtain ⟨hk,hta⟩ := mem_sigma.mp hp
      exact mul_le_mul_of_nonneg_right (add_le_add
        (cellWeight_le_atomWeight hN hξ hρ hρu hk (occupied_big hξ hρ hρu hlarge hk)
          (mem_product.mp hta).2) (le_refl ε)) (beta_nonneg N a)
    _ = ∑ p ∈ (gridAtoms N e ξ ρ).image (fun p : GridAtom => p.2),
        (atomWeight N p.2+ε)*beta N p.2 := by
      rw [sum_image (gridAtoms_injective hξ hρ hρu hlarge)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (gridAtoms_maps hξ hρ hρu hlarge)
      (fun p _ _ => mul_nonneg (add_nonneg (atomWeight_nonneg N p.2) hε) (beta_nonneg N p.2))

#print axioms gridAtoms_injective
#print axioms gridMass_le_relaxed
end Wu08FirstPrimeFour.SmallGrid
