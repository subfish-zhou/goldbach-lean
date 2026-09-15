import HighConsumerMother
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureAssembly
import Mathlib.Data.Nat.Pairing

namespace MixedSixth
open Finset Real Wu2008DoubleSieve
open scoped Classical
noncomputable section

/-- The original coarse cells, with their original two integer coordinates. -/
def coarse (i : ℕ) : ℕ × ℕ := Nat.unpair i

def loX (n i : ℕ) : ℝ := truncatedSixthClosureLo n (coarse i).1
def hiX (n i : ℕ) : ℝ := truncatedSixthClosureHi n (coarse i).1
def loY (n i : ℕ) : ℝ := truncatedSixthClosureLo n (coarse i).2
def hiY (n i : ℕ) : ℝ := truncatedSixthClosureHi n (coarse i).2

def lowCells (δ : ℝ) (n : ℕ) : Finset ℕ :=
  (truncatedSixthClosureInner true δ n).image (fun j => Nat.pair j.1 j.2)

/-- The high cells are selected by their lower quarter boundary and their
upper retained-polygon corner; no arbitrary small high subdomain is used. -/
def highCells (δ : ℝ) (n : ℕ) : Finset ℕ :=
  ((truncatedSixthClosureCells n).filter (fun j =>
    truncatedSixthLowerAlpha ≤ truncatedSixthClosureLo n j.1 ∧
    (1:ℝ)/4 ≤ truncatedSixthClosureLo n j.2 ∧
    truncatedSixthLowerRegion δ (truncatedSixthClosureHi n j.1)
      (truncatedSixthClosureHi n j.2))).image (fun j => Nat.pair j.1 j.2)

/-- Each coarse cell is filled with the existing exact shrinking prime grid. -/
def fineCells (N n i : ℕ) : Finset ℕ :=
  (truncatedSixthMassPacking N (loX n i) (hiX n i) (loY n i) (hiY n i)).image
    (fun j => Nat.pair j.1 j.2)

def packing (N n : ℕ) (K : Finset ℕ) : Finset ℕ :=
  K.biUnion (fun i => (fineCells N n i).image (Nat.pair i))

def outer (k : ℕ) : ℕ := (Nat.unpair k).1
def inner (k : ℕ) : ℕ × ℕ := Nat.unpair (Nat.unpair k).2

def x (N n k : ℕ) : ℝ :=
  truncatedSixthMassGridPoint N (loX n (outer k)) ((inner k).1+1)
def y (N n k : ℕ) : ℝ :=
  truncatedSixthMassGridPoint N (loY n (outer k)) ((inner k).2+1)
def sourceS (δ : ℝ) (n k : ℕ) : ℝ :=
  truncatedSixthLowerS δ (hiX n (outer k)) (hiY n (outer k))
def lowNodes (δ : ℝ) (n : ℕ) : Finset ℝ :=
  (lowCells δ n).image (fun i => truncatedSixthLowerS δ (hiX n i) (hiY n i))

theorem packing_mem {N n k : ℕ} {K : Finset ℕ} (hk : k ∈ packing N n K) :
    outer k ∈ K ∧ inner k ∈
      truncatedSixthMassPacking N (loX n (outer k)) (hiX n (outer k))
        (loY n (outer k)) (hiY n (outer k)) := by
  obtain ⟨i,hi,hk⟩ := mem_biUnion.mp hk
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
  simpa only [outer,inner,Nat.unpair_pair] using And.intro hi hp

theorem packing_encode {N n i : ℕ} {p : ℕ × ℕ} {K : Finset ℕ}
    (hi : i ∈ K) (hp : p ∈ truncatedSixthMassPacking N
      (loX n i) (hiX n i) (loY n i) (hiY n i)) :
    Nat.pair i (Nat.pair p.1 p.2) ∈ packing N n K := by
  apply mem_biUnion.mpr
  exact ⟨i,hi,mem_image.mpr ⟨Nat.pair p.1 p.2,mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩⟩

theorem low_geometry {δ : ℝ} {n i : ℕ} (hi : i ∈ lowCells δ n) :
    truncatedSixthLowerAlpha ≤ loX n i ∧
    truncatedSixthLowerBeta ≤ loY n i ∧
    truncatedSixthLowerAdmissibleRegion δ (hiX n i) (hiY n i) := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  have hg := truncatedSixthClosure_inner_geometry hj
  have hu : truncatedSixthLowerAdmissibleRegion δ
      (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2) :=
    (mem_filter.mp hj).2.2
  simpa only [loX,loY,hiX,hiY,coarse,Nat.unpair_pair] using ⟨hg.1,hg.2.1,hu⟩

theorem high_geometry {δ : ℝ} {n i : ℕ} (hi : i ∈ highCells δ n) :
    truncatedSixthLowerAlpha ≤ loX n i ∧ (1:ℝ)/4 ≤ loY n i ∧
      truncatedSixthLowerRegion δ (hiX n i) (hiY n i) := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
  simpa only [loX,loY,hiX,hiY,coarse,Nat.unpair_pair] using (mem_filter.mp hj).2

theorem fine_bounds {N n k : ℕ} {K : Finset ℕ} (hN : 1 < N)
    (hk : k ∈ packing N n K) :
    loX n (outer k) < x N n k ∧ x N n k ≤ hiX n (outer k) ∧
    loY n (outer k) < y N n k ∧ y N n k ≤ hiY n (outer k) := by
  have h := (packing_mem hk).2
  obtain ⟨hx,hy⟩ := mem_product.mp h
  have hbx := truncatedSixthMass_grid_point_bounds hN
    (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).1).le (mem_range.mp hx)
  have hby := truncatedSixthMass_grid_point_bounds hN
    (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).2).le (mem_range.mp hy)
  exact ⟨hbx.1.trans_lt (truncatedSixthMass_grid_point_mono hN _ (Nat.lt_succ_self _)),
    hbx.2,hby.1.trans_lt (truncatedSixthMass_grid_point_mono hN _ (Nat.lt_succ_self _)),hby.2⟩

theorem fine_lower_endpoints {N n k : ℕ} {K : Finset ℕ} (hN : 1 < N)
    (hk : k ∈ packing N n K) :
    (N:ℝ)^(loX n (outer k)) ≤ (N:ℝ)^(x N n k)/truncatedSixthMassDelta N ∧
    (N:ℝ)^(loY n (outer k)) ≤ (N:ℝ)^(y N n k)/truncatedSixthMassDelta N := by
  obtain ⟨hx,hy⟩ := mem_product.mp (packing_mem hk).2
  have hbx := truncatedSixthMass_grid_point_bounds hN
    (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).1).le (mem_range.mp hx)
  have hby := truncatedSixthMass_grid_point_bounds hN
    (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).2).le (mem_range.mp hy)
  dsimp only [x,y]
  rw [truncatedSixthMass_grid_lower_endpoint hN,truncatedSixthMass_grid_lower_endpoint hN]
  exact ⟨rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hbx.1,
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hby.1⟩

theorem physical_box_eq (N n k : ℕ) :
    truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x N n k) (y N n k) =
      truncatedSixthMassPackingBox N (loX n (outer k)) (loY n (outer k)) (inner k) := rfl

theorem physical_box_subset {N n k : ℕ} {K : Finset ℕ} (hN : 1 < N)
    (hk : k ∈ packing N n K) :
    truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x N n k) (y N n k) ⊆
      truncatedSixthClosurePairs N (loX n (outer k)) (hiX n (outer k))
        (loY n (outer k)) (hiY n (outer k)) :=
  truncatedSixthMass_packing_box_subset hN
    (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).1).le
    (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).2).le (packing_mem hk).2

theorem physical_pairwise {N n : ℕ} (hN : 1 < N) (K : Finset ℕ) :
    Set.PairwiseDisjoint (packing N n K : Set ℕ) (fun k =>
      truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x N n k) (y N n k)) := by
  intro i hi j hj hij
  change Disjoint (truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x N n i) (y N n i))
    (truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x N n j) (y N n j))
  by_cases ho : outer i = outer j
  · have hn : inner i ≠ inner j := by
      intro he
      apply hij
      apply Nat.pairEquiv.symm.injective
      apply Prod.ext ho
      exact Nat.pairEquiv.symm.injective he
    rw [physical_box_eq,physical_box_eq,ho]
    exact truncatedSixthMass_packing_disjoint hN _ _ hn
  · have hc : coarse (outer i) ≠ coarse (outer j) :=
      fun h => ho (Nat.pairEquiv.symm.injective h)
    exact (truncatedSixthClosure_grid_pairs_disjoint hN hc).mono
      (physical_box_subset hN hi) (physical_box_subset hN hj)

theorem lowNodes_bounds {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ∀ s ∈ lowNodes δ n, 2 ≤ s ∧ s ≤ 5 := by
  intro s hs
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
  exact (truncatedSixthLower_region_bounds hδ (low_geometry hi).2.2.1).2.2.2

/-- Concrete joint packing, for every symbolic coarse resolution and every N>1.
No packing existence, disjointness, cardinality or mass premise is supplied. -/
theorem actual_geometry {N : ℕ} {δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ) (n : ℕ) :
    HighConsumer.PackingGeometry N δ (truncatedSixthMassDelta N)
      (packing N n (lowCells δ n)) (packing N n (highCells δ n))
      (x N n) (y N n) (sourceS δ n) (x N n) (y N n) (sourceS δ n) (lowNodes δ n) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN.le
  have hlow (k : ℕ) (hk : k ∈ packing N n (lowCells δ n)) :=
    truncatedSixthMass_packing_admissible hN
      (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).1).le
      (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).2).le
      (low_geometry (packing_mem hk).1).1 (low_geometry (packing_mem hk).1).2.1
      (low_geometry (packing_mem hk).1).2.2 (packing_mem hk).2
  have hs (K : Finset ℕ) (k : ℕ) (hk : k ∈ packing N n K) :
      sourceS δ n k ≤ truncatedSixthLowerS δ (x N n k) (y N n k) := by
    exact truncatedSixthClosure_s_order (δ := δ)
      (l := (x N n k,y N n k)) (u := (hiX n (outer k),hiY n (outer k)))
      ⟨(fine_bounds hN hk).2.1,(fine_bounds hN hk).2.2.2⟩
  refine ⟨fun k hk => (hlow k hk).1,fun k hk => (hlow k hk).2.1,
    fun k hk => (hlow k hk).2.2,?_,physical_pairwise hN _,?_,?_,?_,?_,physical_pairwise hN _⟩
  · intro k hk
    exact ⟨mem_image.mpr ⟨outer k,(packing_mem hk).1,rfl⟩,hs _ k hk⟩
  · intro k hk
    have hg := high_geometry (packing_mem hk).1
    have hb := fine_bounds hN hk
    refine ⟨⟨hg.1.trans hb.1.le,hb.2.1.trans hg.2.2.2.1,?_,
      hb.2.2.2.trans hg.2.2.2.2.2.1,
      (add_le_add hb.2.1 hb.2.2.2).trans hg.2.2.2.2.2.2⟩,hg.2.1.trans_lt hb.2.2.1⟩
    exact (show truncatedSixthLowerBeta ≤ (1:ℝ)/4 by norm_num [truncatedSixthLowerBeta]).trans
      (hg.2.1.trans hb.2.2.1.le)
  · intro k hk
    exact (rpow_le_rpow_of_exponent_le hNR (high_geometry (packing_mem hk).1).1).trans
      (fine_lower_endpoints hN hk).1
  · intro k hk
    exact (rpow_le_rpow_of_exponent_le hNR (high_geometry (packing_mem hk).1).2.1).trans
      (fine_lower_endpoints hN hk).2
  · intro k hk
    have hg := high_geometry (packing_mem hk).1
    have hy : (1:ℝ)/4 < hiY n (outer k) := hg.2.1.trans_lt
      (truncatedSixthClosure_lo_lt_hi n (coarse (outer k)).2)
    exact ⟨(HighConsumer.high_source_bounds hδ hg.2.2 hy).1,
      (HighConsumer.high_source_bounds hδ hg.2.2 hy).2,hs _ k hk⟩

end
end MixedSixth
