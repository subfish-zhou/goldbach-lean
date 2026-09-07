import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramAggregateBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryResonanceDomain
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryResonanceBound

/-!
# Exact resonance fibers of occupied Gram labels

The base is `((r,n₁),h,n₂',s')`, and its fiber is `(n₂,s,h')`.
Both maps retain the common first beta coordinate and signed frequencies.
No diagonal restriction is imposed.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WGramResonanceBase := (ℕ × ℕ) × ℤ × ℕ × ℕ

def wGramResonanceBase (L : WGramLabel) : WGramResonanceBase :=
  (L.1, L.2.1.2.2, L.2.2.1, L.2.2.2.1)

def wGramResonanceTriple (L : WGramLabel) : ℕ × ℕ × ℤ :=
  (L.2.1.1, L.2.1.2.1, L.2.2.2.2)

def wGramResonanceJoin (v : WGramResonanceBase) (t : ℕ × ℕ × ℤ) : WGramLabel :=
  (v.1, (t.1, t.2.1, v.2.1), (v.2.2.1, v.2.2.2, t.2.2))

theorem wGramResonanceJoin_base_triple (L : WGramLabel) :
    wGramResonanceJoin (wGramResonanceBase L) (wGramResonanceTriple L) = L := rfl

def wGramZeroLabels (K : WExtractedKey) (a : ℤ)
    (V : Finset (WExtractedTuple × ℤ)) : Finset WGramLabel :=
  (wGramLabels V).filter (fun L => wGramNumerator K a L = 0)

def wGramResonanceBases (G : Finset WGramLabel) : Finset WGramResonanceBase :=
  G.image wGramResonanceBase

def wGramResonanceFiber (G : Finset WGramLabel) (v : WGramResonanceBase) :
    Finset (ℕ × ℕ × ℤ) :=
  (G.filter (fun L => wGramResonanceBase L = v)).image wGramResonanceTriple

theorem mem_wGramResonanceFiber {G : Finset WGramLabel}
    {v : WGramResonanceBase} {t : ℕ × ℕ × ℤ} :
    t ∈ wGramResonanceFiber G v ↔ wGramResonanceJoin v t ∈ G := by
  constructor
  · intro ht
    obtain ⟨L, hL, rfl⟩ := mem_image.mp ht
    obtain ⟨hL, hv⟩ := mem_filter.mp hL
    rw [← hv, wGramResonanceJoin_base_triple]
    exact hL
  · intro ht
    exact mem_image.mpr ⟨wGramResonanceJoin v t, mem_filter.mpr ⟨ht, rfl⟩, rfl⟩

/-- An exact finite reindexing, including every occupied base and triple. -/
theorem sum_wGramResonanceFiber {A : Type*} [AddCommMonoid A]
    (G : Finset WGramLabel) (F : WGramLabel → A) :
    ∑ L ∈ G, F L =
      ∑ v ∈ wGramResonanceBases G,
        ∑ t ∈ wGramResonanceFiber G v, F (wGramResonanceJoin v t) := by
  rw [show (∑ L ∈ G, F L) =
      ∑ v ∈ wGramResonanceBases G,
        ∑ L ∈ G.filter (fun L => wGramResonanceBase L = v), F L from
    (sum_fiberwise_of_maps_to
      (fun L hL => mem_image.mpr ⟨L, hL, rfl⟩) F).symm]
  apply sum_congr rfl
  intro v _
  rw [wGramResonanceFiber, sum_image]
  · apply sum_congr rfl
    intro L hL
    rw [← (mem_filter.mp hL).2, wGramResonanceJoin_base_triple]
  · intro L hL L' hL' he
    have hv := (mem_filter.mp hL).2.trans (mem_filter.mp hL').2.symm
    rw [← wGramResonanceJoin_base_triple L, ← wGramResonanceJoin_base_triple L',
      hv, he]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
