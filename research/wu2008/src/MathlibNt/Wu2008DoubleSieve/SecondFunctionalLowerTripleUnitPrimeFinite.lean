import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughMassFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimePrefixAsymptotics

namespace Wu2008DoubleSieve.LowerTripleGroupedUnit
open Finset LiLiuPrereqBuchstab LowerTripleGroupedFinite
open scoped Classical

abbrev Pair := ℕ × ℕ

/-- Both original prime windows, their copN conditions, order and precondition. -/
noncomputable def pairs (N : ℕ) (a f : ℝ) (pre : ℕ → ℕ → Prop) : Finset Pair :=
  ((primeWindow N a f).product (primeWindow N a f)).filter fun x => x.1 < x.2 ∧ pre x.1 x.2

theorem mem_pairs {N : ℕ} {a f : ℝ} {pre : ℕ → ℕ → Prop} {x : Pair} :
    x ∈ pairs N a f pre ↔ x.1 ∈ primeWindow N a f ∧
      x.2 ∈ primeWindow N a f ∧ x.1 < x.2 ∧ pre x.1 x.2 := by
  simp only [pairs, mem_filter, Finset.product_eq_sprod, mem_product]
  tauto

def denominator (d : ℕ) (x : Pair) : ℕ := d*x.1*x.2
noncomputable def lower (lo : ℝ) (x : Pair) : ℝ := max (x.2 : ℝ) (lo-1)
noncomputable def upper (N d : ℕ) (hi : ℝ) (x : Pair) : ℝ :=
  min hi ((N : ℝ)/denominator d x)
noncomputable def fibre (N d : ℕ) (lo hi : ℝ) (x : Pair) : Finset ℕ :=
  (range (N+1)).filter fun r => r.Prime ∧ lower lo x < r ∧ (r : ℝ) ≤ upper N d hi x

/-- Closed prefixes at both actual endpoints; an inverted interval contributes zero. -/
noncomputable def prefixDifference (L U : ℝ) : ℝ :=
  if L ≤ U then ((primesIcc 0 U).card : ℝ) - ((primesIcc 0 L).card : ℝ) else 0

theorem denominator_pos {N d : ℕ} {a f : ℝ} {pre : ℕ → ℕ → Prop} {x : Pair}
    (hd : 0 < d) (hx : x ∈ pairs N a f pre) : 0 < denominator d x := by
  obtain ⟨hp,hq,_,_⟩ := mem_pairs.mp hx
  exact Nat.mul_pos (Nat.mul_pos hd (mem_primeWindow.mp hp).1.pos) (mem_primeWindow.mp hq).1.pos

theorem upper_le_N {N d : ℕ} {hi : ℝ} {x : Pair} (hD : 0 < denominator d x) :
    upper N d hi x ≤ N := by
  have hDR : (1 : ℝ) ≤ denominator d x := by exact_mod_cast hD
  exact (min_le_right _ _).trans (div_le_self (Nat.cast_nonneg _) hDR)

theorem atom_iff {N d : ℕ} {a f lo hi : ℝ} {pre : ℕ → ℕ → Prop}
    (hd : 0 < d) (t : PrimeTriple) :
    (t ∈ primeTriples N a f lo hi pre ∧ tupleProduct d t ≤ N) ↔
      (t.1,t.2.1) ∈ pairs N a f pre ∧ t.2.2 ∈ fibre N d lo hi (t.1,t.2.1) := by
  constructor
  · rintro ⟨ht,hcap⟩
    obtain ⟨hp,hq,hrN,hpq,hpre,hr,hl,hu⟩ := mem_primeTriples.mp ht
    have hx : (t.1,t.2.1) ∈ pairs N a f pre := mem_pairs.mpr ⟨hp,hq,hpq,hpre⟩
    have hD : (0 : ℝ) < denominator d (t.1,t.2.1) := by
      exact_mod_cast denominator_pos hd hx
    refine ⟨hx,mem_filter.mpr ⟨mem_range.mpr hrN,hr,hl,le_min hu ?_⟩⟩
    apply (le_div_iff₀ hD).mpr
    rw [mul_comm]
    exact_mod_cast hcap
  · rintro ⟨hx,hr⟩
    obtain ⟨hp,hq,hpq,hpre⟩ := mem_pairs.mp hx
    obtain ⟨hrN,hr,hl,hu⟩ := mem_filter.mp hr
    have hD : (0 : ℝ) < denominator d (t.1,t.2.1) := by
      exact_mod_cast denominator_pos hd hx
    refine ⟨mem_primeTriples.mpr ⟨hp,hq,mem_range.mp hrN,hpq,hpre,hr,hl,
      hu.trans (min_le_left _ _)⟩,?_⟩
    have hc := (le_div_iff₀ hD).mp (hu.trans (min_le_right _ _))
    rw [mul_comm] at hc
    exact_mod_cast hc

/-- Coordinate reindexing retains multiplicity even when products coincide. -/
theorem triple_pair_dictionary (N d : ℕ) (a f lo hi : ℝ) (pre : ℕ → ℕ → Prop)
    (hd : 0 < d) :
    (∑ t ∈ primeTriples N a f lo hi pre, if tupleProduct d t ≤ N then (1 : ℝ) else 0) =
      ∑ x ∈ pairs N a f pre, ((fibre N d lo hi x).card : ℝ) := by
  rw [sum_boole]
  have he : ((primeTriples N a f lo hi pre).filter fun t => tupleProduct d t ≤ N).card =
      ((pairs N a f pre).sigma fun x => fibre N d lo hi x).card := by
    apply card_bij (fun t _ => (⟨(t.1,t.2.1),t.2.2⟩ : Σ _ : Pair, ℕ))
    · intro t ht
      exact mem_sigma.mpr ((atom_iff hd t).mp (mem_filter.mp ht))
    · rintro ⟨p,q,r⟩ _ ⟨p',q',r'⟩ _ h
      have h1 := congrArg (fun z : Σ _ : Pair, ℕ => z.1) h
      have h2 := congrArg (fun z : Σ _ : Pair, ℕ => z.2) h
      simp only [Prod.mk.injEq] at h1
      exact Prod.ext h1.1 (Prod.ext h1.2 h2)
    · rintro ⟨⟨p,q⟩,r⟩ hy
      exact ⟨(p,q,r),mem_filter.mpr ((atom_iff hd _).mpr (mem_sigma.mp hy)),rfl⟩
  rw [he,card_sigma,Nat.cast_sum]

theorem fibre_prefix_dictionary (N d : ℕ) (lo hi : ℝ) (x : Pair)
    (hD : 0 < denominator d x) :
    ((fibre N d lo hi x).card : ℝ) = prefixDifference (lower lo x) (upper N d hi x) := by
  have hL : 0 ≤ lower lo x := (Nat.cast_nonneg x.2).trans (le_max_left _ _)
  have hUN := upper_le_N (N := N) (hi := hi) hD
  by_cases h : lower lo x ≤ upper N d hi x
  · have hU : 0 ≤ upper N d hi x := hL.trans h
    have hsub : primesIcc 0 (lower lo x) ⊆ primesIcc 0 (upper N d hi x) := by
      intro r hr
      obtain ⟨hp,hl,hu⟩ := (mem_primesIcc hL).mp hr
      exact (mem_primesIcc hU).mpr ⟨hp,hl,hu.trans h⟩
    have he : fibre N d lo hi x = primesIcc 0 (upper N d hi x) \ primesIcc 0 (lower lo x) := by
      ext r
      simp only [fibre, mem_filter, mem_range, mem_sdiff, mem_primesIcc hU, mem_primesIcc hL]
      constructor
      · rintro ⟨_,hp,hl,hu⟩
        exact ⟨⟨hp,Nat.cast_nonneg _,hu⟩,fun hh => (not_le_of_gt hl) hh.2.2⟩
      · rintro ⟨⟨hp,_,hu⟩,hn⟩
        have hl : lower lo x < r := lt_of_not_ge (fun hh => hn ⟨hp,Nat.cast_nonneg _,hh⟩)
        have hrN : r ≤ N := by exact_mod_cast hu.trans hUN
        exact ⟨by omega,hp,hl,hu⟩
    rw [he,card_sdiff_of_subset hsub,Nat.cast_sub (card_le_card hsub),prefixDifference,if_pos h]
  · have he : fibre N d lo hi x = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨_,_,hl,hu⟩ := mem_filter.mp hr
      exact h (hl.le.trans hu)
    simp only [he,card_empty,Nat.cast_zero,prefixDifference,if_neg h]

noncomputable def actualPairs (N : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) (d : ℕ) : Finset Pair :=
  pairs N (wuLocalCutoff N δ d P.S) (wuLocalCutoff N δ d P.s)
    (LowerTripleGrouped.actualPre N δ P j d)
noncomputable def actualLower (N : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) (d : ℕ) (x : Pair) : ℝ :=
  lower (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.1 x
noncomputable def actualUpper (N : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) (d : ℕ) (x : Pair) : ℝ :=
  upper N d (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.2 x

/-- The unchanged unitMass first reorders to the actual physical prime fibres. -/
theorem unitMass_pair_fibre {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) :
    unitMass N δ Δ V P j =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ∑ x ∈ actualPairs N δ P j d,
          ((fibre N d (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.1
            (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.2 x).card : ℝ) := by
  unfold unitMass
  apply sum_congr rfl
  intro d hd
  have hdp := boxConvolutionSupport_pos
    (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
  congr 1
  exact triple_pair_dictionary _ _ _ _ _ _ _ hdp

/-- The unchanged original unitMass, exactly, with both closed endpoints. -/
theorem unitMass_pair_prefix {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) :
    unitMass N δ Δ V P j =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ∑ x ∈ actualPairs N δ P j d,
          prefixDifference (actualLower N δ P j d x) (actualUpper N δ P j d x) := by
  rw [unitMass_pair_fibre]
  apply sum_congr rfl
  intro d hd
  have hdp := boxConvolutionSupport_pos
    (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
  congr 1
  exact sum_congr rfl (fun x hx => fibre_prefix_dictionary _ _ _ _ _ (denominator_pos hdp hx))

end Wu2008DoubleSieve.LowerTripleGroupedUnit
