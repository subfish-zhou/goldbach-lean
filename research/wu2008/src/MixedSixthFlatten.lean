import MixedSixthGrid

namespace MixedSixth
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
noncomputable section

/-- The nested natural encoding retains every label once, even across coarse cells. -/
theorem sum_packing (N n : ℕ) (K : Finset ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ packing N n K, f k) = ∑ i ∈ K,
      ∑ j ∈ truncatedSixthMassPacking N (loX n i) (hiX n i) (loY n i) (hiY n i),
        f (Nat.pair i (Nat.pair j.1 j.2)) := by
  unfold packing
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro i _
    rw [sum_image]
    · unfold fineCells
      rw [sum_image]
      intro a _ b _ h
      exact Nat.pairEquiv.injective h
    · intro a _ b _ h
      exact (Nat.pair_eq_pair.mp h).2
  · intro i _ j _ hij
    apply disjoint_left.mpr
    intro k hk hk'
    obtain ⟨a,_,ha⟩ := mem_image.mp hk
    obtain ⟨b,_,hb⟩ := mem_image.mp hk'
    exact hij (Nat.pair_eq_pair.mp (ha.trans hb.symm)).1

def reciprocal (N n : ℕ) (K : Finset ℕ) : ℝ :=
  ∑ k ∈ packing N n K,
    ∑ p ∈ truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x N n k) (y N n k),
      1/((p.1:ℝ)*p.2)

def reciprocalLimit (n : ℕ) (K : Finset ℕ) : ℝ :=
  ∑ i ∈ K, log (hiX n i / loX n i)*log (hiY n i / loY n i)

theorem reciprocal_eq (N n : ℕ) (K : Finset ℕ) :
    reciprocal N n K = ∑ i ∈ K,
      truncatedSixthMassPackingReciprocal N (loX n i) (hiX n i) (loY n i) (hiY n i) := by
  unfold reciprocal
  rw [sum_packing]
  apply sum_congr rfl
  intro i _
  simp only [x,y,outer,inner,Nat.unpair_pair,truncatedSixthMassPackingReciprocal,
    truncatedSixthMassPackingBox]

theorem reciprocal_tendsto (n : ℕ) (K : Finset ℕ)
    (hK : ∀ i ∈ K, 0 < loX n i ∧ 0 < loY n i) :
    Tendsto (fun N => reciprocal N n K) atTop (𝓝 (reciprocalLimit n K)) := by
  simp_rw [reciprocal_eq,reciprocalLimit]
  exact tendsto_finsetSum K (fun i hi => truncatedSixthMass_packing_reciprocal_tendsto
    (hK i hi).1 (truncatedSixthClosure_lo_lt_hi n (coarse i).1).le
    (hK i hi).2 (truncatedSixthClosure_lo_lt_hi n (coarse i).2).le)

theorem low_reciprocal_tendsto (δ : ℝ) (n : ℕ) :
    Tendsto (fun N => reciprocal N n (lowCells δ n)) atTop
      (𝓝 (reciprocalLimit n (lowCells δ n))) :=
  reciprocal_tendsto n _ (fun _ hi =>
    ⟨truncatedSixthLower_parameters.1.trans_le (low_geometry hi).1,
      (truncatedSixthLower_parameters.1.trans truncatedSixthLower_parameters.2.1).trans_le
        (low_geometry hi).2.1⟩)

theorem high_reciprocal_tendsto (δ : ℝ) (n : ℕ) :
    Tendsto (fun N => reciprocal N n (highCells δ n)) atTop
      (𝓝 (reciprocalLimit n (highCells δ n))) :=
  reciprocal_tendsto n _ (fun _ hi =>
    ⟨truncatedSixthLower_parameters.1.trans_le (high_geometry hi).1,
      (show (0:ℝ) < 1/4 by norm_num).trans_le (high_geometry hi).2.1⟩)

/-- The entire actual packing mass has its full finite-rectangle limit. -/
theorem joint_reciprocal_tendsto (δ : ℝ) (n : ℕ) :
    Tendsto (fun N => reciprocal N n (lowCells δ n)+reciprocal N n (highCells δ n))
      atTop (𝓝 (reciprocalLimit n (lowCells δ n)+reciprocalLimit n (highCells δ n))) :=
  (low_reciprocal_tendsto δ n).add (high_reciprocal_tendsto δ n)

/-- Literal evaluation on the constructed joint packing. -/
def main (N n : ℕ) (δ η : ℝ) : ℝ :=
  HighConsumer.mixedMain N δ (truncatedSixthMassDelta N) η
    (packing N n (lowCells δ n)) (packing N n (highCells δ n))
    (x N n) (y N n) (sourceS δ n) (x N n) (y N n) (sourceS δ n)

/-- The constructed grid actually enters the original sixth count. There is
no PackingGeometry binder. This is not yet a scalar normalization theorem. -/
theorem actual_count {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*HighBoxRecovery.highEta)
    (hd : δ < 1/100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε) (n : ℕ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      main N n δ η-ε*U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨T,hT,hcount⟩ := HighConsumer.mixed_count hδ hδhi hd hη hηhi hε
    (lowNodes δ n) (lowNodes_bounds hδ.le n)
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hN1 : 1 < N := by omega
  exact hcount N hN he (truncatedSixthMassDelta N)
    (truncatedSixthMass_delta_legal hN1).2.1 (truncatedSixthMass_delta_legal hN1).2.2
    _ _ _ _ _ _ _ _ (actual_geometry hN1 hδ.le n)

end
end MixedSixth
