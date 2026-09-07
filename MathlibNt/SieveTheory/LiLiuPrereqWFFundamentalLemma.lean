import MathlibNt.SieveTheory.LiLiuPrereqWFAnalytic
import MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridge

/-!
# Large-D fundamental-lemma density of the original small weights

The actual JR/Suzuki estimate controls the entire defects, including their
low-prime contributions. An absolute constant is selected before `ε`;
the explicit threshold is selected before all sieve data, `K`, and depths.
This proves the large-`D` form of Iwaniec p.316 (22), not the density of the
as-yet unassembled full signed box family.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne
open scoped Classical

/-- The full original defects, with an absolute constant selected before
`ε`, and a threshold selected before the carrier, density, and `K`. -/
theorem exists_smallDensityDefects_fundamental_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ (P : Finset ℕ) (g : ArithmeticFunction ℝ),
          g.IsMultiplicative →
          (∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p < 1) →
          ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P g K →
            let B := geometricSmallPrimes P D ε
            let E := C * (Real.exp (-(1 / ε)) +
              Real.exp (Real.sqrt K - 1 / ε) *
                (ε * Real.log D) ^ (-(1 / 3 : ℝ)))
            lowerDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) ≤
                (∏ p ∈ B, (1 - g p)) * E ∧
            upperDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) ≤
                (∏ p ∈ B, (1 - g p)) * E := by
  obtain ⟨A, B, hA, hB, hactual⟩ := exists_actualT_exp_bound
  let C := max A (B * Real.exp (Real.sqrt 2))
  refine ⟨C, hA.trans_le (le_max_left _ _), ?_⟩
  intro ε hε hεsmall
  let T := max (max (Real.log 2) ((2 / ε) ^ 13)) (Real.exp 1)
  refine ⟨max 2 (Real.exp (T / ε)), le_max_left _ _, ?_⟩
  intro D hD P g hgm hg K hK hdim
  have hD2 : 2 ≤ D := (le_max_left _ _).trans hD
  have hlarge : T ≤ ε * Real.log D := by
    have h := Real.log_le_log (Real.exp_pos (T / ε))
      ((le_max_right _ _).trans hD)
    rw [Real.log_exp] at h
    exact (div_le_iff₀ hε).mp h |>.trans_eq (mul_comm _ _)
  have hb := (le_max_left _ _).trans hlarge
  have hl := (le_max_left _ _).trans hb
  let S := smallDensityBoundingSieve P D ε g hgm hg
  let ps := nonzeroDensityPrimes (geometricSmallPrimes P D ε) g
  let R := ⌈D ^ ε⌉₊
  let s := roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2))
  have hL : 1 < D ^ ε := Real.one_lt_rpow (by linarith) hε
  have hu : 1 < D ^ (ε ^ 2) := Real.one_lt_rpow (by linarith) (sq_pos_of_pos hε)
  have hR : 2 ≤ R := by
    have : 1 < R := Nat.lt_ceil.mpr (by simpa using hL)
    omega
  have hs8 : 8 < s := (small_rounded_moving_range hD2 hε hεsmall hlarge).1
  have hs : 2 ≤ s := by linarith
  have hbudget : s ^ 13 ≤ Real.log (R : ℝ) :=
    small_rounded_power_budget hD2 hε hb
  have hlog : Real.exp 1 ≤ Real.log (R : ℝ) :=
    ((le_max_right _ _).trans hlarge).trans (log_ceil_rpow_bounds hD2 hl).1
  have hcut : (R : ℝ) ^ (1 / s) = D ^ (ε ^ 2) :=
    roundedSieveCoordinate_cutoff hL hu
  have hz : 2 ≤ ⌈(R : ℝ) ^ (1 / s)⌉₊ := by
    rw [hcut]
    exact (small_rounded_cutoff_bounds hD2 hε (by linarith)).1
  have hlocal : HasDimensionOneLocalProductBound S (max K 2) :=
    smallDensityBoundingSieve_hasDimensionOneLocalProductBound P D ε g hgm hg
      (hK.trans (le_max_left _ _))
      (dimensionOneProductBound_mono hdim (le_max_left _ _))
  have hV : suzukiVProduct S (⌈D ^ (ε ^ 2)⌉₊ : ℝ) =
      ∏ p ∈ geometricSmallPrimes P D ε, (1 - g p) :=
    densityBoundingSieve_suzukiVProduct (geometricSmallPrimes P D ε)
      (smallPrimes_prime P D ε) g hgm hg
      (fun p hp => (Finset.mem_filter.mp hp).2.2)
  have hV0 : 0 ≤ ∏ p ∈ geometricSmallPrimes P D ε, (1 - g p) :=
    Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hg p hp).2.le)
  have hsingle (N : ℕ) (hN : 1 ≤ N) :
      suzukiActualT S N R ⌈D ^ (ε ^ 2)⌉₊ ≤
        (∏ p ∈ geometricSmallPrimes P D ε, (1 - g p)) *
          (C * (Real.exp (-(1 / ε)) +
            Real.exp (Real.sqrt K - 1 / ε) *
              (ε * Real.log D) ^ (-(1 / 3 : ℝ)))) := by
    have hdom : s ∈ KappaOneModel.parityDomain 2 N := by
      unfold KappaOneModel.parityDomain
      split_ifs <;> simp only [Set.mem_Ioi, Set.mem_Ici] <;> linarith
    have h := hactual S (max K 2) N R s (le_max_right _ _) hlocal
      hN hR hs hdom hbudget hlog hz
    rw [hcut, hV] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (small_rounded_error_bound A B K hA.le hB.le hD2 hε hl) hV0)
  have hid := smallDensityDefects_eq_suzukiActualT P hD2 hε
    (by linarith) g hgm hg
  dsimp only at hid ⊢
  rw [hid.1, hid.2]
  exact ⟨hsingle (2 * (ps.card + 1)) (by omega),
    hsingle (2 * ps.card + 1) (by omega)⟩

/-- The large-D form of Iwaniec p.316 (22), in the literal `ω(d)/d`
convention and for the already constructed small weights. -/
theorem exists_smallWeight_source_fundamental_density :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ (P : Finset ℕ) (ω : ArithmeticFunction ℝ),
          ω.IsMultiplicative →
          (∀ p ∈ geometricSmallPrimes P D ε,
            0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
          ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
            let B := geometricSmallPrimes P D ε
            let V := ∏ p ∈ B, (1 - ω p / (p : ℝ))
            let E := C * (Real.exp (-(1 / ε)) +
              Real.exp (Real.sqrt K - 1 / ε) *
                (ε * Real.log D) ^ (-(1 / 3 : ℝ)))
            |(∑ d ∈ (B.prod id).divisors,
                lowerSmallWeight P D ε d * (ω d / (d : ℝ))) - V| ≤ V * E ∧
            |(∑ d ∈ (B.prod id).divisors,
                upperSmallWeight P D ε d * (ω d / (d : ℝ))) - V| ≤ V * E := by
  obtain ⟨C, hC, hbound⟩ := exists_smallDensityDefects_fundamental_bound
  refine ⟨C, hC, ?_⟩
  intro ε hε hεsmall
  obtain ⟨D₀, hD₀, hbound⟩ := hbound ε hε hεsmall
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD P ω hω hg K hK hdim
  have hD2 := hD₀.trans hD
  have h := hbound D hD P (primeDensity ω) (primeDensity_isMultiplicative hω)
    hg K hK hdim
  have hid := smallWeight_source_density_identities P hD2 hε hεsmall hω
  have hlo0 := lowerDensityDefect_nonneg (L := D ^ ε) (g := primeDensity ω)
    ((geometricSmallPrimes P D ε).sort (· ≤ ·))
    (fun p hp => ⟨(hg p (by simpa using hp)).1, (hg p (by simpa using hp)).2.le⟩)
  have hup0 := upperDensityDefect_nonneg (L := D ^ ε) (g := primeDensity ω)
    ((geometricSmallPrimes P D ε).sort (· ≤ ·))
    (fun p hp => ⟨(hg p (by simpa using hp)).1, (hg p (by simpa using hp)).2.le⟩)
  dsimp only at h ⊢
  rw [hid.1, hid.2]
  simpa only [primeDensity_apply, sub_sub_cancel_left, abs_neg, add_sub_cancel_left,
    abs_of_nonneg hlo0, abs_of_nonneg hup0] using h

/-- Signed small-weight bounds and the exact cost needed when replacing the
lower small-weight density by the upper one. This does not perform that
replacement inside an unproved full box-family identity. -/
theorem exists_smallWeight_source_density_sandwich :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ (P : Finset ℕ) (ω : ArithmeticFunction ℝ),
          ω.IsMultiplicative →
          (∀ p ∈ geometricSmallPrimes P D ε,
            0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
          ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
            let B := geometricSmallPrimes P D ε
            let V := ∏ p ∈ B, (1 - ω p / (p : ℝ))
            let E := C * (Real.exp (-(1 / ε)) +
              Real.exp (Real.sqrt K - 1 / ε) *
                (ε * Real.log D) ^ (-(1 / 3 : ℝ)))
            let lo := ∑ d ∈ (B.prod id).divisors,
              lowerSmallWeight P D ε d * (ω d / (d : ℝ))
            let hi := ∑ d ∈ (B.prod id).divisors,
              upperSmallWeight P D ε d * (ω d / (d : ℝ))
            V * (1 - E) ≤ lo ∧ lo ≤ V ∧ V ≤ hi ∧
              hi ≤ V * (1 + E) ∧ hi - lo ≤ 2 * V * E := by
  obtain ⟨C, hC, hbound⟩ := exists_smallWeight_source_fundamental_density
  refine ⟨C, hC, ?_⟩
  intro ε hε hεsmall
  obtain ⟨D₀, hD₀, hbound⟩ := hbound ε hε hεsmall
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD P ω hω hg K hK hdim
  have habs := hbound D hD P ω hω hg K hK hdim
  have hbracket := smallWeight_density_bracket P (hD₀.trans hD) hε hεsmall
    (primeDensity_isMultiplicative hω) (fun p hp => ⟨(hg p hp).1, (hg p hp).2.le⟩)
  dsimp only at habs ⊢
  have hlo := (abs_le.mp habs.1).1
  have hhi := (abs_le.mp habs.2).2
  refine ⟨?_, hbracket.1, hbracket.2, ?_, ?_⟩ <;> nlinarith

#check exists_smallDensityDefects_fundamental_bound
#check exists_smallWeight_source_fundamental_density
#check exists_smallWeight_source_density_sandwich
#print axioms exists_smallDensityDefects_fundamental_bound
#print axioms exists_smallWeight_source_fundamental_density
#print axioms exists_smallWeight_source_density_sandwich

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
