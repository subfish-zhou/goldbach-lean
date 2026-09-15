import HighO3Atoms

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter LiLiuPrereqBuchstab
open scoped Classical Topology
noncomputable section

/-- Fixed-delta Buchstab convergence on the actual closed-p3 atoms. The
compact cap is an existential natural bound, never a searched numerical cap. -/
theorem rough_uniform {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ p ∈ omega3XPrimes N δ s t d,
      let x := omega3XScale N d p.1 p.2.1 p.2.2
      let y := (p.2.1 : ℝ)
      primeErrorStart ≤ y ∧
        |(roughCount x y : ℝ)-x*buchstab (log x/log y)/log y| ≤ ε*(x/log y) := by
  let u0 : ℝ := 1+2*δ/(1/2-δ)
  have hu0 : 1 < u0 := by
    have : 0 < 2*δ/(1/2-δ) := by positivity
    dsimp [u0]; linarith
  obtain ⟨M,hM⟩ := exists_nat_gt (max 2 (max (1/η) u0))
  have hM2 : 2 ≤ M := by
    have := (le_max_left 2 (max (1/η) u0)).trans_lt hM
    exact_mod_cast this.le
  obtain ⟨X,_,hX⟩ := roughCount_uniform_buchstab_fixed M hM2 hu0 hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max X primeErrorStart)))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN d hd hsize s t hs hst ht p hp
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨_,hy,hyx,hyg,hxg,_,hgap,hcap⟩ :=
    atom_geometry (by omega) hd hδ hδhi hη hsize hs hst ht hp
  have hu : log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1 ∈ Set.Icc u0 (M : ℝ) := by
    constructor
    · have hh := div_le_div_of_nonneg_right (show 2*δ ≤ 4*δ by linarith)
        (show 0 ≤ 1/2-δ by linarith)
      dsimp [u0]; linarith
    · exact hcap.trans (((le_max_left (1/η) u0).trans (le_max_right _ _)).trans_lt hM).le
  have hgrowth := hT N ((le_max_right _ _).trans hN)
  have hxX := ((le_max_left X primeErrorStart).trans hgrowth).trans hxg
  have hyStart := ((le_max_right X primeErrorStart).trans hgrowth).trans hyg
  have hy1 : (1 : ℝ) < p.2.1 := by linarith
  obtain ⟨_,_,_,hcoord,hnorm⟩ := omega3X_buchstab_coordinates hy1 hyx
  obtain ⟨hpos,hrel⟩ := hX _ hxX _ hu
  rw [← hcoord,hnorm] at hrel
  rw [hnorm] at hpos
  refine ⟨hyStart,?_⟩
  let B := omega3XScale N d p.1 p.2.1 p.2.2 *
    buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1)/log p.2.1
  have heq : (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)/B-1 =
      ((roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)-B)/B := by
    have hB : B ≠ 0 := hpos.ne'
    field_simp
  change |(roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)/B-1| < ε at hrel
  rw [heq,abs_div,abs_of_pos hpos] at hrel
  exact ((div_lt_iff₀ hpos).mp hrel).le.trans
    (mul_le_mul_of_nonneg_left (omega3X_buchstab_main_term_bounds hy1 hyx).2 hε.le)

/-- Whole finite rough main sum, paid by the identical coefficient reciprocal mass. -/
theorem rough_buchstab {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ (i : ℕ) (W : Fin i → Finset ℕ),
      (∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3XRoughMajorant N δ s t W ≤ omega3XBuchstabMain N δ s t W+
        ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass W := by
  let C : ℝ := (5/η)^3/η
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T1,hT14,hT1⟩ := rough_uniform hδ hδhi hη (div_pos hε hC)
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop primeErrorStart))
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN i W hw s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN4 := hT14.trans hN1
  have hstart := hT2 N ((le_max_right _ _).trans hN)
  have hpoint : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ omega3XPrimes N δ s t d,(roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)) ≤
      (∑ p ∈ omega3XPrimes N δ s t d,
        omega3XScale N d p.1 p.2.1 p.2.2 *buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1)/log p.2.1)+
      ε*((N : ℝ)/d/log N) := by
    intro d hd
    have hb : (∑ p ∈ omega3XPrimes N δ s t d,
        (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)) ≤
      (∑ p ∈ omega3XPrimes N δ s t d,
        omega3XScale N d p.1 p.2.1 p.2.2 *buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1)/log p.2.1)+
      ε/C*(∑ p ∈ omega3XPrimes N δ s t d,omega3XScale N d p.1 p.2.1 p.2.2/log p.2.1) := by
      rw [mul_sum,← sum_add_distrib]
      apply sum_le_sum
      intro p hp
      have hh := (hT1 N hN1 d (hw d hd).1 (hw d hd).2 s t hs hst ht p hp).2
      have hh' := (le_abs_self _).trans hh
      linarith
    have hm := mul_le_mul_of_nonneg_left
      (scale_mass (by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2 hs hst ht hstart) (div_pos hε hC).le
    change ε/C* _ ≤ ε/C*(C*((N : ℝ)/d/log N)) at hm
    have heq : ε/C*(C*((N : ℝ)/d/log N)) = ε*((N : ℝ)/d/log N) := by field_simp
    rw [heq] at hm
    exact hb.trans (add_le_add le_rfl hm)
  unfold omega3XRoughMajorant omega3XBuchstabMain boxConvolutionReciprocalMass
  rw [mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hm := mul_le_mul_of_nonneg_left (hpoint d hd) (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _)
  convert hm using 1
  ring

/-- The distinct repeated-p1 X error is also paid; it is not charged to the
three switching losses a second time. -/
theorem X_buchstab {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ (i : ℕ) (W : Fin i → Finset ℕ),
      (∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3SieveX N δ s t W ≤ omega3XBuchstabMain N δ s t W+
        ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass W := by
  obtain ⟨T1,hT14,hT1⟩ := rough_buchstab hδ hδhi hη (half_pos hε)
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp (omega3_repeated_scalar_budget hη (half_pos hε))
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN i W hw s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN4 := hT14.trans hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : omega3XRepeatedMajorant N δ s t W ≤
      (((N : ℝ)/(N : ℝ)^η)*(1+log N)^3)*boxConvolutionReciprocalMass W := by
    unfold omega3XRepeatedMajorant omega3XScale
    apply omega3_repeated_weighted_floor_le _ _ (rpow_pos_of_pos hNr _)
    · exact fun d hd => (hw d hd).1
    · exact fun _ _ _ hp => omega3XPrimes_mem_Icc hp
    · intro d hd p hp
      exact ((mem_primesIcc hNr.le).mp
        (prime_interval (by omega) (hw d hd).1 hδ hδhi hη (hw d hd).2 hs hst ht hp).1).2.1
  have hm : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hrpay := hr.trans (mul_le_mul_of_nonneg_right (hT2 N ((le_max_right _ _).trans hN)) hm)
  have hb := hT1 N hN1 i W hw s t hs hst ht
  have hf := omega3SieveX_le_rough_add_repeated N δ s t W (fun d hd => (hw d hd).1)
  linarith

end
end HighO3
