import WR2GammaHighLowerTripleBoundary

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve HighBoxRecovery Real Finset Filter
open scoped Classical Topology

/-- Moving the lower r face pays one epsilon across all six original bands. -/
theorem finiteMain_six_boundary_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Fin 6, finiteBuchstabMain j N δ k ≤
        unshiftedFiniteBuchstabMain j N δ k +
          (ε/6)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Fin 6, finiteBuchstabMain j N δ k) ≤
        (∑ k : Fin 6, unshiftedFiniteBuchstabMain j N δ k) +
          ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
  let C : ℝ := 5^2/highEta
  have hlim : Tendsto (fun N : ℕ => C*(N:ℝ)^(-highEta)) atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (by norm_num [highEta] : 0 < highEta)).comp
        tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by positivity : 0 < ε/6)))
  obtain ⟨T1,hT1,h1⟩ := high_slab_mass hd hh
  refine ⟨max T0 T1,by omega,?_⟩
  intro N hN j
  have hN4 : 4 ≤ N := by omega
  have hc := (hT0 N (by omega)).le
  have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hX : 0 ≤ ((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hlog.le)
      (sum_nonneg (fun _ _ => by positivity))
  have hs (k : Fin 6) : finiteBuchstabMain j N δ k ≤
      unshiftedFiniteBuchstabMain j N δ k +
        (ε/6)*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) := by
    rw [main_split]
    apply add_le_add le_rfl
    apply (boundaryMass_le j hN4 hd hh k (h1 N (by omega) j)).trans
    simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_right hc hX
  refine ⟨hs,?_⟩
  have hsum := sum_le_sum (s := (univ : Finset (Fin 6))) (fun k _ => hs k)
  simpa only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, show (6:ℝ)*((ε/6)*((N:ℝ)/log N)*
      boxConvolutionReciprocalMass (windows j N)) =
      ε*((N:ℝ)/log N)*boxConvolutionReciprocalMass (windows j N) by ring] using hsum

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.finiteMain_six_boundary_paid
