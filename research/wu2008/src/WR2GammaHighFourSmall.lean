import WR2GammaHighFourOutput
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSieveSmall
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeErrorInputs

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Real Finset
open scoped Classical

theorem source_small_le_closed (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 4) (Z : ℝ) :
    (sourceFamily j N δ k).small Z ≤
      closedSmall N δ (Wu04RemainingCore.row j) (windows j N) k Z := by
  let L := sourceFamily j N δ k
  have hsub : L.labels ⊆ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k :=
    filter_subset _ _
  calc
    _ ≤ ∑ x ∈ L.labels, (convolutionCoeff (windows j N) x.1 : ℝ) *
        ((actualFibre N δ (Wu04RemainingCore.row j) k x).filter (fun q => ((N-gamma16Cofactor x*q : ℕ) : ℝ) ≤ Z)).card := by
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Nat.cast_le.mpr
      apply card_le_card
      intro q hq
      obtain ⟨hq,hprime,hlt⟩ := mem_filter.mp hq
      have hd : ∀ d ∈ boxConvolutionSupport (windows j N), 0 < d :=
        fun _ hd => boxConvolutionSupport_pos
          (fun _ _ hq => (mem_primeWindow.mp hq).1.pos) hd
      have he := (actualFamily_fibres (Wu04RemainingCore.row j) (windows j N) k hd (hsub hx)).2
      have hmem : q ∈ ((actualFamily N δ (Wu04RemainingCore.row j) (windows j N) k hd).primes x).filter
          (fun q => (N-gamma16Cofactor x*q).Prime) := mem_filter.mpr ⟨hq,hprime⟩
      rw [he] at hmem
      exact mem_filter.mpr ⟨hmem,hlt.le⟩
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem small_bound {N : ℕ} {δ Z : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (hZ : 0 ≤ Z) :
    (sourceFamily j N δ k).small Z ≤ (max 1 (1/highEta))^5*Z := by
  apply (source_small_le_closed j N δ k Z).trans
  apply closedSmall_le_of_output_bound _ _ _ hZ (by positivity)
  exact actual_fixed_output j hN hd hh k (fun _ q hq => by
    have hg := prime_geometry j hN hd hh hq
    exact ⟨hg.1,hg.2.2.1⟩)

theorem small_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 4,
      (sourceFamily j N δ k).small (sqrt ((N : ℝ)^(1/2-δ))) ≤ ε*truncatedSixthMassScale N := by
  have hK : 0 < (max 1 (1/highEta))^5 := by positivity
  have hg : 0 < 1-(1/2-δ)/2 := by linarith
  obtain ⟨T,hT,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 0 he hK hg
  refine ⟨T,hT,fun N hN j k => ?_⟩
  have hs := HighUnitSieve.source_small_power (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  exact (small_bound j k (by omega) hd hh (sqrt_nonneg _)).trans
    ((hs.2.2.2.2.2 _).trans_le (hp N hN))

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.small_paid
