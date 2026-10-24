import WR2GammaHighTailUnitFibre
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitErrorPayment
import WR2GammaHighNineUpper

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve HighBoxRecovery Real Finset
open scoped Classical

theorem small_bound {n N : ℕ} {δ Z : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (hn : n ≤ 5)
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)))
    (j : Fin n) (b : ℕ → ℝ) (hZ : 0 ≤ Z) (hZN : Z < N) :
    (sourceFamily row hN hd hh P j b).small Z ≤ (max 1 (1/highEta))^7*Z := by
  apply (sourceFamily_small_le row hN hd hh P j b Z).trans
  have hs := small_output_real_le (windows row N) (family N (windows row N) P j b) j
    (by norm_num : 1 ≤ 1) (by omega : 1 < N) (by norm_num [highEta] : 0 < highEta) hZ hZN
    (fun a q hq => by
      have hw := prime_geometry row hN hd hh hq
      exact ⟨hw.1,hw.2.2.1⟩)
    (fun c hc => source_profile_geometry row hN hd hh P j b hc)
  exact hs.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (le_max_left _ _) (by omega)) hZ)

theorem small_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, ∃ hT : 4 ≤ T, ∀ (N : ℕ) (hN : T ≤ N), ∀ row : Fin 3,
      ∀ (n : ℕ), n ≤ 5 →
      ∀ (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)))
        (j : Fin n) (b : ℕ → ℝ),
      (sourceFamily row (by omega : 2 ≤ N) hd hh P j b).small (sqrt ((N:ℝ)^(1/2-δ))) ≤
        ε*truncatedSixthMassScale N := by
  have hK : 0 < (max 1 (1/highEta))^7 := by positivity
  have hg : 0 < 1-(1/2-δ)/2 := by linarith
  obtain ⟨T,hT,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 0 he hK hg
  refine ⟨T,hT,?_⟩
  intro N hN row n hn P j b
  have hs := HighUnitSieve.source_small_power (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  exact (small_bound row (by omega) hd hh hn P j b hs.2.2.2.1 hs.2.2.2.2.1).trans
    ((hs.2.2.2.2.2 _).trans_le (hp N hN))

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.small_paid
