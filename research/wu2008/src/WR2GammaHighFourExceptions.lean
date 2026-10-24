import WR2GammaHighFourRough
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeExceptionBounds

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Real Finset
open scoped Classical

theorem bad_prime_bound {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    (sourceFamily j N δ k).noncoprimePart.primeMass ≤
      (max 1 (1/highEta))^5*log N/log 2 := by
  apply LabelledPhysical.Family.noncoprimePart_primeMass_le_log
    (sourceFamily j N δ k) (by omega) (by positivity)
  intro ell hell
  unfold sourceFamily
  rw [actualFamily_weightAt_prime _ _ _ _ (Nat.prime_of_mem_primeFactors hell)]
  exact actual_fixed_output j hN hd hh k (fun _ q hq => by
    have hg := prime_geometry j hN hd hh hq
    exact ⟨hg.1,hg.2.2.1⟩) ell

theorem square_mass_bound {N : ℕ} {δ Y : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (hY : 2 ≤ Y) :
    (sourceFamily j N δ k).squareRawMass Y ≤
      (max 1 (1/highEta))^4*N*(1+log N)/(Y-1) :=
  (sourceFamily j N δ k).squareRawMass_le hY (by positivity)
    (fixed_cofactor_bound j k hN hd hh)

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.bad_prime_bound
#print axioms WuPaper.R2GammaHigh.Four.square_mass_bound
