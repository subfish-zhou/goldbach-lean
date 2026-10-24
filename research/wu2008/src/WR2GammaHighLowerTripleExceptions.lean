import WR2GammaHighLowerTripleRoughMass
import WR2GammaHighLowerTripleOutput

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Real Finset
open scoped Classical

theorem weightAt_prime {N ell : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6) (hell : ell.Prime) :
    (sourceFamily j N δ k).weightAt ell =
      ∑ x ∈ (sourceFamily j N δ k).labels,
        (convolutionCoeff (windows j N) x.1 : ℝ) *
          ((outputFibre j N δ k x).filter
            (fun r => N-cofactor x*r = ell)).card := by
  change (∑ x ∈ (sourceFamily j N δ k).labels,
    (convolutionCoeff (windows j N) x.1 : ℝ) *
      (((sourceFamily j N δ k).primes x).filter
        (fun r => N-cofactor x*r = ell)).card) = _
  apply sum_congr rfl
  intro x _
  apply congrArg (fun s : Finset ℕ =>
    (convolutionCoeff (windows j N) x.1 : ℝ) * (s.card : ℝ))
  ext r
  simp only [outputFibre, mem_filter]
  constructor
  · rintro ⟨hr,he⟩
    exact ⟨⟨hr,he ▸ hell⟩,he⟩
  · rintro ⟨⟨hr,_⟩,he⟩
    exact ⟨hr,he⟩

theorem bad_prime_bound {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    (sourceFamily j N δ k).noncoprimePart.primeMass ≤
      (max 1 (1/highEta))^4*log N/log 2 := by
  apply LabelledPhysical.Family.noncoprimePart_primeMass_le_log
    (sourceFamily j N δ k) (by omega) (by positivity)
  intro ell hell
  rw [weightAt_prime j k (Nat.prime_of_mem_primeFactors hell)]
  exact actual_fixed_output j k hN hd hh ell

theorem square_mass_bound {N : ℕ} {δ Y : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) (hY : 2 ≤ Y) :
    (sourceFamily j N δ k).squareRawMass Y ≤
      (max 1 (1/highEta))^3*N*(1+log N)/(Y-1) :=
  (sourceFamily j N δ k).squareRawMass_le hY (by positivity)
    (fixed_cofactor_bound j k hN hd hh)

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.bad_prime_bound
#print axioms WuPaper.R2GammaHigh.LowerTriple.square_mass_bound
