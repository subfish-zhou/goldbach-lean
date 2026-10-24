import WR2GammaHighTailUnitFibre
import WR2GammaHighTailR2

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve HighBoxRecovery Real Finset Filter
open scoped Classical Topology

theorem R2_bound {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 4 ≤ N), ∀ row : Fin 3,
      ∀ (n : ℕ), n ≤ 5 →
      ∀ (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N:ℝ)^(1/2-δ)/d))) (j : Fin n) (b : ℕ → ℝ),
      (sourceFamily row (by omega : 2 ≤ N) hd hh P j b).R2 (⌊(N : ℝ)^(1/2-δ)⌋₊+1)
        (sqrt ((N : ℝ)^(1/2-δ))) ≤
          C*(max 1 (1/highEta))^6*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2)) := by
  obtain ⟨C,hC,hc⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  refine ⟨C,hC,fun N hN row n hn P j b => ?_⟩
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  apply hc N (by omega) _ (sourceFamily row (by omega : 2 ≤ N) hd hh P j b) _ _ _ _ hg.2.2.2.1
    (by positivity) (by positivity) ?_ ?_ ?_
  · intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    omega
  · intro c hc q hq hqc _
    exact (family_facts row (by omega) hd hh P j b).1 c hc |>.2 q hq hqc
  · intro e
    exact (fixed_cofactor_bound row (by omega) hd hh P j b e).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))

theorem R2_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, ∃ hT : 4 ≤ T, ∀ (N : ℕ) (hN : T ≤ N), ∀ row : Fin 3,
      ∀ (n : ℕ), n ≤ 5 →
      ∀ (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N:ℝ)^(1/2-δ)/d))) (j : Fin n) (b : ℕ → ℝ),
      (sourceFamily row (by omega : 2 ≤ N) hd hh P j b).R2 (⌊(N : ℝ)^(1/2-δ)⌋₊+1)
        (sqrt ((N : ℝ)^(1/2-δ))) ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,hb⟩ := R2_bound hd hh
  have hK : 0 < 2*C*(max 1 (1/highEta))^6/log 2 := by positivity
  obtain ⟨T0,hT0,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 5 he hK
    (show 0 < highEta by norm_num [highEta])
  obtain ⟨T1,hl⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),fun N hN row n hn P j b => ?_⟩
  have hlog := hl N (by omega)
  dsimp only [Function.comp_apply] at hlog
  calc
    _ ≤ C*(max 1 (1/highEta))^6*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2)) :=
      hb N (by omega) row n hn P j b
    _ ≤ C*(max 1 (1/highEta))^6*N*((2*log N)*log N^4/((N : ℝ)^highEta*log 2)) := by
      gcongr
      linarith
    _ = (2*C*(max 1 (1/highEta))^6/log 2)*N*log N^5/(N : ℝ)^highEta := by ring
    _ ≤ _ := hp N (by omega)

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.R2_paid
