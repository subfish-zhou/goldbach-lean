import MathlibNt.Wu2008DoubleSieve.HighSixOmega3R1

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter
open scoped Classical Topology

/-- The full arbitrary-saving BV remainder is paid on the original scale. -/
theorem R1_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Z : ℝ,
      omega3SieveR1 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S Z (W N) ≤
        ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,T,_,hBV⟩ := R1_log_saving hδ hδhi (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C/(ε*wuSingularSeries 1))))
  refine ⟨max 4 (max T M),le_max_left _ _,?_⟩
  intro N hN Z
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hbudget : C/log (N : ℝ) ≤ ε*wuSingularSeries N := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hC1)).mp (hM N (by omega))
    have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hseries hε.le) hlog.le
    dsimp only [Function.comp_apply] at h
    nlinarith
  have hb := hBV N (by omega) Z
  have hb' : omega3SieveR1 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S Z (W N) ≤
      C*N/log (N : ℝ)^(3 : ℕ) := by convert hb using 1; norm_num
  calc
    _ ≤ C*N/log (N : ℝ)^(3 : ℕ) := hb'
    _ = (C/log (N : ℝ))*((N : ℝ)/log (N : ℝ)^2) := by ring
    _ ≤ (ε*wuSingularSeries N)*((N : ℝ)/log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

/-- The original roughness condition allows repeated p1 and p2. -/
theorem cofactor_prime_lower {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) {c : Omega3CofactorIndex}
    (hc : c ∈ omega3CofactorLabels N δ s S (W N)) :
    ∀ q, q.Prime → q ∣ omega3CofactorValue c → (N : ℝ)^(1/25 : ℝ) ≤ q := by
  rcases c with ⟨d,p2,p1,n⟩
  obtain ⟨hd,h2,h1,_,_,_,hgood⟩ := mem_omega3CofactorLabels.mp hc
  have hdP : d ∈ P N := (support N) ▸ hd
  have hlow := inner_lower_cutoff hN hδ hδhi hdP
  intro q hq hqe
  exact omega3_cofactor_prime_lower (mem_primeWindow.mp h1).1 (mem_primeWindow.mp h2).1
    (fun r hr hrd => by
      have heq : r = d := (Nat.dvd_prime (mem_primeWindow.mp hdP).1).mp hrd |>.resolve_left hr.ne_one
      subst r
      exact (rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num [left])).trans
          (mem_primeWindow.mp hdP).2.2.1)
    (hlow.trans (mem_primeWindow.mp h1).2.2.1)
    (hlow.trans (mem_primeWindow.mp h2).2.2.1) hgood.2.2 hq hqe

/-- Fixed power-log errors are negligible at the original singular-series scale. -/
theorem power_log_scale_paid (m : ℕ) {ε C η : ℝ}
    (hε : 0 < ε) (hC : 0 < C) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      C*N*log N^m/(N : ℝ)^η ≤ ε*truncatedSixthMassScale N := by
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget (m+2)
      (show 0 < C/(ε*wuSingularSeries 1) by positivity) hη)
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  calc
    _ ≤ C*N*log N^m/((C/(ε*wuSingularSeries 1))*log (N : ℝ)^(m+2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (hT N (by omega))
    _ = ε*wuSingularSeries 1*((N : ℝ)/log N^2) := by rw [pow_add]; field_simp
    _ ≤ ε*wuSingularSeries N*((N : ℝ)/log N^2) := by gcongr
    _ = _ := by unfold truncatedSixthMassScale; ring

/-- Euler payment of the actual full-cofactor R2, at floor(Q)+1. -/
theorem R2_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      omega3SieveR2 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s S
        (sqrt ((N : ℝ)^(1/2-δ))) (W N) ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,hbound⟩ := omega3_non_coprime_euler_bound
  obtain ⟨T1,hT14,hT1⟩ := power_log_scale_paid 5 hε
    (show 0 < 2*C*(25 : ℝ)^3/log 2 by positivity) (show (0 : ℝ) < 1/25 by norm_num)
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hlog1 := hT2 N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  have hg := omega3_source_sieve_geometry hN2 hδ (show δ < 1/2 by linarith)
  have hm : ∀ q ∈ omega3SieveModuli N (⌊(N : ℝ)^(1/2-δ)⌋₊+1)
      (sqrt ((N : ℝ)^(1/2-δ))), q ≤ N := by
    intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    omega
  have hb := hbound N (by omega) 1 δ s S (sqrt ((N : ℝ)^(1/2-δ)))
    ((N : ℝ)^(1/25 : ℝ)) ((25 : ℝ)^3) (W N)
    (omega3SieveModuli N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) (sqrt ((N : ℝ)^(1/2-δ))))
    hg.2.2.2.1 (by positivity) (by positivity) (filter_subset _ _) hm
    (fun c hc => ⟨(cofactor_profile_geometry hN2 hδ hδhi hc).1,
      (cofactor_profile_geometry hN2 hδ hδhi hc).2.1,cofactor_prime_lower hN2 hδ hδhi hc⟩)
    (cofactor_fibre_weight hN2 hδ hδhi)
  calc
    _ ≤ C*(25 : ℝ)^3*N*((1+log N)*log N^4/((N : ℝ)^(1/25 : ℝ)*log 2)) := hb
    _ ≤ C*(25 : ℝ)^3*N*((2*log N)*log N^4/((N : ℝ)^(1/25 : ℝ)*log 2)) := by
      gcongr
      linarith
    _ = (2*C*(25 : ℝ)^3/log 2)*N*log N^5/(N : ℝ)^(1/25 : ℝ) := by ring
    _ ≤ _ := hT1 N (by omega)

end Wu2008DoubleSieve.HighSix.Omega3Upper
