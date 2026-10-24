import WR2GammaHighTailFibre
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitErrorInputs

noncomputable section
namespace WuPaper.R2GammaHigh.Tail
open Wu2008DoubleSieve HighNonunit HighBoxRecovery Real Finset Filter
open scoped Classical Topology

/-- Relative roughness uses the original mask, including its selected prefix primes. -/
theorem relative_rough {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Bool)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) {x : Profile}
    (hx : x ∈ (sourceFamily j N δ k).labels) :
    ∀ r, r.Prime → r ∣ cofactor x → r.Coprime N → (N:ℝ)^highEta ≤ r := by
  have hx : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k :=
    (mem_filter.mp hx).1
  have hW : ∀ a q, q ∈ windows j N a → q.Prime ∧ (N:ℝ)^highEta ≤ (q:ℝ) := by
    intro a q hq
    have hg := prime_geometry j hN hδ hδhi hq
    exact ⟨hg.1,hg.2.2.1⟩
  obtain ⟨hd, hpre, hm, _, hs, _⟩ := profile_data hx
  have hpen := LowerTriple.window_lower j hN hδ hδhi hd hm
  have hprefix := RelativeRoughness.masked_prefix x.2.1 hs hpen.2
    (fun q hq hqd => omega3_support_prime_lower _ hW hd hq hqd)
    (fun r hr => LowerTriple.window_lower j hN hδ hδhi hd (hpre r hr))
  have hlast : ∀ q : ℕ, q.Prime → q ∣ x.2.2.1 → q.Coprime N →
      (N : ℝ)^(highEta) ≤ (q : ℝ) := by
    intro q hq hqd _
    have heq : q = x.2.2.1 := ((Nat.dvd_prime hpen.1).mp hqd).resolve_left hq.ne_one
    simpa only [heq] using hpen.2
  have hfull := RelativeRoughness.mul hprefix hlast
  simpa only [cofactor, List.prod_append, List.prod_singleton, mul_assoc, mul_left_comm,
    mul_comm] using hfull


theorem R2_bound {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ j : Fin 3, ∀ k : Bool,
      (sourceFamily j N δ k).R2 (⌊(N : ℝ)^(1/2-δ)⌋₊+1)
        (sqrt ((N : ℝ)^(1/2-δ))) ≤
          C*(max 1 (1/highEta))^6*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2)) := by
  obtain ⟨C,hC,hc⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  refine ⟨C,hC,fun N hN j k => ?_⟩
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  apply hc N (by omega) Profile (sourceFamily j N δ k) _ _ _ _ hg.2.2.2.1
    (by positivity) (by positivity) ?_ ?_ ?_
  · intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    omega
  · exact fun x hx => relative_rough j k (by omega) hd hh hx
  · exact fixed_cofactor_bound j k (by omega) hd hh

theorem R2_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Bool,
      (sourceFamily j N δ k).R2 (⌊(N : ℝ)^(1/2-δ)⌋₊+1)
        (sqrt ((N : ℝ)^(1/2-δ))) ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,hb⟩ := R2_bound hd hh
  have hK : 0 < 2*C*(max 1 (1/highEta))^6/log 2 := by positivity
  obtain ⟨T0,hT0,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 5 he hK
    (show 0 < highEta by norm_num [highEta])
  obtain ⟨T1,hl⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),fun N hN j k => ?_⟩
  have hlog := hl N (by omega)
  dsimp only [Function.comp_apply] at hlog
  calc
    _ ≤ C*(max 1 (1/highEta))^6*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2)) :=
      hb N (by omega) j k
    _ ≤ C*(max 1 (1/highEta))^6*N*((2*log N)*log N^4/((N : ℝ)^highEta*log 2)) := by
      gcongr
      linarith
    _ = (2*C*(max 1 (1/highEta))^6/log 2)*N*log N^5/(N : ℝ)^highEta := by ring
    _ ≤ _ := hp N (by omega)

end WuPaper.R2GammaHigh.Tail
#print axioms WuPaper.R2GammaHigh.Tail.R2_paid
