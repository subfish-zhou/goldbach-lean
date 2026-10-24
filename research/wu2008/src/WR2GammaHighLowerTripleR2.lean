import WR2GammaHighLowerTripleFibre
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleErrorInputs

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Real Finset Filter
open scoped Classical Topology

theorem relative_rough {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) {x : Label}
    (hx : x ∈ (sourceFamily j N δ k).labels) :
    ∀ r, r.Prime → r ∣ cofactor x → r.Coprime N → (N : ℝ)^highEta ≤ r := by
  obtain ⟨hm,hp,hq,_,_,_,_,hs,_⟩ := (mem_labels x).mp hx
  have hpl := window_lower j hN hd hh hm hp
  have hql := window_lower j hN hd hh hm hq
  apply RelativeRoughness.of_sifted hs hql.2
  intro r hr hrd hc
  rcases hr.dvd_mul.mp hrd with hdp | hNr
  · rcases hr.dvd_mul.mp hdp with hdv | hpv
    · apply omega3_support_prime_lower (windows j N) _ hm hr hdv
      intro a q hq
      have h := prime_geometry j hN hd hh hq
      exact ⟨h.1,h.2.2.1⟩
    · have he : r = x.2.1 := ((Nat.dvd_prime hpl.1).mp hpv).resolve_left hr.ne_one
      simpa only [he] using hpl.2
  · exact (hr.coprime_iff_not_dvd.mp hc hNr).elim

theorem R2_bound {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ j : Fin 3, ∀ k : Fin 6,
      (sourceFamily j N δ k).R2 (⌊(N : ℝ)^(1/2-δ)⌋₊+1)
        (sqrt ((N : ℝ)^(1/2-δ))) ≤
          C*(max 1 (1/highEta))^3*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2)) := by
  obtain ⟨C,hC,hc⟩ := LabelledPhysical.Family.R2_euler_relative.{0}
  refine ⟨C,hC,fun N hN j k => ?_⟩
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hd (by linarith : δ < 1/2)
  apply hc N (by omega) Label (sourceFamily j N δ k) _ _ _ _ hg.2.2.2.1
    (by positivity) (by positivity) ?_ ?_ ?_
  · intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    omega
  · exact fun x hx => relative_rough j k (by omega) hd hh hx
  · exact fixed_cofactor_bound j k (by omega) hd hh

theorem R2_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ k : Fin 6,
      (sourceFamily j N δ k).R2 (⌊(N : ℝ)^(1/2-δ)⌋₊+1)
        (sqrt ((N : ℝ)^(1/2-δ))) ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C,hC,hb⟩ := R2_bound hd hh
  have hK : 0 < 2*C*(max 1 (1/highEta))^3/log 2 := by positivity
  obtain ⟨T0,hT0,hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 5 he hK
    (show 0 < highEta by norm_num [highEta])
  obtain ⟨T1,hl⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),fun N hN j k => ?_⟩
  have hlog := hl N (by omega)
  dsimp only [Function.comp_apply] at hlog
  calc
    _ ≤ C*(max 1 (1/highEta))^3*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2)) :=
      hb N (by omega) j k
    _ ≤ C*(max 1 (1/highEta))^3*N*((2*log N)*log N^4/((N : ℝ)^highEta*log 2)) := by
      gcongr
      linarith
    _ = (2*C*(max 1 (1/highEta))^3/log 2)*N*log N^5/(N : ℝ)^highEta := by ring
    _ ≤ _ := hp N (by omega)

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.R2_paid
