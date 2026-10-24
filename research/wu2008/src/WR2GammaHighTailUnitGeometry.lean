import WR2GammaHighTailUnitLimit
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveMultiplicity

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve HighBoxRecovery Finset
open scoped Classical

theorem selected_lower {n N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d))
    (hd : c.1 ∈ boxConvolutionSupport (windows row N)) (j : Fin n) :
    (selected c j).Prime ∧ (N : ℝ) ^ (highEta) ≤ selected c j := by
  have hg := LowerTriple.phi_bounds row hN hδ hδhi hd
  have hm := (LiLiuPrereqBuchstab.mem_primesIcc
    (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1/2-δ)/c.1) _)).mp (c.2 j).property
  refine ⟨hm.1, le_trans ?_ hm.2.1⟩
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hg.1
    (by norm_num : (0 : ℝ) ≤ 1/10)
  simpa only [← Real.rpow_mul (Nat.cast_nonneg N), show (10*highEta)*(1/10:ℝ) = highEta by ring] using hp

theorem source_profile_geometry {n N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1/2-δ)/d)))
    (j : Fin n) (b : ℕ → ℝ)
    {c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d)}
    (hc : c ∈ family N (windows row N) P j b) :
    Geometry N (highEta) b j c := by
  obtain ⟨hd, _, hf⟩ := mem_family.mp hc
  have hR := (LowerTriple.phi_bounds row hN hδ hδhi hd).2.1
  have hd0 : 0 < c.1 := boxConvolutionSupport_pos
    (fun j q hq => (mem_primeWindow.mp hq).1.pos) hd
  have hA := cofactor_pos c hd0 hR
  have hAr : (0 : ℝ) < cofactor c := by exact_mod_cast hA
  have hsel := selected_lower row hN hδ hδhi c hd
  have htwo : 2 ≤ lower j c := by
    change (2 : ℝ) ≤ (selected c j : ℝ)
    exact_mod_cast (hsel j).1.two_le
  have hsize : (cofactor c : ℝ) * upper N b c ≤ N := by
    have hu : upper N b c ≤ (N : ℝ) / cofactor c := min_le_right _ _
    have h := (le_div_iff₀ hAr).mp hu
    exact (mul_comm _ _).trans_le h
  have hprod : cofactor c * selected c j ≤ N := by
    have hp : (cofactor c : ℝ) * (selected c j : ℝ) ≤ N :=
      (mul_le_mul_of_nonneg_left hf hAr.le).trans hsize
    exact_mod_cast hp
  have heN : cofactor c ≤ N := (Nat.le_mul_of_pos_right _ (hsel j).1.pos).trans hprod
  refine ⟨hA, heN, (hsel j).2.trans ?_, omega3_cofactor_power_gap (by omega) (hsel j).2 hprod,
    htwo, hf, hsize, fun t => ⟨(hsel t).1, selected_dvd c t, (hsel t).2⟩⟩
  exact_mod_cast Nat.le_of_dvd hA (selected_dvd c j)

theorem source_profile_rough {n N : ℕ} {δ : ℝ} (row : Fin 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hW : ∀ j q, q ∈ windows row N j →
      q.Prime ∧ (N : ℝ) ^ (highEta) ≤ (q : ℝ))
    (c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d))
    (hd : c.1 ∈ boxConvolutionSupport (windows row N)) :
    ∀ q, q.Prime → q ∣ cofactor c → (N : ℝ) ^ (highEta) ≤ (q : ℝ) := by
  intro q hq hqc
  rcases hq.dvd_mul.mp hqc with h | h
  · exact omega3_support_prime_lower _ hW hd hq h
  · exact product_rough (selected_lower row hN hδ hδhi c hd) hq h

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.source_profile_geometry
#print axioms WuPaper.R2GammaHigh.TailUnit.source_profile_rough
