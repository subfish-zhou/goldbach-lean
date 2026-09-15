import Wu18938Campaign.M1.Confirmed.Buchstab
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveInstance

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Unit

open Wu2008DoubleSieve HighUnitSieve SecondFunctionalUnitPrimeFibre Finset Real
open scoped Classical

variable {m i n N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)

include hb hN hη hδ

theorem selected_large (c : Profile n (fun d => (N : ℝ) ^ (1 / 2 - δ) / d))
    (hd : c.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (j : Fin n) :
    (selected c j).Prime ∧ (N : ℝ) ^ (η / 10) ≤ (selected c j : ℝ) := by
  have hg := hb.support_geometry hN hη hδ hd
  have hm := (LiLiuPrereqBuchstab.mem_primesIcc
    (rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / c.1) _)).mp (c.2 j).property
  refine ⟨hm.1, le_trans ?_ hm.2.1⟩
  have hp := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) _) (hb.remaining c.1 hd)
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
  simpa only [← rpow_mul (Nat.cast_nonneg N), div_eq_mul_inv, one_mul] using hp

theorem profile_geometry
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
    (j : Fin n) (b : ℕ → ℝ)
    {c : Profile n (fun d => (N : ℝ) ^ (1 / 2 - δ) / d)}
    (hc : c ∈ family N (convolutionWuWindows N Δ V) P j b) :
    Geometry N (η / 10) b j c := by
  obtain ⟨hd, _, hf⟩ := mem_family.mp hc
  have hR := (hb.support_geometry hN hη hδ hd).2.2.1
  have hA := cofactor_pos c (hb.support_pos hd) hR
  have hAr : (0 : ℝ) < cofactor c := by exact_mod_cast hA
  have hsel := selected_large hb hN hη hδ c hd
  have htwo : 2 ≤ lower j c := by
    change (2 : ℝ) ≤ (selected c j : ℝ)
    exact_mod_cast (hsel j).1.two_le
  have hsize : (cofactor c : ℝ) * upper N b c ≤ N := by
    have hu : upper N b c ≤ (N : ℝ) / cofactor c := min_le_right _ _
    exact (mul_comm _ _).trans_le ((le_div_iff₀ hAr).mp hu)
  have hprod : cofactor c * selected c j ≤ N := by
    have ht : (cofactor c : ℝ) * (selected c j : ℝ) ≤ N :=
      (mul_le_mul_of_nonneg_left hf hAr.le).trans hsize
    exact_mod_cast ht
  have heN := (Nat.le_mul_of_pos_right _ (hsel j).1.pos).trans hprod
  refine ⟨hA, heN, (hsel j).2.trans ?_,
    omega3_cofactor_power_gap (by omega) (hsel j).2 hprod, htwo, hf, hsize,
    fun t => ⟨(hsel t).1, selected_dvd c t, (hsel t).2⟩⟩
  exact_mod_cast Nat.le_of_dvd hA (selected_dvd c j)

theorem profile_rough
    (c : Profile n (fun d => (N : ℝ) ^ (1 / 2 - δ) / d))
    (hd : c.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    ∀ q, q.Prime → q ∣ cofactor c → (N : ℝ) ^ (η / 10) ≤ (q : ℝ) := by
  intro q hq hqc
  rcases hq.dvd_mul.mp hqc with h | h
  · exact omega3_support_prime_lower _ (roughBox_window_tenth hb hN hη) hd hq h
  · exact product_rough (selected_large hb hN hη hδ c hd) hq h

def physicalFamily
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
    (j : Fin n) (b : ℕ → ℝ) :
    LabelledPhysical.Family (Profile n (fun d => (N : ℝ) ^ (1 / 2 - δ) / d)) N where
  labels := family N (convolutionWuWindows N Δ V) P j b
  weight := fun c => (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)
  cofactor := cofactor
  lower := lower j
  upper := upper N b
  weight_nonneg := fun _ _ => Nat.cast_nonneg _
  geometry := fun c hc => by
    have h := profile_geometry hb hN hη hδ P j b hc
    exact ⟨h.positive, h.lower_two, h.feasible, h.physical⟩

theorem physicalFamily_primes
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
    (j : Fin n) (b : ℕ → ℝ)
    {c : Profile n (fun d => (N : ℝ) ^ (1 / 2 - δ) / d)}
    (hc : c ∈ family N (convolutionWuWindows N Δ V) P j b) :
    (physicalFamily hb hN hη hδ P j b).primes c = fibre (lower j c) (upper N b c) := by
  have h := profile_geometry hb hN hη hδ P j b hc
  exact (interval_eq_profile h.positive h.lower_two h.feasible h.physical).symm

theorem physicalFamily_mass
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
    (j : Fin n) (b : ℕ → ℝ) :
    (physicalFamily hb hN hη hδ P j b).mass =
      intervalMass N (convolutionWuWindows N Δ V)
        (family N (convolutionWuWindows N Δ V) P j b) j b := by
  unfold LabelledPhysical.Family.mass intervalMass
  exact sum_congr rfl (fun c hc => by rw [physicalFamily_primes hb hN hη hδ P j b hc]; rfl)

theorem physicalFamily_primeMass
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
    (j : Fin n) (b : ℕ → ℝ) :
    (physicalFamily hb hN hη hδ P j b).primeMass =
      outputMass N (convolutionWuWindows N Δ V)
        (family N (convolutionWuWindows N Δ V) P j b) j b := by
  unfold LabelledPhysical.Family.primeMass outputMass
  exact sum_congr rfl (fun c hc => by rw [physicalFamily_primes hb hN hη hδ P j b hc]; rfl)

theorem physicalFamily_small
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
    (j : Fin n) (b : ℕ → ℝ) {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : Z < N) :
    (physicalFamily hb hN hη hδ P j b).small Z ≤
      (max 1 (1 / (η / 10))) ^ (m + n + 1) * Z := by
  have hle : (physicalFamily hb hN hη hδ P j b).small Z ≤
      smallOutputMassReal N Z (convolutionWuWindows N Δ V)
        (family N (convolutionWuWindows N Δ V) P j b) j b := by
    unfold LabelledPhysical.Family.small smallOutputMassReal
    apply sum_le_sum
    intro c hc
    rw [physicalFamily_primes hb hN hη hδ P j b hc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro q hq
    obtain ⟨hq, hp, hz⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hq, hp, hz.le⟩
  exact hle.trans (small_output_real_le _ _ j hb.depth (by omega) (by positivity)
    hZ0 hZ (roughBox_window_tenth hb hN hη) (fun _ hc => profile_geometry hb hN hη hδ P j b hc))

theorem physicalFamily_fibre
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)))
    (j : Fin n) (b : ℕ → ℝ) (e : ℕ) :
    let L := physicalFamily hb hN hη hδ P j b
    (∑ c ∈ L.layerFibre e, L.weight c) ≤ (max 1 (1 / (η / 10))) ^ (m + n) := by
  let S := (family N (convolutionWuWindows N Δ V) P j b).filter (fun c => cofactor c = e)
  by_cases hs : S.Nonempty
  · obtain ⟨c, hc⟩ := hs
    obtain ⟨hc, he⟩ := mem_filter.mp hc
    have hg := profile_geometry hb hN hη hδ P j b hc
    apply weighted_fibre_le _ S hb.depth (by omega) (he ▸ hg.positive) (he ▸ hg.le_N)
      (by positivity) (roughBox_window_tenth hb hN hη)
    · exact fun _ hc => (mem_filter.mp hc).2
    · intro c hc t
      obtain ⟨hc, he⟩ := mem_filter.mp hc
      have ht := (profile_geometry hb hN hη hδ P j b hc).selected_large t
      exact ⟨ht.1, he ▸ ht.2.1, ht.2.2⟩
  · change (∑ c ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

end Wu18938Campaign.M1.Confirmed.Unit
