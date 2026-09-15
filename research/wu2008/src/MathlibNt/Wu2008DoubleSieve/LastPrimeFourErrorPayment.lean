import MathlibNt.Wu2008DoubleSieve.LastPrimeFourSieveCore
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledMissingMass
import MathlibNt.Wu2008DoubleSieve.NinthErrorPaymentAsymptotic

/-! Original-alpha roughness and fixed-fibre full Euler payment. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real Filter
open scoped Classical Topology

noncomputable abbrev alpha : ℝ := truncatedSixthLowerAlpha

theorem four_cofactor_rough {N : ℕ} {e : Bool} {t : Index}
    (ht : t ∈ labels N e) {p : ℕ} (hp : p.Prime) (hd : p ∣ cofactor t) :
    (N : ℝ)^alpha ≤ p := by
  obtain ⟨ha,_,hza,hb,_,hc,_,hab,hbc,_,_,hr⟩ := base_data (labels_base ht)
  have hzb : (N : ℝ)^alpha ≤ t.2.1 := hza.trans (by exact_mod_cast hab.le)
  have hzc : (N : ℝ)^alpha ≤ t.2.2.1 := hzb.trans (by exact_mod_cast hbc.le)
  rcases hp.dvd_mul.mp hd with habc | hn
  · rcases hp.dvd_mul.mp habc with hab' | hc'
    · rcases hp.dvd_mul.mp hab' with ha' | hb'
      · have he := ((Nat.dvd_prime ha).mp ha').resolve_left hp.ne_one
        simpa only [he, z, alpha] using hza
      · have he := ((Nat.dvd_prime hb).mp hb').resolve_left hp.ne_one
        simpa only [he] using hzb
    · have he := ((Nat.dvd_prime hc).mp hc').resolve_left hp.ne_one
      simpa only [he] using hzc
  · exact hzb.trans (hr p hp hn)

theorem four_fibre_weight {N : ℕ} (hN : 1 < N) (e : Bool) (m : ℕ) :
    (∑ t ∈ (family N e).labels.filter (fun t => (family N e).cofactor t = m),
      (family N e).weight t) ≤ (layerBound : ℝ) := by
  have h := fibre_card_le hN e m
  simpa only [family, LabelledPhysical.Family.layerFibre, sum_const,
    nsmul_eq_mul, mul_one] using (show (((family N e).layerFibre m).card : ℝ) ≤ layerBound by exact_mod_cast h)

theorem fourR2_eq (N : ℕ) (e : Bool) (D : ℕ) (Z : ℝ) :
    fourR2 N e D Z = (family N e).R2 D Z := by
  simp only [fourR2, fourMissingMass, LabelledPhysical.Family.R2,
    LabelledPhysical.Family.missing, LabelledPhysical.Family.primes, family, one_mul]
  rfl

theorem fourR2_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 512 ≤ N → ∀ e : Bool,
      ∀ D : ℕ, ∀ Z : ℝ,
      Z ≤ N → (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) →
      fourR2 N e D Z ≤
        C * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) := by
  obtain ⟨C,hC,hE⟩ := LabelledPhysical.Family.R2_euler.{0}
  refine ⟨C*((layerBound : ℝ)+1),by positivity,?_⟩
  intro N hN e D Z hZ hqN
  rw [fourR2_eq]
  have h := hE N (by omega) Index (family N e) D Z ((N : ℝ)^alpha)
    (layerBound : ℝ) hZ (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _)
    (Nat.cast_nonneg _) hqN (fun _ ht _ hp hd => four_cofactor_rough ht hp hd)
    (four_fibre_weight (by omega) e)
  calc
    _ ≤ C * (layerBound : ℝ) * N *
        ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) := h
    _ ≤ _ := by
      have := log_natCast_nonneg N
      gcongr
      linarith

theorem fourR2_source_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 512 ≤ N → ∀ e : Bool, ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      fourR2 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
      C * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) := by
  obtain ⟨C, hC, hb⟩ := fourR2_finite_bound
  refine ⟨C, hC, ?_⟩
  intro N hN e δ hδ hδhi
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hδ hδhi
  apply hb N hN e _ _ hg.2.2.2.1
  intro q hq
  have hqD := (omega3SieveModuli_properties hq).2.2.2
  have hDN := hg.2.2.2.2.2.2.1
  omega

theorem fourR2_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      fourR2 N e (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤ ε * N / log N ^ 2 := by
  obtain ⟨C, hC, hf⟩ := fourR2_source_bound
  obtain ⟨T1, hT1, hpay⟩ := ninth_power_log_error_budget 5
    (show 0 < 2 * C / log 2 by positivity) (by norm_num [alpha, truncatedSixthLowerAlpha] : 0 < alpha) hε
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hlogT⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN e δ hδ hδhi
  have hN1 := (le_max_left T1 T2).trans hN
  have hlog1 := hlogT N ((le_max_right _ _).trans hN)
  calc
    _ ≤ C * N * ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) :=
      hf N (hT1.trans hN1) e δ hδ hδhi
    _ ≤ C * N * ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ alpha * log 2)) := by
      gcongr
      linarith
    _ = (2 * C / log 2) * N * log N ^ 5 / (N : ℝ) ^ alpha := by ring
    _ ≤ _ := hpay N hN1

end Wu2008DoubleSieve.LastPrimeFour
