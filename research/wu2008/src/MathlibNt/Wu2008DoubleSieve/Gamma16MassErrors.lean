import MathlibNt.Wu2008DoubleSieve.Gamma16Quadrature
import MathlibNt.Wu2008DoubleSieve.Gamma16MassGeometry
import MathlibNt.Wu2008DoubleSieve.Omega3XErrorBudget

/-! # Four-prime reciprocal mass and both exceptional-divisor payments -/

namespace Wu2008DoubleSieve

open Finset Set Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem gamma16_reciprocal_mass {R : ℝ} (hR : 1 < R)
    (hm : ∑ p ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta), 1 / (p : ℝ) ≤ 5) :
    ∑ p ∈ gamma16MassPrimes R,
      1 / ((p.2.1 : ℝ) * p.2.2.1 * p.2.2.2 * p.1) ≤ 625 := by
  let P := primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta)
  let T : Finset Gamma16MassTuple := P.sigma fun _ => P.sigma fun _ => P.sigma fun _ => P
  have hsub : gamma16MassPrimes R ⊆ T := by
    intro p hp
    obtain ⟨h4, h1, h2, h3, hlo, h12, h23, h34, hhi⟩ :=
      gamma16_mass_prime_bounds (by linarith) hp
    have h12' : (p.2.1 : ℝ) ≤ p.2.2.1 := by exact_mod_cast h12.le
    have h23' : (p.2.2.1 : ℝ) ≤ p.2.2.2 := by exact_mod_cast h23.le
    have h34' : (p.2.2.2 : ℝ) ≤ p.1 := by exact_mod_cast h34
    have hmem (q : ℕ) := mem_primesIcc (a := R ^ gamma16Alpha) (p := q)
      (rpow_nonneg (by linarith : 0 ≤ R) gamma16Beta)
    exact mem_sigma.mpr ⟨(hmem _).mpr ⟨h4, hlo.trans (h12'.trans (h23'.trans h34')), hhi⟩,
      mem_sigma.mpr ⟨(hmem _).mpr ⟨h1, hlo, h12'.trans (h23'.trans (h34'.trans hhi))⟩,
      mem_sigma.mpr ⟨(hmem _).mpr ⟨h2, hlo.trans h12', h23'.trans (h34'.trans hhi)⟩,
        (hmem _).mpr ⟨h3, hlo.trans (h12'.trans h23'), h34'.trans hhi⟩⟩⟩⟩
  calc
    _ ≤ ∑ p ∈ T, 1 / ((p.2.1 : ℝ) * p.2.2.1 * p.2.2.2 * p.1) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ p ∈ P, 1 / (p : ℝ)) ^ 4 := by
      simp only [T, sum_sigma]
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
      simp only [sum_mul, mul_sum]
      apply sum_congr rfl
      intro p4 _
      apply sum_congr rfl
      intro p1 _
      apply sum_congr rfl
      intro p2 _
      apply sum_congr rfl
      intro p3 _
      ring
    _ ≤ 5 ^ 4 := pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hm 4
    _ = _ := by norm_num

theorem gamma16_mass_scale_sum {N d : ℕ} {R : ℝ} (hR : 1 < R)
    (hm : ∑ p ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta), 1 / (p : ℝ) ≤ 5) :
    ∑ p ∈ gamma16MassPrimes R, gamma16MassScale N d p ≤ 625 * (N : ℝ) / d := by
  calc
    _ = ((N : ℝ) / d) * ∑ p ∈ gamma16MassPrimes R,
        1 / ((p.2.1 : ℝ) * p.2.2.1 * p.2.2.2 * p.1) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      unfold gamma16MassScale
      ring
    _ ≤ ((N : ℝ) / d) * 625 :=
      mul_le_mul_of_nonneg_left (gamma16_reciprocal_mass hR hm) (by positivity)
    _ = _ := by ring

theorem gamma16_repeated_mass_finite {N d : ℕ} {R Y : ℝ} (hR : 1 < R) (hY : 0 < Y)
    (hm : ∑ p ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta), 1 / (p : ℝ) ≤ 5)
    (hl : ∀ p ∈ gamma16MassPrimes R, Y ≤ (p.2.1 : ℝ) ∧ Y ≤ (p.2.2.1 : ℝ)) :
    ∑ p ∈ gamma16MassPrimes R,
      ((⌊gamma16MassScale N d p / p.2.1⌋₊ : ℝ) + ⌊gamma16MassScale N d p / p.2.2.1⌋₊) ≤
        1250 * (N : ℝ) / (d * Y) := by
  calc
    _ ≤ ∑ p ∈ gamma16MassPrimes R, (2 / Y) * gamma16MassScale N d p := by
      apply sum_le_sum
      intro p hp
      have hx : 0 ≤ gamma16MassScale N d p := by unfold gamma16MassScale; positivity
      have h1 := (Nat.floor_le (div_nonneg hx (Nat.cast_nonneg _))).trans
        (div_le_div_of_nonneg_left hx hY (hl p hp).1)
      have h2 := (Nat.floor_le (div_nonneg hx (Nat.cast_nonneg _))).trans
        (div_le_div_of_nonneg_left hx hY (hl p hp).2)
      calc
        _ ≤ gamma16MassScale N d p / Y + gamma16MassScale N d p / Y := add_le_add h1 h2
        _ = _ := by ring
    _ = (2 / Y) * ∑ p ∈ gamma16MassPrimes R, gamma16MassScale N d p := (mul_sum ..).symm
    _ ≤ (2 / Y) * (625 * (N : ℝ) / d) :=
      mul_le_mul_of_nonneg_left (gamma16_mass_scale_sum hR hm) (by positivity)
    _ = _ := by ring

theorem gamma16_buchstab_error_mass {N d : ℕ} {R L : ℝ} (hR : 1 < R) (hL : 0 < L)
    (hm : ∑ p ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta), 1 / (p : ℝ) ≤ 5)
    (hl : ∀ p ∈ gamma16MassPrimes R, L ≤ log (p.2.2.2 : ℝ)) :
    ∑ p ∈ gamma16MassPrimes R, gamma16MassScale N d p / log p.2.2.2 ≤
      625 * (N : ℝ) / (d * L) := by
  calc
    _ ≤ ∑ p ∈ gamma16MassPrimes R, gamma16MassScale N d p / L := by
      apply sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left (by unfold gamma16MassScale; positivity) hL (hl p hp)
    _ = (∑ p ∈ gamma16MassPrimes R, gamma16MassScale N d p) / L := (Finset.sum_div ..).symm
    _ ≤ (625 * (N : ℝ) / d) / L :=
      div_le_div_of_nonneg_right (gamma16_mass_scale_sum hR hm) hL.le
    _ = _ := by ring

theorem gamma16_source_quadrature (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (∑ p ∈ primesIcc
          (((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma16Alpha)
          (((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma16Beta), 1 / (p : ℝ) ≤ 5) ∧
        |gamma16PrimeKernelSum ((N : ℝ) ^ (1 / 2 - δ) / d) (omega3XPhi N d δ) -
          gamma16FourthIntegral (omega3XPhi N d δ)| < ε := by
  have hlam := wuLocalExponent_pos k hδ hδhi
  have hlamhi : wuLocalExponent k δ ≤ 1 / 2 := by
    exact (min_le_right _ _).trans (by linarith : 1 / 2 - δ ≤ 1 / 2)
  have hcap : 2 ≤ 1 / wuLocalExponent k δ := (le_div_iff₀ hlam).mpr (by linarith)
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    ((gamma16_fourfold_prime_quadrature (1 / wuLocalExponent k δ) ε hcap hε).and
      gamma16_prime_mass_eventually)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hlam).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb d hd
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hR := hR0 _ ((hT N ((le_max_right _ _).trans hN)).trans hg.1)
  have hφ : 2 ≤ omega3XPhi N d δ := by
    have hh : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    linarith [hg.2.2.1]
  exact ⟨hR.2, hR.1 _ hφ hg.2.2.2⟩

end Wu2008DoubleSieve
