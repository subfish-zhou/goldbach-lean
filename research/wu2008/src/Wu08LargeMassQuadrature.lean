import Wu08LargeMassActual

noncomputable section
open Finset Real Set
open scoped Classical
open Wu2008DoubleSieve FourRoughClosedMass LiLiuPrereqBuchstab
namespace Wu08FirstPrimeFour.Large

theorem partial_first_primes {N : ℕ} (hN : 1 < N) :
    (primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^FourRoughClosedMass.beta)).filter
      (fun a : ℕ => (N : ℝ)^(1/10 : ℝ) ≤ (a : ℝ)) =
      primesIcc ((N : ℝ)^(1/10 : ℝ)) ((N : ℝ)^FourRoughClosedMass.beta) := by
  have hpow : (N : ℝ)^FourRoughClosedMass.alpha ≤ (N : ℝ)^(1/10 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) cutoff_geometry.1.1
  ext a
  rw [mem_filter]
  simp only [mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) FourRoughClosedMass.beta)]
  constructor
  · rintro ⟨⟨hp,_,hu⟩,hl⟩
    exact ⟨hp,hl,hu⟩
  · rintro ⟨hp,hl,hu⟩
    exact ⟨⟨hp,hpow.trans hl,hu⟩,hl⟩

theorem closed_main_nested {N : ℕ} (hN : 1 < N) (e : Bool) :
    mainMass N (closedLabels N e) =
      ∑ a ∈ primesIcc ((N : ℝ)^(1/10 : ℝ)) ((N : ℝ)^FourRoughClosedMass.beta),
      ∑ b ∈ primesIcc a ((N : ℝ)^FourRoughClosedMass.beta),
      ∑ c ∈ primesIcc b ((N : ℝ)^FourRoughClosedMass.beta),
      ∑ d ∈ primesIcc (if e then (N : ℝ)^FourRoughClosedMass.beta else c)
        (if e then (N : ℝ)^lam/c else (N : ℝ)^FourRoughClosedMass.beta),
        density (coord N a) (coord N b) (coord N c) (coord N d)/(a*b*c*d : ℝ) := by
  have heq : LastPrimeFour.fourClosedLabels N e = labelSet N e := (labelSet_eq N e).symm
  rw [mainMass,closedLabels,heq,sum_filter,labelSet]
  have nested (f : TruncatedFourPhysical.Quad → ℝ) (l u : ℕ → ℝ) :
      (∑ q ∈ FourRoughClosedMass.labels N l u, f q) =
        ∑ a ∈ primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^FourRoughClosedMass.beta),
        ∑ b ∈ primesIcc a ((N : ℝ)^FourRoughClosedMass.beta),
        ∑ c ∈ primesIcc b ((N : ℝ)^FourRoughClosedMass.beta),
        ∑ d ∈ primesIcc (l c) (u c), f (a,b,c,d) := by
    simp only [FourRoughClosedMass.labels,sum_map,sum_sigma]
    rfl
  rw [nested,← partial_first_primes hN,sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : (N : ℝ)^(1/10 : ℝ) ≤ a
  · simp only [ha,↓reduceIte,mainTerm,fourModulusProduct,Nat.cast_mul]
  · simp only [ha,↓reduceIte,sum_const_zero]

/-- Exact partial closed arithmetic mass, with the lower endpoint retained. -/
theorem closed_main_eq_Q {N : ℕ} (hN : 1 < N) (e : Bool) :
    mainMass N (closedLabels N e) = Q N e := by
  rw [closed_main_nested hN e]
  unfold Q primeOrderedClosedSum
  apply sum_congr rfl
  intro a ha
  have hca0 := closed_coord hN ha
  have hca : coord N a ∈ Icc FourRoughClosedMass.alpha FourRoughClosedMass.beta :=
    ⟨cutoff_geometry.1.1.trans hca0.1,hca0.2⟩
  have hpa := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) FourRoughClosedMass.beta)).mp ha).1
  have haold : a ∈ primesIcc ((N : ℝ)^FourRoughClosedMass.alpha) ((N : ℝ)^FourRoughClosedMass.beta) :=
    (mem_filter.mp ((partial_first_primes hN).symm ▸ ha)).1
  unfold Q1 primeOrderedClosedSum
  simp only [← coord_eq_log]
  rw [cap_eq hca,rpow_coord hN hpa.pos,sum_div]
  apply sum_congr rfl
  intro b hb
  have hcb := prime_row_coord hN hca hpa.pos hb
  have hpb := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) FourRoughClosedMass.beta)).mp hb).1
  unfold Q2 primeOrderedClosedSum
  simp only [← coord_eq_log]
  rw [cap_eq hcb,rpow_coord hN hpb.pos,sum_div,sum_div]
  apply sum_congr rfl
  intro c hc
  have hcc := prime_row_coord hN hcb hpb.pos hc
  have hpc := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) FourRoughClosedMass.beta)).mp hc).1
  unfold Q3 primeOrderedClosedSum
  simp only [← coord_eq_log]
  obtain ⟨hl,hu⟩ := last_windows hN hpc.pos hcc e
  rw [hl,hu,sum_div,sum_div,sum_div]
  apply sum_congr rfl
  intro d hd
  have hq : (a,b,c,d) ∈ labelSet N e := mem_labels.mpr ⟨haold,hb,hc,hd⟩
  rw [F_actual hN e hq]
  ring

theorem actual_mass_integral_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool,
      (family N e).mass ≤ (I e+ε)*((N : ℝ)/log N) := by
  have hh : 0 < ε/2 := by positivity
  obtain ⟨T1,hT1,h1⟩ := actual_mass_main_paid hh
  obtain ⟨T2,_,h2⟩ := partial_quadrature hh
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN e
  have hn : 1 < N := by omega
  have hm := h1 N (by omega) e
  rw [closed_main_eq_Q hn e] at hm
  have hq := (abs_lt.mp (h2 N (by omega) e)).2
  have he : Q N e+ε/2 ≤ I e+ε := by linarith only [hq]
  exact hm.trans (mul_le_mul_of_nonneg_right he (div_nonneg (Nat.cast_nonneg N)
    (log_pos (by exact_mod_cast hn)).le))

#print axioms closed_main_eq_Q
#print axioms actual_mass_integral_paid
end Wu08FirstPrimeFour.Large
