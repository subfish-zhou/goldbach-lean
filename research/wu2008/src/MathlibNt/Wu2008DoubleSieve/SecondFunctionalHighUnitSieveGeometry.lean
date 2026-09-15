import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitPrimeOutput
import MathlibNt.Wu2008DoubleSieve.Gamma16Geometry
import MathlibNt.Wu2008DoubleSieve.Omega3R1Layers

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSieve
open Finset SecondFunctionalUnitPrimeFibre HighUnitPrimeOutput

/-- Every free coordinate is retained, with the actual dependent slab type. -/
abbrev Profile (n : ℕ) (R : ℕ → ℝ) := Σ d : ℕ, Fin n → primeSlabPrimes (R d)

def cofactor {n : ℕ} {R : ℕ → ℝ} (c : Profile n R) : ℕ :=
  c.1 * freeProduct c.2

noncomputable def lower {n : ℕ} {R : ℕ → ℝ} (j : Fin n) (c : Profile n R) : ℝ :=
  (c.2 j).val

noncomputable def upper {n : ℕ} {R : ℕ → ℝ} (N : ℕ) (b : ℕ → ℝ)
    (c : Profile n R) : ℝ := min (R c.1 ^ b c.1) ((N : ℝ) / cofactor c)

/-- The only deletion criterion is real interval geometry. -/
noncomputable def family {i n : ℕ} {R : ℕ → ℝ} (N : ℕ)
    (W : Fin i → Finset ℕ) (P : ∀ d, Finset (Fin n → primeSlabPrimes (R d)))
    (j : Fin n) (b : ℕ → ℝ) : Finset (Profile n R) :=
  ((boxConvolutionSupport W).sigma P).filter fun c => lower j c ≤ upper N b c

@[simp] theorem mem_family {i n N : ℕ} {R b : ℕ → ℝ}
    {W : Fin i → Finset ℕ} {P : ∀ d, Finset (Fin n → primeSlabPrimes (R d))}
    {j : Fin n} {c : Profile n R} :
    c ∈ family N W P j b ↔ c.1 ∈ boxConvolutionSupport W ∧ c.2 ∈ P c.1 ∧
      lower j c ≤ upper N b c := by
  simp [family, and_assoc]

theorem cofactor_pos {n : ℕ} {R : ℕ → ℝ} (c : Profile n R)
    (hd : 0 < c.1) (hR : 1 < R c.1) : 0 < cofactor c := by
  apply Nat.mul_pos hd
  exact_mod_cast (show (0 : ℝ) < (freeProduct c.2 : ℝ) by
    rw [freeProduct_cast]; exact prefixProduct_pos hR c.2)

/-- The old physical fibre is exactly the strict/closed prime interval. -/
theorem physical_interval {n N : ℕ} {R b : ℕ → ℝ} (j : Fin n) (c : Profile n R)
    (hd : 0 < c.1) (hR : 1 < R c.1) :
    physical (prefixProduct c.2) ((N : ℝ) / c.1) (c.2 j).val (R c.1 ^ b c.1) =
      fibre (lower j c) (upper N b c) := by
  rw [physical_eq (prefixProduct_pos hR c.2) (by positivity)
    (Real.rpow_nonneg (by linarith) _)]
  congr 1
  dsimp [upper, cofactor]
  rw [Nat.cast_mul, freeProduct_cast, div_div, min_comm]

theorem upper_nonneg {n N : ℕ} {R b : ℕ → ℝ} (c : Profile n R)
    (hR : 1 < R c.1) : 0 ≤ upper N b c := by
  apply le_min
  · exact Real.rpow_nonneg (by linarith) _
  · positivity

/-- Discarding a profile uses no primality test on the output. -/
theorem discarded_empty {n N : ℕ} {R b : ℕ → ℝ} (j : Fin n) (c : Profile n R)
    (hd : 0 < c.1) (hR : 1 < R c.1) (h : ¬ lower j c ≤ upper N b c) :
    physical (prefixProduct c.2) ((N : ℝ) / c.1) (c.2 j).val (R c.1 ^ b c.1) = ∅ := by
  rw [physical_interval j c hd hR]
  exact fibre_empty (upper_nonneg c hR) (le_of_lt (lt_of_not_ge h))

/-- Exact disintegration for arbitrary profile-dependent real tests. -/
theorem sum_interval {i n N : ℕ} {R b : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (P : ∀ d, Finset (Fin n → primeSlabPrimes (R d)))
    (j : Fin n) (f : Profile n R → ℕ → ℝ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d) :
    (∑ d ∈ boxConvolutionSupport W, ∑ g ∈ P d,
      ∑ q ∈ physical (prefixProduct g) ((N : ℝ)/d) (g j).val (R d ^ b d), f ⟨d,g⟩ q) =
    ∑ c ∈ family N W P j b, ∑ q ∈ fibre (lower j c) (upper N b c), f c q := by
  rw [family, sum_filter]
  rw [sum_sigma']
  apply sum_congr rfl
  intro c hc
  have hdW := (mem_sigma.mp hc).1
  rw [physical_interval j c (hd c.1 hdW) (hR c.1 hdW)]
  split_ifs with h
  · rfl
  · rw [fibre_empty (upper_nonneg c (hR c.1 hdW)) (le_of_lt (lt_of_not_ge h)), sum_empty]

/-- The range(N+1) in the existing profile API is redundant. -/
theorem interval_eq_profile {N A : ℕ} {l u : ℝ} (hA : 0 < A)
    (hl : 2 ≤ l) (hlu : l ≤ u) (hu : (A : ℝ) * u ≤ N) :
    fibre l u = omega3ProfilePrimes N l u := by
  have hu0 : 0 ≤ u := by linarith
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have huN : u ≤ N := (le_mul_of_one_le_left hu0 hA1).trans hu
  ext q
  rw [mem_fibre hu0, omega3ProfilePrimes, mem_filter, mem_range]
  constructor
  · intro h
    refine ⟨?_, h⟩
    have : q ≤ N := by exact_mod_cast h.2.2.trans huN
    omega
  · exact fun h => h.2

/-- The full four-coordinate word20 carrier. -/
noncomputable def family20 {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (R a2 a3 b : ℕ → ℝ) : Finset (Profile 4 R) :=
  family N W (fun d => HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d)) (Fin.last 3) b

/-- The full five-coordinate word21 carrier. -/
noncomputable def family21 {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (R a3 b : ℕ → ℝ) : Finset (Profile 5 R) :=
  family N W (fun d => HighUnit.primePrefix21 (R d) (a3 d) (b d)) (Fin.last 4) b

theorem weighted_card_interval {i n N : ℕ} {R b : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (P : ∀ d, Finset (Fin n → primeSlabPrimes (R d)))
    (j : Fin n) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * ∑ g ∈ P d,
      ((physical (prefixProduct g) ((N : ℝ)/d) (g j).val (R d ^ b d)).card : ℝ)) =
    ∑ c ∈ family N W P j b, (convolutionCoeff W c.1 : ℝ) *
      ((fibre (lower j c) (upper N b c)).card : ℝ) := by
  simpa only [sum_const, nsmul_eq_mul, mul_comm, mul_sum, sum_mul] using
    sum_interval W P j (fun c _ => (convolutionCoeff W c.1 : ℝ)) hd hR

theorem weighted_filtered_interval {i n N : ℕ} {R b : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (P : ∀ d, Finset (Fin n → primeSlabPrimes (R d)))
    (j : Fin n) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * ∑ g ∈ P d,
      ((filteredPhysical N d g j (R d ^ b d)).card : ℝ)) =
    ∑ c ∈ family N W P j b, (convolutionCoeff W c.1 : ℝ) *
      (((fibre (lower j c) (upper N b c)).filter
        (fun q => (N - cofactor c * q).Prime)).card : ℝ) := by
  have h := sum_interval (N := N) (b := b) W P j
    (fun c q => if (N - cofactor c * q).Prime then (convolutionCoeff W c.1 : ℝ) else 0) hd hR
  simpa only [filteredPhysical, cofactor, ← sum_filter, sum_const, nsmul_eq_mul,
    mul_comm, mul_sum, sum_mul] using h

theorem boxedSigma20_interval {i N : ℕ} {δ : ℝ}
    (W : Fin i → Finset ℕ) (a2 a3 b : ℕ → ℝ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < (N : ℝ) ^ (1/2-δ)/d) :
    HighUnit.boxedSigma20 N δ W a2 a3 b =
    ∑ c ∈ family20 N W (fun d => (N : ℝ) ^ (1/2-δ)/d) a2 a3 b,
      (convolutionCoeff W c.1 : ℝ) *
        ((fibre (lower (Fin.last 3) c) (upper N b c)).card : ℝ) :=
  weighted_card_interval W _ (Fin.last 3) hd hR

theorem boxedSigma21_interval {i N : ℕ} {δ : ℝ}
    (W : Fin i → Finset ℕ) (a3 b : ℕ → ℝ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < (N : ℝ) ^ (1/2-δ)/d) :
    HighUnit.boxedSigma21 N δ W a3 b =
    ∑ c ∈ family21 N W (fun d => (N : ℝ) ^ (1/2-δ)/d) a3 b,
      (convolutionCoeff W c.1 : ℝ) *
        ((fibre (lower (Fin.last 4) c) (upper N b c)).card : ℝ) :=
  weighted_card_interval W _ (Fin.last 4) hd hR

theorem envelope20_interval {i N : ℕ} (W : Fin i → Finset ℕ) (R a2 a3 b : ℕ → ℝ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d) :
    envelope20 N W R a2 a3 b =
    ∑ c ∈ family20 N W R a2 a3 b, (convolutionCoeff W c.1 : ℝ) *
      (((fibre (lower (Fin.last 3) c) (upper N b c)).filter
        (fun q => (N - cofactor c * q).Prime)).card : ℝ) :=
  weighted_filtered_interval W _ (Fin.last 3) hd hR

theorem envelope21_interval {i N : ℕ} (W : Fin i → Finset ℕ) (R a3 b : ℕ → ℝ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d) :
    envelope21 N W R a3 b =
    ∑ c ∈ family21 N W R a3 b, (convolutionCoeff W c.1 : ℝ) *
      (((fibre (lower (Fin.last 4) c) (upper N b c)).filter
        (fun q => (N - cofactor c * q).Prime)).card : ℝ) :=
  weighted_filtered_interval W _ (Fin.last 4) hd hR

def selected {n : ℕ} {R : ℕ → ℝ} (c : Profile n R) (j : Fin n) : ℕ := (c.2 j).val

theorem selected_dvd {n : ℕ} {R : ℕ → ℝ} (c : Profile n R) (j : Fin n) :
    selected c j ∣ cofactor c :=
  (dvd_prod_of_mem (fun j => (c.2 j).val) (mem_univ j)).trans (dvd_mul_left _ _)

theorem selected_lower {i k n N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hb : wuSourceBox k δ N i Δ V)
    (c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d))
    (hd : c.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (j : Fin n) :
    (selected c j).Prime ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ selected c j := by
  have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hm := (LiLiuPrereqBuchstab.mem_primesIcc
    (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1/2-δ)/c.1) _)).mp (c.2 j).property
  refine ⟨hm.1, le_trans ?_ hm.2.1⟩
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hg.1
    (by norm_num : (0 : ℝ) ≤ 1/10)
  simpa only [← Real.rpow_mul (Nat.cast_nonneg N), div_eq_mul_inv, one_mul] using hp

/-- Geometry of every retained profile, not merely inhabited output fibres. -/
structure Geometry {n : ℕ} {R : ℕ → ℝ} (N : ℕ) (η : ℝ) (b : ℕ → ℝ)
    (j : Fin n) (c : Profile n R) : Prop where
  positive : 0 < cofactor c
  le_N : cofactor c ≤ N
  power_lower : (N : ℝ) ^ η ≤ cofactor c
  power_upper : (cofactor c : ℝ) ≤ (N : ℝ) ^ (1-η)
  lower_two : 2 ≤ lower j c
  feasible : lower j c ≤ upper N b c
  physical : (cofactor c : ℝ) * upper N b c ≤ N
  selected_large : ∀ t, (selected c t).Prime ∧ selected c t ∣ cofactor c ∧
    (N : ℝ) ^ η ≤ selected c t

theorem source_profile_geometry {i k n N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hb : wuSourceBox k δ N i Δ V)
    (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1/2-δ)/d)))
    (j : Fin n) (b : ℕ → ℝ)
    {c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d)}
    (hc : c ∈ family N (convolutionWuWindows N Δ V) P j b) :
    Geometry N (wuLocalExponent k δ / 10) b j c := by
  obtain ⟨hd, _, hf⟩ := mem_family.mp hc
  have hR := (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.1
  have hd0 : 0 < c.1 := boxConvolutionSupport_pos
    (fun j q hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
  have hA := cofactor_pos c hd0 hR
  have hAr : (0 : ℝ) < cofactor c := by exact_mod_cast hA
  have hsel := selected_lower hN hδ hδhi hb c hd
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

theorem product_rough {n : ℕ} {g : Fin n → ℕ} {Y : ℝ}
    (hg : ∀ j, (g j).Prime ∧ Y ≤ (g j : ℝ)) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ ∏ j, g j) : Y ≤ (q : ℝ) := by
  have aux : ∀ s : Finset (Fin n), q ∣ ∏ j ∈ s, g j → Y ≤ (q : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [prod_empty]; intro h; exact (hq.not_dvd_one h).elim
    | @insert a s ha ih =>
      rw [prod_insert ha]
      intro h
      rcases hq.dvd_mul.mp h with h | h
      · have he : q = g a := ((Nat.dvd_prime (hg a).1).mp h).resolve_left hq.ne_one
        exact he ▸ (hg a).2
      · exact ih h
  exact aux univ hd

theorem source_profile_rough {i k n N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hb : wuSourceBox k δ N i Δ V)
    (hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ))
    (c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d))
    (hd : c.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    ∀ q, q.Prime → q ∣ cofactor c → (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ) := by
  intro q hq hqc
  rcases hq.dvd_mul.mp hqc with h | h
  · exact omega3_support_prime_lower _ hW hd hq h
  · exact product_rough (selected_lower hN hδ hδhi hb c hd) hq h

/-- One threshold precedes every box and every full prefix family, including empty ones. -/
theorem source_geometry (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      (∀ j q, q ∈ convolutionWuWindows N Δ V j →
        q.Prime ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ)) ∧
      ∀ (n : ℕ) (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1/2-δ)/d)))
        (j : Fin n) (b : ℕ → ℝ),
        ∀ c ∈ family N (convolutionWuWindows N Δ V) P j b,
          Geometry N (wuLocalExponent k δ / 10) b j c ∧
          ∀ q, q.Prime → q ∣ cofactor c → (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ) := by
  obtain ⟨T, hT, hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb
  have hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ) :=
    fun j q hq => ⟨(hw N hN i Δ V hb j q hq).1, (hw N hN i Δ V hb j q hq).2.2⟩
  refine ⟨hW, ?_⟩
  intro n P j b c hc
  exact ⟨source_profile_geometry (by omega) hδ hδhi hb P j b hc,
    source_profile_rough (by omega) hδ hδhi hb hW c (mem_family.mp hc).1⟩

/-- Literal interval sums, with the unchanged original sigma. -/
noncomputable def intervalMass {i n : ℕ} {R : ℕ → ℝ} (N : ℕ)
    (W : Fin i → Finset ℕ) (L : Finset (Profile n R)) (j : Fin n) (b : ℕ → ℝ) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * ((fibre (lower j c) (upper N b c)).card : ℝ)

noncomputable def outputMass {i n : ℕ} {R : ℕ → ℝ} (N : ℕ)
    (W : Fin i → Finset ℕ) (L : Finset (Profile n R)) (j : Fin n) (b : ℕ → ℝ) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
    (((fibre (lower j c) (upper N b c)).filter (fun q => (N-cofactor c*q).Prime)).card : ℝ)

/-- Concrete source boxes supply positivity and R>1 internally for all four exact identities. -/
theorem source_dictionary {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2) (hb : wuSourceBox k δ N i Δ V)
    (a2 a3 b : ℕ → ℝ) :
    let W := convolutionWuWindows N Δ V
    let R := fun d : ℕ => (N : ℝ) ^ (1/2-δ)/d
    HighUnit.boxedSigma20 N δ W a2 a3 b = intervalMass N W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
    HighUnit.boxedSigma21 N δ W a3 b = intervalMass N W (family21 N W R a3 b) (Fin.last 4) b ∧
    envelope20 N W R a2 a3 b = outputMass N W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
    envelope21 N W R a3 b = outputMass N W (family21 N W R a3 b) (Fin.last 4) b := by
  have hd : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 < d :=
    fun _ hd => boxConvolutionSupport_pos (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
  have hR : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      1 < (N : ℝ) ^ (1/2-δ)/d := fun _ hd => (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.1
  exact ⟨boxedSigma20_interval _ _ _ _ hd hR, boxedSigma21_interval _ _ _ hd hR,
    envelope20_interval _ _ _ _ _ hd hR, envelope21_interval _ _ _ _ hd hR⟩

end Wu2008DoubleSieve.HighUnitSieve
