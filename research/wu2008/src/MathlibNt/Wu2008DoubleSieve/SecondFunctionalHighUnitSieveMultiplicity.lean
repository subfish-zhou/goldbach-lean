import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveGeometry

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSieve
open Finset SecondFunctionalUnitPrimeFibre HighUnitPrimeOutput

/-- All natural free labels, together with d, determine the dependent profile. -/
theorem profile_ext {n : ℕ} {R : ℕ → ℝ} {c c' : Profile n R}
    (hd : c.1 = c'.1) (hg : selected c = selected c') : c = c' := by
  rcases c with ⟨d,g⟩
  rcases c' with ⟨d',g'⟩
  dsimp only at hd
  subst d'
  have he : g = g' := by
    funext j
    exact Subtype.ext (congr_fun hg j)
  subst g'
  rfl

/-- Exact original sigma mass is bounded through all window+n labels. -/
theorem weighted_fibre_le {i k n N e : ℕ} {η : ℝ} {R : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (S : Finset (Profile n R))
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ η ≤ (p : ℝ))
    (hprod : ∀ c ∈ S, cofactor c = e)
    (ht : ∀ c ∈ S, ∀ j, (selected c j).Prime ∧ selected c j ∣ e ∧
      (N : ℝ) ^ η ≤ (selected c j : ℝ)) :
    (∑ c ∈ S, (convolutionCoeff W c.1 : ℝ)) ≤ (max 1 (1/η)) ^ (k+n) := by
  let L := S.sigma fun c => (Fintype.piFinset W).filter fun t => ∏ j, t j = c.1
  let labels (a : Σ _ : Profile n R, Fin i → ℕ) : Fin (i+n) → ℕ :=
    Fin.append a.2 (selected a.1)
  have hinj : Set.InjOn labels L := by
    intro a ha a' ha' hh
    obtain ⟨_, _, hatp⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨_, _, hatp'⟩ := mem_sigma.mp ha' |>.imp_right mem_filter.mp
    have htt : a.2 = a'.2 := by
      funext j
      simpa only [labels, Fin.append_left] using congr_fun hh (Fin.castAdd n j)
    have hs : selected a.1 = selected a'.1 := by
      funext j
      simpa only [labels, Fin.append_right] using congr_fun hh (Fin.natAdd i j)
    have hd : a.1.1 = a'.1.1 :=
      hatp.symm.trans ((congrArg (fun t : Fin i → ℕ => ∏ j, t j) htt).trans hatp')
    exact Sigma.ext (profile_ext hd hs) (heq_of_eq htt)
  have hcard := omega3_prime_labels_card_le L labels hinj hN he heN hη (by
    intro a ha j
    obtain ⟨hc, htW, htd⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hw := hW j (a.2 j) (Fintype.mem_piFinset.mp htW j)
      have hd : a.1.1 ∣ e := by
        rw [← hprod _ hc]
        exact dvd_mul_right _ _
      simpa only [labels, Fin.append_left] using
        (show (a.2 j).Prime ∧ a.2 j ∣ e ∧ (N : ℝ) ^ η ≤ (a.2 j : ℝ) from
          ⟨hw.1, ((htd ▸ dvd_prod_of_mem a.2 (mem_univ j))).trans hd, hw.2⟩)
    · simpa only [labels, Fin.append_right] using ht _ hc j)
  have heq : (L.card : ℝ) = ∑ c ∈ S, (convolutionCoeff W c.1 : ℝ) := by
    simp only [L, card_sigma, Nat.cast_sum, convolutionCoeff]
  rw [heq] at hcard
  exact hcard.trans ((pow_le_pow_left₀ (by positivity) (le_max_right 1 (1/η)) _).trans
    (pow_le_pow_right₀ (le_max_left 1 (1/η)) (Nat.add_le_add_right hik n)))

/-- Common-T source geometry, roughness, and fixed-e original-sigma multiplicity. -/
theorem source_fibres (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      (∀ j q, q ∈ convolutionWuWindows N Δ V j →
        q.Prime ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ)) ∧
      ∀ (n : ℕ) (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1/2-δ)/d)))
        (j : Fin n) (b : ℕ → ℝ),
        (∀ c ∈ family N (convolutionWuWindows N Δ V) P j b,
          Geometry N (wuLocalExponent k δ / 10) b j c ∧
          ∀ q, q.Prime → q ∣ cofactor c → (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ)) ∧
        (∀ e, (∑ c ∈ (family N (convolutionWuWindows N Δ V) P j b).filter
          (fun c => cofactor c = e), (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)) ≤
          (max 1 (1/(wuLocalExponent k δ / 10))) ^ (k+n)) := by
  obtain ⟨T, hT, hw⟩ := source_geometry k hδ hδhi
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb
  obtain ⟨hW, hG⟩ := hw N hN i Δ V hb
  refine ⟨hW, ?_⟩
  intro n P j b
  refine ⟨hG n P j b, ?_⟩
  intro e
  by_cases hn : ((family N (convolutionWuWindows N Δ V) P j b).filter
      (fun c => cofactor c = e)).Nonempty
  · obtain ⟨c, hc⟩ := hn
    obtain ⟨hc, he⟩ := mem_filter.mp hc
    have hg := (hG n P j b c hc).1
    apply weighted_fibre_le _ _ hb.1 (by omega) (he ▸ hg.positive) (he ▸ hg.le_N)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
    · exact fun _ hc => (mem_filter.mp hc).2
    · intro c hc t
      obtain ⟨hc, he⟩ := mem_filter.mp hc
      have ht := (hG n P j b c hc).1.selected_large t
      exact ⟨ht.1, he ▸ ht.2.1, ht.2.2⟩
  · rw [not_nonempty_iff_eq_empty.mp hn, sum_empty]
    exact pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) _

/-- Positivity is extracted from the original support before any unweighting. -/
theorem coefficient_pos {i n N : ℕ} {R b : ℕ → ℝ}
    {W : Fin i → Finset ℕ} {P : ∀ d, Finset (Fin n → primeSlabPrimes (R d))}
    {j : Fin n} {c : Profile n R} (hc : c ∈ family N W P j b) :
    0 < convolutionCoeff W c.1 := mem_boxConvolutionSupport.mp (mem_family.mp hc).1

theorem card_fibre_le_weight {i n N e : ℕ} {R b : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (P : ∀ d, Finset (Fin n → primeSlabPrimes (R d))) (j : Fin n) :
    (((family N W P j b).filter (fun c => cofactor c = e)).card : ℝ) ≤
      ∑ c ∈ (family N W P j b).filter (fun c => cofactor c = e),
        (convolutionCoeff W c.1 : ℝ) := by
  calc
    _ = ∑ _c ∈ (family N W P j b).filter (fun c => cofactor c = e), (1 : ℝ) := by simp
    _ ≤ _ := sum_le_sum fun c hc => by exact_mod_cast coefficient_pos (mem_filter.mp hc).1

/-- A transparent package of proved geometry, roughness and fixed-cofactor sigma mass. -/
def FamilyFacts {i n : ℕ} {R : ℕ → ℝ} (k N : ℕ) (η : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset (Profile n R)) (j : Fin n) (b : ℕ → ℝ) : Prop :=
  (∀ c ∈ L, Geometry N η b j c ∧ ∀ q, q.Prime → q ∣ cofactor c → (N : ℝ)^η ≤ (q : ℝ)) ∧
  (∀ e, (∑ c ∈ L.filter (fun c => cofactor c = e), (convolutionCoeff W c.1 : ℝ)) ≤
    (max 1 (1/η)) ^ (k+n))

/-- Actual mother word20 and word21 endpoints; no geometry or coprimality gate is supplied. -/
theorem source_mother_pair (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let R := fun d : ℕ => (N : ℝ) ^ (1/2-δ)/d
      let a2 := fun _ : ℕ => 1/p.kappa2
      let a3 := fun _ : ℕ => 1/p.kappa3
      let b := fun _ : ℕ => 1/p.s
      (∀ j q, q ∈ W j → q.Prime ∧ (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ (q : ℝ)) ∧
      FamilyFacts k N (wuLocalExponent k δ / 10) W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
      FamilyFacts k N (wuLocalExponent k δ / 10) W (family21 N W R a3 b) (Fin.last 4) b ∧
      HighUnit.boxedSigma20 N δ W a2 a3 b = intervalMass N W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
      HighUnit.boxedSigma21 N δ W a3 b = intervalMass N W (family21 N W R a3 b) (Fin.last 4) b ∧
      envelope20 N W R a2 a3 b = outputMass N W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
      envelope21 N W R a3 b = outputMass N W (family21 N W R a3 b) (Fin.last 4) b := by
  obtain ⟨T, hT, hw⟩ := source_fibres k hδ hδhi
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb p _ _
  obtain ⟨hW, hF⟩ := hw N hN i Δ V hb
  refine ⟨hW, hF 4 _ (Fin.last 3) _, hF 5 _ (Fin.last 4) _, ?_⟩
  exact source_dictionary (by omega) hδ hδhi hb _ _ _

/-- Input primes inherit size and the nontruncated physical product bound. -/
theorem input_geometry {n N : ℕ} {η : ℝ} {R b : ℕ → ℝ} {j : Fin n} {c : Profile n R}
    (hg : Geometry N η b j c) {q : ℕ} (hq : q ∈ fibre (lower j c) (upper N b c)) :
    q.Prime ∧ (N : ℝ)^η ≤ (q : ℝ) ∧ 0 < cofactor c*q ∧ cofactor c*q ≤ N := by
  have hu : 0 ≤ upper N b c := by linarith [hg.lower_two, hg.feasible]
  obtain ⟨hp, hl, hhi⟩ := (mem_fibre hu).mp hq
  have hlow : (N : ℝ)^η ≤ lower j c := (hg.selected_large j).2.2
  refine ⟨hp, hlow.trans hl.le, Nat.mul_pos hg.positive hp.pos, ?_⟩
  have h : (cofactor c : ℝ) * q ≤ N :=
    (mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg _)).trans hg.physical
  exact_mod_cast h

/-- Small prime outputs retain the original closed interval and every label. -/
noncomputable def smallInputs {n : ℕ} {R : ℕ → ℝ} (N Z : ℕ)
    (j : Fin n) (b : ℕ → ℝ) (c : Profile n R) : Finset ℕ :=
  (fibre (lower j c) (upper N b c)).filter fun q =>
    (N-cofactor c*q).Prime ∧ N-cofactor c*q ≤ Z

noncomputable def smallOutputMass {i n : ℕ} {R : ℕ → ℝ} (N Z : ℕ)
    (W : Fin i → Finset ℕ) (S : Finset (Profile n R)) (j : Fin n) (b : ℕ → ℝ) : ℝ :=
  ∑ c ∈ S, (convolutionCoeff W c.1 : ℝ) * ((smallInputs N Z j b c).card : ℝ)

/-- All window+n+1 labels count small outputs, rather than profiles times Z. -/
theorem small_output_le {i k n N Z : ℕ} {η : ℝ} {R b : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (S : Finset (Profile n R)) (j : Fin n)
    (hik : i ≤ k) (hN : 1 < N) (hη : 0 < η) (hZ : Z < N)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ (p : ℝ))
    (hG : ∀ c ∈ S, Geometry N η b j c) :
    smallOutputMass N Z W S j b ≤ (max 1 (1/η)) ^ (k+n+1) * Z := by
  let L := S.sigma fun c =>
    ((Fintype.piFinset W).filter fun t => ∏ j, t j = c.1) ×ˢ smallInputs N Z j b c
  let labels (a : Σ _ : Profile n R, (Fin i → ℕ) × ℕ) : Fin (i+n+1) → ℕ :=
    Fin.append (Fin.append a.2.1 (selected a.1)) (fun _ : Fin 1 => a.2.2)
  let out (a : Σ _ : Profile n R, (Fin i → ℕ) × ℕ) : ℕ := cofactor a.1 * a.2.2
  let E := (Icc 1 Z).image (fun ell => N-ell)
  have hinj : Set.InjOn (fun a => (out a, labels a)) L := by
    intro a ha a' ha' hh
    have hh := congrArg Prod.snd hh
    obtain ⟨_, hat, _⟩ := mem_sigma.mp ha |>.imp_right mem_product.mp
    obtain ⟨_, hat', _⟩ := mem_sigma.mp ha' |>.imp_right mem_product.mp
    have htt : a.2.1 = a'.2.1 := by
      funext t
      simpa only [labels, Fin.append_left] using congr_fun hh (Fin.castAdd 1 (Fin.castAdd n t))
    have hs : selected a.1 = selected a'.1 := by
      funext t
      simpa only [labels, Fin.append_left, Fin.append_right] using
        congr_fun hh (Fin.castAdd 1 (Fin.natAdd i t))
    have hq : a.2.2 = a'.2.2 := by
      simpa only [labels, Fin.append_right] using congr_fun hh (Fin.natAdd (i+n) 0)
    have hd : a.1.1 = a'.1.1 := (mem_filter.mp hat).2.symm.trans
      ((congrArg (fun t : Fin i → ℕ => ∏ j, t j) htt).trans (mem_filter.mp hat').2)
    exact Sigma.ext (profile_ext hd hs) (heq_of_eq (Prod.ext htt hq))
  have hinput (a : Σ _ : Profile n R, (Fin i → ℕ) × ℕ) (ha : a ∈ L) :
      a.2.2 ∈ smallInputs N Z j b a.1 ∧
      a.2.2.Prime ∧ (N : ℝ)^η ≤ (a.2.2 : ℝ) ∧ 0 < out a ∧ out a ≤ N := by
    obtain ⟨hc, _, hq⟩ := mem_sigma.mp ha |>.imp_right mem_product.mp
    exact ⟨hq, input_geometry (hG a.1 hc) (mem_filter.mp hq).1⟩
  have hcard := omega3_labels_card_le_outputs L out labels E hinj (by
    intro a ha
    obtain ⟨hq, _, _, _, hmN⟩ := hinput a ha
    have hs := (mem_filter.mp hq).2
    apply mem_image.mpr
    refine ⟨N-out a, mem_Icc.mpr ⟨hs.1.pos, hs.2⟩, ?_⟩
    exact Nat.sub_sub_self hmN) hN hη (by
      intro a ha
      have hmN := (hinput a ha).2.2.2.2
      have hsmall := (mem_filter.mp (hinput a ha).1).2.2
      have hpos : 0 < N - (N-out a) := Nat.sub_pos_of_lt (lt_of_le_of_lt hsmall hZ)
      rw [Nat.sub_sub_self hmN] at hpos
      exact ⟨hpos, hmN⟩) (by
    intro a ha t
    obtain ⟨hc, htW, _⟩ := mem_sigma.mp ha |>.imp_right mem_product.mp
    obtain ⟨htW, htd⟩ := mem_filter.mp htW
    have hAo : cofactor a.1 ∣ out a := dvd_mul_right _ _
    refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
      · have hw := hW t (a.2.1 t) (Fintype.mem_piFinset.mp htW t)
        have hd : a.1.1 ∣ cofactor a.1 := dvd_mul_right _ _
        simpa only [labels, Fin.append_left] using
          (show (a.2.1 t).Prime ∧ a.2.1 t ∣ out a ∧ (N : ℝ)^η ≤ (a.2.1 t : ℝ) from
            ⟨hw.1, ((htd ▸ dvd_prod_of_mem a.2.1 (mem_univ t)).trans hd).trans hAo, hw.2⟩)
      · have hs := (hG a.1 hc).selected_large t
        simpa only [labels, Fin.append_left, Fin.append_right] using
          (show (selected a.1 t).Prime ∧ selected a.1 t ∣ out a ∧ (N : ℝ)^η ≤ selected a.1 t from
            ⟨hs.1, hs.2.1.trans hAo, hs.2.2⟩)
    · have hi := hinput a ha
      simpa only [labels, Fin.append_right] using
        (show a.2.2.Prime ∧ a.2.2 ∣ out a ∧ (N : ℝ)^η ≤ (a.2.2 : ℝ) from
          ⟨hi.2.1, dvd_mul_left _ _, hi.2.2.1⟩))
  have heq : (L.card : ℝ) = smallOutputMass N Z W S j b := by
    simp only [L, card_sigma, card_product, Nat.cast_sum, Nat.cast_mul,
      smallOutputMass, convolutionCoeff]
  rw [heq] at hcard
  have hE : (E.card : ℝ) ≤ (Z : ℝ) := by
    exact_mod_cast (card_image_le.trans_eq (show (Icc 1 Z).card = Z by simp))
  have hpow : (1/η) ^ (i+n+1) ≤ (max 1 (1/η)) ^ (k+n+1) :=
    (pow_le_pow_left₀ (by positivity) (le_max_right 1 (1/η)) _).trans
      (pow_le_pow_right₀ (le_max_left 1 (1/η)) (by omega))
  exact hcard.trans (mul_le_mul hpow hE (Nat.cast_nonneg _) (by positivity))

/-- Exact small-output disintegration of the old physical sums. -/
theorem small_output_dictionary {i n N Z : ℕ} {R b : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (P : ∀ d, Finset (Fin n → primeSlabPrimes (R d)))
    (j : Fin n) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * ∑ g ∈ P d,
      (((physical (prefixProduct g) ((N : ℝ)/d) (g j).val (R d ^ b d)).filter
        (fun q => (N-d*freeProduct g*q).Prime ∧ N-d*freeProduct g*q ≤ Z)).card : ℝ)) =
      smallOutputMass N Z W (family N W P j b) j b := by
  have h := sum_interval (N := N) (b := b) W P j (fun c q =>
    if (N-cofactor c*q).Prime ∧ N-cofactor c*q ≤ Z then (convolutionCoeff W c.1 : ℝ) else 0) hd hR
  simpa only [smallOutputMass, smallInputs, cofactor, ← sum_filter,
    sum_const, nsmul_eq_mul, mul_comm, mul_sum, sum_mul] using h

/-- Real thresholds preserve the exact prime-output predicate, including the closed boundary. -/
noncomputable def smallOutputMassReal {i n : ℕ} {R : ℕ → ℝ} (N : ℕ) (Z : ℝ)
    (W : Fin i → Finset ℕ) (S : Finset (Profile n R)) (j : Fin n) (b : ℕ → ℝ) : ℝ :=
  ∑ c ∈ S, (convolutionCoeff W c.1 : ℝ) *
    (((fibre (lower j c) (upper N b c)).filter
      (fun q => (N-cofactor c*q).Prime ∧ (N-cofactor c*q : ℕ) ≤ Z)).card : ℝ)

theorem small_real_eq_floor {i n N : ℕ} {R : ℕ → ℝ} {Z : ℝ} (hZ : 0 ≤ Z)
    (W : Fin i → Finset ℕ) (S : Finset (Profile n R)) (j : Fin n) (b : ℕ → ℝ) :
    smallOutputMassReal N Z W S j b = smallOutputMass N ⌊Z⌋₊ W S j b := by
  simp only [smallOutputMassReal, smallOutputMass, smallInputs, Nat.le_floor_iff hZ]

theorem small_output_real_le {i k n N : ℕ} {η Z : ℝ} {R b : ℕ → ℝ}
    (W : Fin i → Finset ℕ) (S : Finset (Profile n R)) (j : Fin n)
    (hik : i ≤ k) (hN : 1 < N) (hη : 0 < η) (hZ0 : 0 ≤ Z) (hZ : Z < N)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ (p : ℝ))
    (hG : ∀ c ∈ S, Geometry N η b j c) :
    smallOutputMassReal N Z W S j b ≤ (max 1 (1/η)) ^ (k+n+1) * Z := by
  rw [small_real_eq_floor hZ0]
  have hf : ⌊Z⌋₊ < N := by exact_mod_cast (Nat.floor_le hZ0).trans_lt hZ
  exact (small_output_le W S j hik hN hη hf hW hG).trans
    (mul_le_mul_of_nonneg_left (Nat.floor_le hZ0) (by positivity))

/-- A single threshold supplies both words' geometry, roughness, multiplicities and small outputs. -/
theorem source_mother_small_pair (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let R := fun d : ℕ => (N : ℝ) ^ (1/2-δ)/d
      let a2 := fun _ : ℕ => 1/p.kappa2
      let a3 := fun _ : ℕ => 1/p.kappa3
      let b := fun _ : ℕ => 1/p.s
      let η := wuLocalExponent k δ / 10
      (∀ j q, q ∈ W j → q.Prime ∧ (N : ℝ)^η ≤ (q : ℝ)) ∧
      FamilyFacts k N η W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
      FamilyFacts k N η W (family21 N W R a3 b) (Fin.last 4) b ∧
      (∀ Z : ℝ, 0 ≤ Z → Z < N →
        smallOutputMassReal N Z W (family20 N W R a2 a3 b) (Fin.last 3) b ≤
          (max 1 (1/η)) ^ (k+4+1) * Z ∧
        smallOutputMassReal N Z W (family21 N W R a3 b) (Fin.last 4) b ≤
          (max 1 (1/η)) ^ (k+5+1) * Z) ∧
      HighUnit.boxedSigma20 N δ W a2 a3 b = intervalMass N W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
      HighUnit.boxedSigma21 N δ W a3 b = intervalMass N W (family21 N W R a3 b) (Fin.last 4) b ∧
      envelope20 N W R a2 a3 b = outputMass N W (family20 N W R a2 a3 b) (Fin.last 3) b ∧
      envelope21 N W R a3 b = outputMass N W (family21 N W R a3 b) (Fin.last 4) b := by
  obtain ⟨T, hT, hw⟩ := source_fibres k hδ hδhi
  refine ⟨T, hT, ?_⟩
  intro N hN i Δ V hb p _ _
  obtain ⟨hW, hF⟩ := hw N hN i Δ V hb
  have h20 := hF 4 (fun d => HighUnit.primePrefix20 _ (1/p.kappa2) (1/p.kappa3) (1/p.s))
    (Fin.last 3) (fun _ => 1/p.s)
  have h21 := hF 5 (fun d => HighUnit.primePrefix21 _ (1/p.kappa3) (1/p.s))
    (Fin.last 4) (fun _ => 1/p.s)
  refine ⟨hW, h20, h21, ?_, source_dictionary (by omega) hδ hδhi hb _ _ _⟩
  intro Z hZ0 hZ
  have hη := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num : (0 : ℝ) < 10)
  exact ⟨small_output_real_le _ _ _ hb.1 (by omega) hη hZ0 hZ hW (fun c hc => (h20.1 c hc).1),
    small_output_real_le _ _ _ hb.1 (by omega) hη hZ0 hZ hW (fun c hc => (h21.1 c hc).1)⟩

end Wu2008DoubleSieve.HighUnitSieve
