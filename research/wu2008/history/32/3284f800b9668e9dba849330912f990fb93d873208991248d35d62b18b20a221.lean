import MathlibNt.Wu2008DoubleSieve.Gamma16MassCarrier

/-! # Multiplicity-preserving reindexing into the positive four-prime mass envelope -/

namespace Wu2008DoubleSieve

open Finset Real LiLiuPrereqBuchstab
open scoped Classical

theorem gamma16_cutoffs (N d : ℕ) (δ : ℝ) :
    wuLocalCutoff N δ d (291 / 100) = ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma16Alpha ∧
    wuLocalCutoff N δ d (5 / 2) = ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma16Beta := by
  norm_num [wuLocalCutoff, gamma16Alpha, gamma16Beta]

def gamma16MassReindex (a : Σ _ : Gamma16Profile, ℕ) :
    Σ _ : ℕ, Σ _ : Gamma16MassTuple, ℕ :=
  ⟨a.1.1, ⟨a.2, a.1.2.2.2.1, a.1.2.2.1, a.1.2.1⟩, a.1.2.2.2.2⟩

theorem gamma16_mass_reindex_injective : Function.Injective gamma16MassReindex := by
  rintro ⟨⟨d, p3, p2, p1, n⟩, p4⟩ ⟨⟨d', p3', p2', p1', n'⟩, p4'⟩ he
  have hd : d = d' := congrArg Sigma.fst he
  have h4 : p4 = p4' := congrArg (fun a : Σ _ : ℕ, Σ _ : Gamma16MassTuple, ℕ => a.2.1.1) he
  have h1 : p1 = p1' := congrArg (fun a : Σ _ : ℕ, Σ _ : Gamma16MassTuple, ℕ => a.2.1.2.1) he
  have h2 : p2 = p2' := congrArg (fun a : Σ _ : ℕ, Σ _ : Gamma16MassTuple, ℕ => a.2.1.2.2.1) he
  have h3 : p3 = p3' := congrArg (fun a : Σ _ : ℕ, Σ _ : Gamma16MassTuple, ℕ => a.2.1.2.2.2) he
  have hn : n = n' := congrArg (fun a : Σ _ : ℕ, Σ _ : Gamma16MassTuple, ℕ => a.2.2) he
  subst d'; subst p4'; subst p1'; subst p2'; subst p3'; subst n'
  rfl

theorem gamma16_mass_reindex_mem {i N : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ}
    {a : Σ _ : Gamma16Profile, ℕ}
    (ha : a ∈ (gamma16Profiles N δ W).sigma (gamma16PrimeFibre N δ)) :
    gamma16MassReindex a ∈ (boxConvolutionSupport W).sigma
      (fun d => (gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)).sigma (gamma16MassNFibre N d)) := by
  rcases a with ⟨⟨d, p3, p2, p1, n⟩, p4⟩
  obtain ⟨hc, hp4⟩ := mem_sigma.mp ha
  obtain ⟨hd, h3, h2, h1, hnN, hn, _, hg⟩ := mem_gamma16Profiles.mp hc
  obtain ⟨_, hp4, h34, h4hi, hsize⟩ := mem_filter.mp hp4
  have h1' := mem_primeWindow.mp h1
  have h2' := mem_primeWindow.mp h2
  have h3' := mem_primeWindow.mp h3
  have h12 : (p1 : ℝ) < p2 := h1'.2.2.2
  have h23 : (p2 : ℝ) < p3 := h2'.2.2.2
  have h34r : (p3 : ℝ) < p4 := by exact_mod_cast h34
  have hcut := gamma16_cutoffs N d δ
  rw [hcut.1] at h1'
  change (p4 : ℝ) ≤ wuLocalCutoff N δ d (5 / 2) at h4hi
  rw [hcut.2] at h4hi
  apply mem_sigma.mpr
  refine ⟨hd, mem_sigma.mpr ⟨?_, ?_⟩⟩
  · apply mem_sigma.mpr
    refine ⟨(mem_primesIcc (by positivity)).mpr
      ⟨hp4, h1'.2.2.1.trans (h12.trans (h23.trans h34r)).le, h4hi⟩, ?_⟩
    apply mem_sigma.mpr
    refine ⟨(mem_primesIcc (Nat.cast_nonneg p4)).mpr
      ⟨h1'.1, h1'.2.2.1, (h12.trans (h23.trans h34r)).le⟩, ?_⟩
    apply mem_sigma.mpr
    exact ⟨(mem_primesIoc (Nat.cast_nonneg p4)).mpr ⟨h2'.1, h12, (h23.trans h34r).le⟩,
      (mem_primesIoc (Nat.cast_nonneg p4)).mpr ⟨h3'.1, h23, h34r.le⟩⟩
  · apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le hnN), hn, ?_, hg.2.2⟩
    simpa only [gamma16MassReindex, gamma16MassProduct, gamma16_encode_value, gamma16Cofactor,
      mul_assoc, mul_left_comm, mul_comm] using hsize

noncomputable def gamma16MassCount {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d), ((gamma16MassNFibre N d p).card : ℝ)

theorem gamma16_X_le_mass_count {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    gamma16X N δ W ≤ gamma16MassCount N δ W := by
  let S := (gamma16Profiles N δ W).sigma (gamma16PrimeFibre N δ)
  let T := (boxConvolutionSupport W).sigma
    (fun d => (gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d)).sigma (gamma16MassNFibre N d))
  have hs : gamma16X N δ W = ∑ a ∈ S, (convolutionCoeff W a.1.1 : ℝ) := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, gamma16X, mul_comm]
  have ht : gamma16MassCount N δ W = ∑ a ∈ T, (convolutionCoeff W a.1 : ℝ) := by
    simp only [T, sum_sigma, sum_const, nsmul_eq_mul, gamma16MassCount,
      card_sigma, Nat.cast_sum, mul_sum, mul_comm]
  rw [hs, ht]
  have hi : (∑ a ∈ S, (convolutionCoeff W a.1.1 : ℝ)) =
      ∑ a ∈ S.image gamma16MassReindex, (convolutionCoeff W a.1 : ℝ) := by
    rw [sum_image gamma16_mass_reindex_injective.injOn]
    rfl
  rw [hi]
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    exact gamma16_mass_reindex_mem hb
  · exact fun _ _ _ => Nat.cast_nonneg _

noncomputable def gamma16RoughMajorant {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d),
      (roughCount (gamma16MassScale N d p) p.2.2.2 : ℝ)

noncomputable def gamma16RepeatedMajorant {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ gamma16MassPrimes ((N : ℝ) ^ (1 / 2 - δ) / d),
      ((⌊gamma16MassScale N d p / p.2.1⌋₊ : ℝ) + ⌊gamma16MassScale N d p / p.2.2.1⌋₊)

theorem gamma16_X_le_rough_repeated {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    gamma16X N δ W ≤ gamma16RoughMajorant N δ W + gamma16RepeatedMajorant N δ W := by
  apply (gamma16_X_le_mass_count N δ W).trans
  unfold gamma16MassCount gamma16RoughMajorant gamma16RepeatedMajorant
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro d hdW
  rw [← mul_add, ← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro p hp
  have h := gamma16_mass_fibre_rough (N := N) (hd d hdW) (by positivity) hp
  exact_mod_cast (by simpa only [Nat.add_assoc] using h)

end Wu2008DoubleSieve
