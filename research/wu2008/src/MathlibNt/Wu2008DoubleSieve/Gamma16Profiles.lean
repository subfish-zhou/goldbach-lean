import MathlibNt.Wu2008DoubleSieve.Gamma16Carriers
import MathlibNt.Wu2008DoubleSieve.Omega3LabelsCofactor
import MathlibNt.Wu2008DoubleSieve.Omega3ClosedEnlargement
import MathlibNt.Wu2008DoubleSieve.NinthProductProfile

/-!
# Actual fourth-row profiles and their lossless finite-family encoding

The profile contains three selected primes and a positive quotient.
The last prime is a separate fibre. Encoding the ordered first pair by
its product preserves labels, rather than replacing them by their e-image.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

abbrev Gamma16Profile := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

def gamma16Cofactor (c : Gamma16Profile) : ℕ :=
  c.1 * c.2.2.2.2 * c.2.2.2.1 * c.2.2.1 * c.2.1

def Gamma16Strengthened (N d p1 p2 p3 n : ℕ) : Prop :=
  (p1 * p2 * p3).Coprime (d * N) ∧ n.Coprime (d * N) ∧
    ∀ q : ℕ, q.Prime → (q : ℝ) < p3 → q ≠ p1 → q ≠ p2 → ¬q ∣ n

noncomputable def gamma16Profiles {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : Finset Gamma16Profile :=
  (boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (wuLocalCutoff N δ d (291 / 100))
      (wuLocalCutoff N δ d (5 / 2))).sigma fun p3 =>
    (primeWindow N (wuLocalCutoff N δ d (291 / 100)) p3).sigma fun p2 =>
    (primeWindow N (wuLocalCutoff N δ d (291 / 100)) p2).sigma fun p1 =>
    (range (N + 1)).filter fun n => 0 < n ∧
      gamma16Cofactor ⟨d, p3, p2, p1, n⟩ * p3 ≤ N ∧
      Gamma16Strengthened N d p1 p2 p3 n

theorem mem_gamma16Profiles {i N d p1 p2 p3 n : ℕ} {δ : ℝ}
    {W : Fin i → Finset ℕ} :
    (⟨d, p3, p2, p1, n⟩ : Gamma16Profile) ∈ gamma16Profiles N δ W ↔
      d ∈ boxConvolutionSupport W ∧
      p3 ∈ primeWindow N (wuLocalCutoff N δ d (291 / 100))
        (wuLocalCutoff N δ d (5 / 2)) ∧
      p2 ∈ primeWindow N (wuLocalCutoff N δ d (291 / 100)) p3 ∧
      p1 ∈ primeWindow N (wuLocalCutoff N δ d (291 / 100)) p2 ∧
      n ≤ N ∧ 0 < n ∧ gamma16Cofactor ⟨d, p3, p2, p1, n⟩ * p3 ≤ N ∧
      Gamma16Strengthened N d p1 p2 p3 n := by
  simp only [gamma16Profiles, mem_sigma, mem_filter, mem_range, Nat.lt_succ_iff]

def gamma16Encode (c : Gamma16Profile) : Omega3CofactorIndex :=
  ⟨c.1, c.2.1, c.2.2.2.1 * c.2.2.1, c.2.2.2.2⟩

theorem gamma16_encode_value (c : Gamma16Profile) :
    omega3CofactorValue (gamma16Encode c) = gamma16Cofactor c := by
  simp only [gamma16Encode, omega3CofactorValue, omega3Cofactor, gamma16Cofactor, mul_assoc]

theorem gamma16_encode_injective {i N : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ} :
    Set.InjOn gamma16Encode (gamma16Profiles N δ W) := by
  rintro ⟨d, p3, p2, p1, n⟩ hc ⟨d', p3', p2', p1', n'⟩ hc' he
  obtain ⟨_, _, h2, h1, _⟩ := mem_gamma16Profiles.mp hc
  obtain ⟨_, _, h2', h1', _⟩ := mem_gamma16Profiles.mp hc'
  have hd : d = d' := congrArg (fun c : Omega3CofactorIndex => c.1) he
  have h3 : p3 = p3' := congrArg (fun c : Omega3CofactorIndex => c.2.1) he
  have hn : n = n' := congrArg (fun c : Omega3CofactorIndex => c.2.2.2) he
  have hprod : p1 * p2 = p1' * p2' :=
    congrArg (fun c : Omega3CofactorIndex => c.2.2.1) he
  have hp := ninth_ordered_prime_product_injective
    (mem_primeWindow.mp h1).1 (mem_primeWindow.mp h2).1
    (mem_primeWindow.mp h1').1 (mem_primeWindow.mp h2').1
    (by exact_mod_cast (mem_primeWindow.mp h1).2.2.2)
    (by exact_mod_cast (mem_primeWindow.mp h1').2.2.2) hprod
  have h1e := congrArg Prod.fst hp
  have h2e := congrArg Prod.snd hp
  change p1 = p1' at h1e
  change p2 = p2' at h2e
  subst d'; subst p3'; subst n'; subst p1'; subst p2'
  rfl

noncomputable def gamma16EncodedProfiles {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : Finset Omega3CofactorIndex :=
  (gamma16Profiles N δ W).image gamma16Encode

theorem gamma16_encoded_sum {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (f : Omega3CofactorIndex → ℝ) :
    (∑ c ∈ gamma16EncodedProfiles N δ W, (convolutionCoeff W c.1 : ℝ) * f c) =
      ∑ c ∈ gamma16Profiles N δ W, (convolutionCoeff W c.1 : ℝ) * f (gamma16Encode c) := by
  exact sum_image (fun _ h _ h' he => gamma16_encode_injective h h' he)

noncomputable def gamma16StrictFibre (N : ℕ) (δ : ℝ)
    (c : Gamma16Profile) : Finset ℕ :=
  (primeWindow N c.2.1 (wuLocalCutoff N δ c.1 (5 / 2))).filter fun p =>
    c.2.1 < p ∧ gamma16Cofactor c * p ≤ N

noncomputable def gamma16PrimeFibre (N : ℕ) (δ : ℝ)
    (c : Gamma16Profile) : Finset ℕ :=
  omega3CofactorPrimeFibreLE N δ (5 / 2) (gamma16Encode c)

theorem gamma16_strict_fibre_subset {N : ℕ} {δ : ℝ} {c : Gamma16Profile}
    (hc : 0 < gamma16Cofactor c) :
    gamma16StrictFibre N δ c ⊆ gamma16PrimeFibre N δ c := by
  intro p hp
  obtain ⟨hp, hlo, hsize⟩ := mem_filter.mp hp
  obtain ⟨hprime, _, _, hhi⟩ := mem_primeWindow.mp hp
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (Nat.lt_succ_of_le
    ((Nat.le_mul_of_pos_left p hc).trans hsize)), hprime, hlo, hhi.le, ?_⟩
  simpa only [gamma16_encode_value] using hsize

noncomputable def gamma16X {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ c ∈ gamma16Profiles N δ W,
    (convolutionCoeff W c.1 : ℝ) * (gamma16PrimeFibre N δ c).card

noncomputable def gamma16S {i : ℕ} (N : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ c ∈ gamma16Profiles N δ W, (convolutionCoeff W c.1 : ℝ) *
    (((gamma16PrimeFibre N δ c).filter
      (fun p => Sifted N (N - gamma16Cofactor c * p) Z)).card : ℝ)

theorem gamma16_cofactor_coprime {i N : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ}
    (hW : ∀ d ∈ boxConvolutionSupport W, d.Coprime N)
    {c : Gamma16Profile} (hc : c ∈ gamma16Profiles N δ W) :
    (gamma16Cofactor c).Coprime N := by
  rcases c with ⟨d, p3, p2, p1, n⟩
  obtain ⟨hd, _, _, _, _, _, _, hg⟩ := mem_gamma16Profiles.mp hc
  have hp := (Nat.coprime_mul_iff_right.mp hg.1).2
  have hn := (Nat.coprime_mul_iff_right.mp hg.2.1).2
  simpa only [gamma16Cofactor, mul_assoc] using (hW d hd).mul_left (hn.mul_left hp)

end Wu2008DoubleSieve
