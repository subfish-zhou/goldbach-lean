import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEta
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosCharacter
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerIndex
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.Finite.Extension

/-!
# Minimal-polynomial linkage in Harcos's Theorem 6

Harcos, §3, pages 7–8 (`pages/harcos-lpolynomial-07.png` and
`pages/harcos-stepanov-08.png`), identifies the character on each orbit
with a power of the polynomial character. The extension multiplicity is
a natural-number quotient, not division in the base field.
-/

noncomputable section

open Polynomial IntermediateField Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

section General

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

omit [FiniteDimensional K L] in
private theorem adjoin_inv_eq (t : L) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  apply le_antisymm
  · exact adjoin_simple_le_iff.mpr ((K⟮t⟯).inv_mem (mem_adjoin_simple_self K t))
  · apply adjoin_simple_le_iff.mpr
    simpa only [inv_inv] using
      (K⟮t⁻¹⟯).inv_mem (mem_adjoin_simple_self K t⁻¹)

theorem harcos_minpoly_inv_natDegree (t : L) :
    (minpoly K t⁻¹).natDegree = (minpoly K t).natDegree := by
  rw [← adjoin.finrank (IsIntegral.of_finite K t⁻¹),
    ← adjoin.finrank (IsIntegral.of_finite K t), adjoin_inv_eq]

/-- The inverse minimal polynomial is the normalized coefficient reversal. -/
theorem harcos_minpoly_inv (t : L) (ht : t ≠ 0) :
    minpoly K t⁻¹ = (minpoly K t).reverse * C ((minpoly K t).coeff 0)⁻¹ := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K t) ht
  have hl : (minpoly K t).reverse.leadingCoeff = (minpoly K t).coeff 0 := by
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hc]
  apply Eq.symm
  apply eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite K t⁻¹))
  · rw [← hl]
    exact monic_mul_leadingCoeff_inv
      (reverse_eq_zero.not.mpr (minpoly.ne_zero (IsIntegral.of_finite K t)))
  · apply minpoly.dvd
    rw [map_mul]
    have hr : aeval t⁻¹ (minpoly K t).reverse = 0 := by
      let : Invertible t := invertibleOfNonzero ht
      simpa only [invOf_eq_inv, ← aeval_def] using
        (eval₂_reverse_eq_zero_iff (algebraMap K L) t (minpoly K t)).mpr
          (minpoly.aeval K t)
    rw [hr, zero_mul]
  · rw [natDegree_mul_C (inv_ne_zero hc), harcos_minpoly_inv_natDegree]
    exact reverse_natDegree_le _

theorem harcos_minpoly_inv_nextCoeff (t : L) (ht : t ≠ 0) :
    (minpoly K t⁻¹).nextCoeff = (minpoly K t).coeff 1 / (minpoly K t).coeff 0 := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K t) ht
  have hd : (minpoly K t).reverse.natDegree = (minpoly K t).natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hc), Nat.sub_zero]
  have hp := minpoly.natDegree_pos (IsIntegral.of_finite K t)
  rw [harcos_minpoly_inv K t ht, nextCoeff_mul_C,
    nextCoeff_of_natDegree_pos (hd.symm ▸ hp), hd, coeff_reverse,
    revAt_le (Nat.sub_le _ _)]
  have hi : (minpoly K t).natDegree - ((minpoly K t).natDegree - 1) = 1 := by omega
  rw [hi, div_eq_mul_inv]

/-- The tower index is an integer quotient before casting to the base field. -/
theorem harcos_minpoly_extension_index (t : L) :
    Module.finrank K⟮t⟯ L = Module.finrank K L / (minpoly K t).natDegree := by
  rw [← Module.finrank_mul_finrank K K⟮t⟯ L,
    adjoin.finrank (IsIntegral.of_finite K t),
    Nat.mul_div_right _ (minpoly.natDegree_pos (IsIntegral.of_finite K t))]

theorem harcos_trace_inv_minpoly (t : L) (ht : t ≠ 0) :
    Algebra.trace K L t⁻¹ =
      ((Module.finrank K L / (minpoly K t).natDegree : ℕ) : K) *
        (-(minpoly K t).coeff 1 / (minpoly K t).coeff 0) := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff,
    harcos_minpoly_extension_index, harcos_minpoly_inv_natDegree,
    harcos_minpoly_inv_nextCoeff K t ht, neg_div]

/-- The actual trace of the Kloosterman phase, including inseparable tower indices
and indices divisible by the characteristic. -/
theorem harcos_trace_minpoly_phase (a b : K) (t : L) (ht : t ≠ 0) :
    Algebra.trace K L (algebraMap K L a * t + algebraMap K L b / t) =
      ((Module.finrank K L / (minpoly K t).natDegree : ℕ) : K) *
        (-a * (minpoly K t).nextCoeff -
          b * (minpoly K t).coeff 1 / (minpoly K t).coeff 0) := by
  rw [div_eq_mul_inv, ← Algebra.smul_def, ← Algebra.smul_def, map_add,
    map_smul, map_smul, trace_eq_finrank_mul_minpoly_nextCoeff,
    harcos_minpoly_extension_index, harcos_trace_inv_minpoly K t ht,
    smul_eq_mul, smul_eq_mul]
  ring

end General

section PrimeField

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [Algebra (ZMod p) F]

/-- The character value is constant on the minimal-polynomial fiber.
The exponent is a natural number even when the characteristic divides the index. -/
theorem harcos_minpoly_eta_power (a b : ZMod p) (m : ℕ) (t : F) (ht : t ≠ 0) :
    ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
      (algebraMap (ZMod p) F a * t + algebraMap (ZMod p) F b / t)) =
      harcosEta a b (minpoly (ZMod p) t) ^
        (m * (Module.finrank (ZMod p) F / (minpoly (ZMod p) t).natDegree)) := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite (ZMod p) t) ht
  rw [harcos_trace_minpoly_phase (ZMod p) a b t ht]
  simp only [harcosEta, hc, if_false,
    (minpoly.monic (IsIntegral.of_finite (ZMod p) t)).leadingCoeff, div_one]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_mul]
  congr 1
  ring

/-- The finite set of minimal polynomials of nonzero elements of the extension. -/
def harcosMinpolyOrbits : Finset (ZMod p)[X] := by
  classical
  exact univ.image fun t : Fˣ => minpoly (ZMod p) (t : F)

/-- Each orbit is represented by its actual nonzero roots in the given field. -/
def harcosMinpolyFiber (k : (ZMod p)[X]) : Finset Fˣ := by
  classical
  exact univ.filter fun t : Fˣ => minpoly (ZMod p) (t : F) = k

theorem harcos_mem_minpolyOrbits (k : (ZMod p)[X]) :
    k ∈ harcosMinpolyOrbits p F ↔ ∃ t : Fˣ, minpoly (ZMod p) (t : F) = k := by
  classical
  simp [harcosMinpolyOrbits]

theorem harcos_mem_minpolyFiber (k : (ZMod p)[X]) (t : Fˣ) :
    t ∈ harcosMinpolyFiber p F k ↔ minpoly (ZMod p) (t : F) = k := by
  classical
  simp [harcosMinpolyFiber]

private theorem irreducible_splits_of_degree_dvd (k : (ZMod p)[X])
    (hi : Irreducible k) (hd : k.natDegree ∣ Module.finrank (ZMod p) F) :
    (k.map (algebraMap (ZMod p) F)).Splits := by
  have hdiv := hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd
  have hc : Nat.card (ZMod p) ^ Module.finrank (ZMod p) F = Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := F)).symm
  rw [hc] at hdiv
  apply (FiniteField.splits_X_pow_card_sub_X p (K := F)).of_dvd
  · simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using
      FiniteField.X_pow_card_sub_X_ne_zero F (Fintype.one_lt_card (α := F))
  · exact Polynomial.map_dvd (algebraMap (ZMod p) F) hdiv

omit [Fintype F] in
private theorem root_ne_zero (k : (ZMod p)[X]) (hc : k.coeff 0 ≠ 0)
    (x : F) (hx : aeval x k = 0) : x ≠ 0 := by
  intro he
  subst x
  apply hc
  apply (algebraMap (ZMod p) F).injective
  simpa only [aeval_def, eval₂_at_zero, map_zero] using hx

/-- Harcos's orbit index set is exactly all monic irreducibles of degree dividing
the extension degree, except `X`, excluded by the nonzero constant coefficient. -/
theorem harcos_mem_minpolyOrbits_iff (k : (ZMod p)[X]) :
    k ∈ harcosMinpolyOrbits p F ↔ k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧
      k.natDegree ∣ Module.finrank (ZMod p) F := by
  rw [harcos_mem_minpolyOrbits]
  constructor
  · rintro ⟨t, rfl⟩
    have hi := IsIntegral.of_finite (ZMod p) (t : F)
    exact ⟨minpoly.monic hi, minpoly.irreducible hi,
      minpoly.coeff_zero_ne_zero hi t.ne_zero, minpoly.degree_dvd hi⟩
  · rintro ⟨hm, hi, hc, hd⟩
    have hs := irreducible_splits_of_degree_dvd p F k hi hd
    have hdeg : (k.map (algebraMap (ZMod p) F)).degree ≠ 0 := by
      rw [degree_map]
      exact hi.degree_pos.ne'
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg
    rw [eval_map_algebraMap] at hx
    refine ⟨Units.mk0 x (root_ne_zero p F k hc x hx), ?_⟩
    exact (minpoly.eq_of_irreducible_of_monic hi hx hm).symm

/-- Each minimal-polynomial fiber has cardinality exactly its degree, with no
chosen algebraic closure and no assumption about orbit cardinalities. -/
theorem harcos_minpolyFiber_card (k : (ZMod p)[X])
    (hk : k ∈ harcosMinpolyOrbits p F) :
    (harcosMinpolyFiber p F k).card = k.natDegree := by
  classical
  obtain ⟨hm, hi, hc, hd⟩ := (harcos_mem_minpolyOrbits_iff p F k).mp hk
  let e : ↥(harcosMinpolyFiber p F k) ≃ k.rootSet F :=
    { toFun := fun t =>
        ⟨(t.1 : F), (mem_rootSet_of_ne hi.ne_zero).mpr (by
          have ht := (harcos_mem_minpolyFiber p F k t.1).mp t.2
          exact (congrArg (aeval (t.1 : F)) ht).symm.trans
            (minpoly.aeval (ZMod p) (t.1 : F)))⟩
      invFun := fun x =>
        ⟨Units.mk0 x.1 (root_ne_zero p F k hc x.1
          ((mem_rootSet_of_ne hi.ne_zero).mp x.2)),
          (harcos_mem_minpolyFiber p F k _).mpr
            (minpoly.eq_of_irreducible_of_monic hi
              ((mem_rootSet_of_ne hi.ne_zero).mp x.2) hm).symm⟩
      left_inv := fun t => by apply Subtype.ext; apply Units.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  calc
    (harcosMinpolyFiber p F k).card = Fintype.card ↥(harcosMinpolyFiber p F k) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (k.rootSet F) := Fintype.card_congr e
    _ = k.natDegree := card_rootSet_eq_natDegree (PerfectField.separable_of_irreducible hi)
      (irreducible_splits_of_degree_dvd p F k hi hd)

/-- The contribution of a single orbit is its degree times its eta power. -/
theorem harcos_minpolyFiber_character_sum (a b : ZMod p) (m : ℕ)
    (k : (ZMod p)[X]) (hk : k ∈ harcosMinpolyOrbits p F) :
    ∑ t ∈ harcosMinpolyFiber p F k,
      ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
        (algebraMap (ZMod p) F a * (t : F) + algebraMap (ZMod p) F b / (t : F))) =
      (k.natDegree : ℂ) *
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
  classical
  calc
    _ = ∑ _t ∈ harcosMinpolyFiber p F k,
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
      apply sum_congr rfl
      intro t ht
      rw [harcos_minpoly_eta_power p F a b m (t : F) t.ne_zero,
        (harcos_mem_minpolyFiber p F k t).mp ht]
    _ = _ := by rw [sum_const, harcos_minpolyFiber_card p F k hk, nsmul_eq_mul]

/-- The finite orbit-sum identity in the last step of Harcos's Theorem 6.
Together with `harcos_mem_minpolyOrbits_iff`, this is precisely the sum over
monic irreducibles of degrees dividing the extension degree, excluding `X`. -/
theorem harcos_trace_character_minpoly_sum [DecidableEq F] (a b : ZMod p) (m : ℕ) :
    ∑ t : Fˣ, ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
      (algebraMap (ZMod p) F a * (t : F) + algebraMap (ZMod p) F b / (t : F))) =
      ∑ k ∈ harcosMinpolyOrbits p F, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
  classical
  calc
    _ = ∑ k ∈ harcosMinpolyOrbits p F, ∑ t ∈ harcosMinpolyFiber p F k,
        ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b / (t : F))) := by
      have h := (sum_fiberwise_of_maps_to
        (s := univ) (t := harcosMinpolyOrbits p F)
        (g := fun t : Fˣ => minpoly (ZMod p) (t : F))
        (fun t _ => (harcos_mem_minpolyOrbits p F _).mpr ⟨t, rfl⟩)
        (fun t => ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b / (t : F))))).symm
      refine h.trans (sum_congr rfl fun k _ => sum_congr ?_ fun _ _ => rfl)
      ext t
      simp [harcos_mem_minpolyFiber]
    _ = _ := sum_congr rfl fun k hk => harcos_minpolyFiber_character_sum p F a b m k hk

/-- The orbit identity consumes the actual trace-character sum used in the
Artin–Schreier point-count bridge, for every prime-field frequency. -/
theorem harcosTraceKloosterman_minpoly_sum [DecidableEq F] (a b m : ZMod p) :
    harcosTraceKloosterman p F a b m =
      ∑ k ∈ harcosMinpolyOrbits p F, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m.val * (Module.finrank (ZMod p) F / k.natDegree)) := by
  simpa only [harcosTraceKloosterman, ZMod.natCast_zmod_val, div_eq_mul_inv] using
    harcos_trace_character_minpoly_sum p F a b m.val

end PrimeField

section ExtensionSequence

variable (p : ℕ) [Fact p.Prime]

/-- Frequency scaling agrees with an eta power on polynomials not divisible by
`X`. The nonzero-constant condition matters at frequency zero. -/
theorem harcosEta_frequency_of_coeff_zero_ne (a b m : ZMod p)
    (k : (ZMod p)[X]) (hk : k.coeff 0 ≠ 0) :
    harcosEta (m * a) (m * b) k = harcosEta a b k ^ m.val := by
  simp only [harcosEta, hk, if_false]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- Orbit indices for the same fixed extension used by `harcosExtensionKloosterman`. -/
def harcosExtensionMinpolyOrbits (n : ℕ) : Finset (ZMod p)[X] := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact harcosMinpolyOrbits p (GaloisField p n)

theorem harcos_mem_extensionMinpolyOrbits_iff (n : ℕ) (hn : 0 < n)
    (k : (ZMod p)[X]) :
    k ∈ harcosExtensionMinpolyOrbits p n ↔
      k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n := by
  let := Fintype.ofFinite (GaloisField p n)
  simpa only [harcosExtensionMinpolyOrbits, GaloisField.finrank p hn.ne'] using
    harcos_mem_minpolyOrbits_iff p (GaloisField p n) k

/-- The orbit identity for the actual extension sequence, only at positive
degrees: `GaloisField p 0` is not a field with one element. -/
theorem harcosExtensionKloosterman_minpoly_sum (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      ∑ k ∈ harcosExtensionMinpolyOrbits p n, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m.val * (n / k.natDegree)) := by
  let := Fintype.ofFinite (GaloisField p n)
  let := Classical.decEq (GaloisField p n)
  simpa only [harcosExtensionKloosterman, harcosExtensionMinpolyOrbits,
    GaloisField.finrank p hn.ne'] using
    harcosTraceKloosterman_minpoly_sum p (GaloisField p n) a b m

/-- Frequency-scaled form of the orbit identity, matching the finite Euler
coefficient for the actual polynomial character `harcosEta (m*a) (m*b)`. -/
theorem harcosExtensionKloosterman_minpoly_sum_scaled (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      ∑ k ∈ harcosExtensionMinpolyOrbits p n, (k.natDegree : ℂ) *
        harcosEta (m * a) (m * b) k ^ (n / k.natDegree) := by
  rw [harcosExtensionKloosterman_minpoly_sum p a b m n hn]
  apply sum_congr rfl
  intro k hk
  have hc := ((harcos_mem_extensionMinpolyOrbits_iff p n hn k).mp hk).2.2.1
  rw [harcosEta_frequency_of_coeff_zero_ne p a b m k hc, pow_mul]

/-- The independently constructed Euler index and actual field-orbit index agree. -/
theorem harcosExtensionMinpolyOrbits_eq_euler (n : ℕ) (hn : 0 < n) :
    harcosExtensionMinpolyOrbits p n = harcosEulerNonzeroPrimes p n := by
  ext k
  rw [harcos_mem_extensionMinpolyOrbits_iff p n hn k,
    mem_harcosEulerNonzeroPrimes n hn.ne' k]

/-- Actual extension-field character sums are the logarithmic coefficients of
the actual polynomial-character Euler series. -/
theorem harcosExtensionKloosterman_eq_eulerLogCoefficient (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      harcosEulerLogCoefficient (harcosEtaHom (m * a) (m * b)).toMonoidHom n := by
  rw [harcosExtensionKloosterman_minpoly_sum_scaled p a b m n hn,
    harcosExtensionMinpolyOrbits_eq_euler p n hn,
    harcosEuler_character_eq_nonzeroPrime_sum (m * a) (m * b) n hn.ne']

/-- Harcos's Theorem 6 with explicitly constructed reciprocal roots, not an
assumed power-sum or Euler identity. -/
theorem harcosExtensionKloosterman_eq_reciprocalRoots (a b m : ZMod p)
    (ha : a ≠ 0) (hm : m ≠ 0) (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      -(harcosReciprocalRootPlus (m * a) (m * b) ^ n +
        harcosReciprocalRootMinus (m * a) (m * b) ^ n) := by
  rw [harcosExtensionKloosterman_eq_eulerLogCoefficient p a b m n hn]
  exact harcosEuler_character_reciprocalRoots (m * a) (m * b) (mul_ne_zero hm ha) n hn.ne'

end ExtensionSequence

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
