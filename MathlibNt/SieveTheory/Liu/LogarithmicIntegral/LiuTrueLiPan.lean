import MathlibNt.SieveTheory.Liu.Weights.LiuWeightROuter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Main-parametric Pan consumption for Liu's coprime majorant

This module defines the fixed-parameter Pan objects for an arbitrary main-term
model and proves the finite structural implication needed by Liu's coprime
`eqn-r` lane. It does not assert the analytic Pan mean-value theorem.

The residue maximum uses the live ANT `unitResidues` convention. In particular,
the unique canonical residue modulo `1` is `0`.
-/

open scoped Asymptotics BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset

/-! ## Main-parametric finite Pan objects -/

/-- Exact change in a scaled AP error when only the additive normalization of
the logarithmic integral is changed. -/
theorem liuScaledAPError_sub_normalization
    (κ₂ κ₁ : ℝ) (Y a q l : ℕ) :
    liuScaledAPError (liuLogarithmicIntegral κ₂) Y a q l -
      liuScaledAPError (liuLogarithmicIntegral κ₁) Y a q l =
      -(κ₂ - κ₁) / Nat.totient q := by
  simp [liuScaledAPError, liuLogarithmicIntegral]
  ring

/-- The unrestricted Pan inner sum for an arbitrary main-term model. -/
noncomputable def liuMainPanInnerSum
    (main : ℝ → ℝ) (Y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1), f a * liuScaledAPError main Y a q l

/-- The coprime Pan inner sum for an arbitrary main-term model. -/
noncomputable def liuMainPanCoprimeSum
    (main : ℝ → ℝ) (Y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1),
    if a.Coprime q then f a * liuScaledAPError main Y a q l else 0

/-- The source-interval version of the coprime Pan sum, with Pan's convention
`A₁ < a ≤ A₂`. -/
noncomputable def liuMainPanCoprimeIntervalSum
    (main : ℝ → ℝ) (Y A₁ A₂ q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Ioc A₁ A₂,
    if a.Coprime q then f a * liuScaledAPError main Y a q l else 0

/-- Zero extension from a Pan source interval to the ambient finite range does
not alter the coprime aggregate.  This is the finite support bridge required
before applying Corollary (2.30). -/
theorem liuMainPanCoprimeSum_eq_sourceIntervalSum
    (main : ℝ → ℝ) (Y X A₁ A₂ q l : ℕ) (f : ℕ → ℝ)
    (hA₂X : A₂ ≤ X)
    (hsupp : ∀ a, a ≤ X → f a ≠ 0 → A₁ < a ∧ a ≤ A₂) :
    liuMainPanCoprimeSum main Y X q l f =
      liuMainPanCoprimeIntervalSum main Y A₁ A₂ q l f := by
  unfold liuMainPanCoprimeSum liuMainPanCoprimeIntervalSum
  symm
  apply Finset.sum_subset
  · intro a ha
    have haIoc := Finset.mem_Ioc.mp ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (haIoc.2.trans hA₂X))
  · intro a haRange haOutside
    have haX : a ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp haRange)
    have hfa : f a = 0 := by
      by_contra hne
      exact haOutside (Finset.mem_Ioc.mpr (hsupp a haX hne))
    simp [hfa]

/-- The maximum of the absolute coprime inner sum over canonical reduced
residues modulo `q`. The value at `q = 0` is `0`, while `q = 1` uses residue
`0`. -/
noncomputable def liuMainPanMaxL
    (main : ℝ → ℝ) (Y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := AnalyticNumberTheory.Sieve.unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |liuMainPanCoprimeSum main Y X q l f|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

/-- The maximum of `liuMainPanMaxL` over source parameters `Y ≤ N`. -/
noncomputable def liuMainPanMaxY
    (main : ℝ → ℝ) (X q N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (N + 1)).image (fun Y => liuMainPanMaxL main Y X q f)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The Pan modulus cutoff `⌊N^(1/2) / log(N)^B⌋`. -/
noncomputable def panModulusCutoff (N : ℕ) (B : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B)

/-- Liu's source cutoff is eventually contained in Pan's modulus range. -/
theorem eventually_liuSourceDEpsilon_le_panModulusCutoff
    (ε B : ℝ) (hε : 0 < ε) (_hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      liuSourceDEpsilon N ε ≤ panModulusCutoff N B := by
  have hreal : ∀ᶠ x : ℝ in atTop, Real.log x ^ B ≤ x ^ ε := by
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop B hε).bound
        (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) B),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) ε),
      one_mul] at hx
    exact hx
  have hnat :
      ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ ε :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with N hgrowth hN
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (by omega : 0 < N)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogpowpos : 0 < Real.log (N : ℝ) ^ B :=
    Real.rpow_pos_of_pos hlogpos B
  unfold liuSourceDEpsilon panModulusCutoff
  apply Nat.floor_le_floor
  rw [Real.rpow_sub hNpos]
  exact div_le_div_of_nonneg_left
    (Real.rpow_nonneg hNpos.le _) hlogpowpos hgrowth

/-- Existential threshold form of the eventual Liu-to-Pan cutoff inclusion. -/
theorem exists_liuSourceDEpsilon_le_panModulusCutoff
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      liuSourceDEpsilon N ε ≤ panModulusCutoff N B :=
  eventually_atTop.mp
    (eventually_liuSourceDEpsilon_le_panModulusCutoff ε B hε hB)

/-- The fixed-`N` main-parametric Pan weighted sum. -/
noncomputable def liuMainPanWeightedSum
    (main : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
        liuMainPanMaxY main N q N f

/-- The endpoint-only weighted sum at `Y = N`.  This is the exact prefix needed
by Liu's source-`Q` consumer and avoids strengthening Pan--Ding--Wang's source
interval hypotheses to every small prefix. -/
noncomputable def liuMainPanEndpointWeightedSum
    (main : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
        liuMainPanMaxL main N N q f

/-- Fixed-`N` endpoint form of the weighted Pan mean-value inequality. -/
def LiuMainPanEndpointMeanValueAt
    (main : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) : Prop :=
  liuMainPanEndpointWeightedSum main N f B ≤ C * N / Real.log N ^ A

/-- A transparent fixed-`N` instance of the main-parametric Pan mean-value
inequality. This is a predicate for consuming an analytic input, not a proof of
that input. -/
def LiuMainPanMeanValueAt
    (main : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) : Prop :=
  liuMainPanWeightedSum main N f B ≤ C * N / Real.log N ^ A

/-! ## Proxy compatibility -/

/-- **Proxy compatibility.** The unrestricted object specializes to ANT's
historical `x / log x` finite sum. This is not a true-`li` statement. -/
theorem liuMainPanInnerSum_proxy
    (Y X q l : ℕ) (f : ℕ → ℝ) :
    liuMainPanInnerSum AnalyticNumberTheory.Sieve.logarithmicIntegral
        Y X q l f =
      AnalyticNumberTheory.Sieve.panDistributionFullSum Y X q l f := by
  rfl

/-- **Proxy compatibility.** The coprime object specializes to ANT's historical
`x / log x` finite sum. This is not a true-`li` statement. -/
theorem liuMainPanCoprimeSum_proxy
    (Y X q l : ℕ) (f : ℕ → ℝ) :
    liuMainPanCoprimeSum AnalyticNumberTheory.Sieve.logarithmicIntegral
        Y X q l f =
      AnalyticNumberTheory.Sieve.panDistributionSum Y X q l f := by
  rfl

/-- The new coprime sum is definitionally the coprime sum used by the Liu
source-Q majorant. -/
theorem liuMainPanCoprimeSum_eq_liuMainCoprimeSum
    (main : ℝ → ℝ) (Y X q l : ℕ) (f : ℕ → ℝ) :
    liuMainPanCoprimeSum main Y X q l f =
      liuMainCoprimeSum main Y X q l f := by
  rfl

/-- **Proxy compatibility.** The canonical-residue maximum specializes
definitionally to ANT's live `panMaxL`. -/
theorem liuMainPanMaxL_proxy
    (Y X q : ℕ) (f : ℕ → ℝ) :
    liuMainPanMaxL AnalyticNumberTheory.Sieve.logarithmicIntegral Y X q f =
      AnalyticNumberTheory.Sieve.panMaxL Y X q f := by
  rfl

/-- **Proxy compatibility.** The source-parameter maximum specializes
definitionally to ANT's live `panMaxY`. -/
theorem liuMainPanMaxY_proxy
    (X q N : ℕ) (f : ℕ → ℝ) :
    liuMainPanMaxY AnalyticNumberTheory.Sieve.logarithmicIntegral X q N f =
      AnalyticNumberTheory.Sieve.panMaxY X q N f := by
  rfl

/-- In particular, the modulus-one maximum uses the canonical residue `0`. -/
@[simp] theorem liuMainPanMaxL_one
    (main : ℝ → ℝ) (Y X : ℕ) (f : ℕ → ℝ) :
    liuMainPanMaxL main Y X 1 f =
      |liuMainPanCoprimeSum main Y X 1 0 f| := by
  simp [liuMainPanMaxL]

/-- **Proxy compatibility.** The fixed weighted sum specializes to the finite
left side occurring in ANT's `PanMeanValueUniform`. -/
theorem liuMainPanWeightedSum_proxy
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) :
    liuMainPanWeightedSum
        AnalyticNumberTheory.Sieve.logarithmicIntegral N f B =
      ∑ q ∈ range (panModulusCutoff N B + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
            AnalyticNumberTheory.Sieve.panMaxY N q N f := by
  rfl

/-- **Proxy compatibility.** This is only a fixed-`N` restatement of ANT's
historical proxy finite inequality, not an analytic theorem. -/
theorem LiuMainPanMeanValueAt_proxy
    (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) :
    LiuMainPanMeanValueAt
        AnalyticNumberTheory.Sieve.logarithmicIntegral N f A B C ↔
      (∑ q ∈ range (panModulusCutoff N B + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
            AnalyticNumberTheory.Sieve.panMaxY N q N f) ≤
        C * N / Real.log N ^ A := by
  rfl

/-! ## Finite consumption bridge -/

theorem liuMainPanMaxL_nonneg
    (main : ℝ → ℝ) (Y X q : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuMainPanMaxL main Y X q f := by
  unfold liuMainPanMaxL
  dsimp only
  by_cases hS : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty
  · rw [dif_pos hS]
    have hmem :
        ((AnalyticNumberTheory.Sieve.unitResidues q).image
            (fun l => |liuMainPanCoprimeSum main Y X q l f|)).max'
              (Finset.image_nonempty.mpr hS) ∈
          (AnalyticNumberTheory.Sieve.unitResidues q).image
            (fun l => |liuMainPanCoprimeSum main Y X q l f|) :=
      Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨l, _, hl⟩
    rw [← hl]
    exact abs_nonneg _
  · rw [dif_neg hS]

theorem liuMainPanMaxY_nonneg
    (main : ℝ → ℝ) (X q N : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuMainPanMaxY main X q N f := by
  unfold liuMainPanMaxY
  have hmem :
      liuMainPanMaxL main 0 X q f ∈
        (range (N + 1)).image (fun Y => liuMainPanMaxL main Y X q f) :=
    Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  exact (liuMainPanMaxL_nonneg main 0 X q f).trans
    (Finset.le_max' _ _ hmem)

/-- A canonical reduced residue is bounded by the residue maximum at the same
endpoint. -/
theorem abs_liuMainPanCoprimeSum_le_maxL
    (main : ℝ → ℝ) (Y X q l : ℕ) (f : ℕ → ℝ)
    (hl : l ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    |liuMainPanCoprimeSum main Y X q l f| ≤
      liuMainPanMaxL main Y X q f := by
  have hS : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty := ⟨l, hl⟩
  unfold liuMainPanMaxL
  dsimp only
  rw [dif_pos hS]
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨l, hl, rfl⟩

/-- A canonical reduced residue and a source parameter in range are bounded by
the two nested Pan maxima. -/
theorem abs_liuMainPanCoprimeSum_le_maxY
    (main : ℝ → ℝ) (Y X q N l : ℕ) (f : ℕ → ℝ)
    (hY : Y ≤ N)
    (hl : l ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    |liuMainPanCoprimeSum main Y X q l f| ≤
      liuMainPanMaxY main X q N f := by
  have hS : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty := ⟨l, hl⟩
  have hleL :
      |liuMainPanCoprimeSum main Y X q l f| ≤
        liuMainPanMaxL main Y X q f := by
    unfold liuMainPanMaxL
    dsimp only
    rw [dif_pos hS]
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  apply hleL.trans
  unfold liuMainPanMaxY
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨Y, Finset.mem_range.mpr (by omega), rfl⟩

/-- The source-faithful endpoint structural bridge: Pan's weighted estimate at
`Y = N` already controls the only prefix used by Liu's source-`Q` coprime
majorant. No maximum over unsupported small prefixes is needed. -/
theorem liuPaperQCoprimeRBound_of_liuMainPanEndpointMeanValueAt
    (main : ℝ → ℝ) (N : ℕ) (ε A B C : ℝ)
    (hcut : liuSourceDEpsilon N ε ≤ panModulusCutoff N B)
    (hpan : LiuMainPanEndpointMeanValueAt main N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C) :
    LiuPaperQCoprimeRBound main N ε A C := by
  classical
  have hQsq : Squarefree (liuPaperQModulus N ε) := by
    rw [liuPaperQModulus_eq_paperQStyleModulus]
    exact paperQStyleModulus_squarefree N (paperQSourceCutoff N ε)
  have hQN : Nat.Coprime (liuPaperQModulus N ε) N := by
    apply Nat.coprime_of_dvd'
    intro r hr hrQ hrN
    rw [liuPaperQModulus_eq_paperQStyleModulus] at hrQ
    exact False.elim (((prime_dvd_paperQStyleModulus hr).mp hrQ).2 hrN)
  unfold LiuPaperQCoprimeRBound
    liuPaperQSourceCoprimeDistributionMajorant
  calc
    (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
        (fun d => d ≤ liuSourceDEpsilon N ε),
        (3 : ℝ) ^ d.primeFactors.card *
          |liuMainCoprimeSum main N N d (N % d)
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) ≤
        ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ d.primeFactors.card *
              liuMainPanMaxL main N N d
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mem_filter] at hd
      have hdvd : d ∣ liuPaperQModulus N ε :=
        Nat.dvd_of_mem_divisors hd.1
      have hdsq : Squarefree d := hQsq.squarefree_of_dvd hdvd
      have hmu :
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 := by
        rw [← Int.cast_pow]
        exact_mod_cast
          ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq
      have hdN : Nat.Coprime d N :=
        Nat.Coprime.coprime_dvd_left hdvd hQN
      have hmodcop : (N % d).Coprime d := by
        apply Nat.coprime_of_dvd'
        intro r hr hrmod hrd
        have hrN : r ∣ N := by
          have hsum : r ∣ d * (N / d) + N % d :=
            Nat.dvd_add
              (by simpa [mul_comm] using
                (dvd_mul_of_dvd_right hrd (N / d)))
              hrmod
          have hNdef : d * (N / d) + N % d = N := by
            simpa [Nat.add_comm] using (Nat.mod_add_div N d)
          rw [← hNdef]
          exact hsum
        exact False.elim
          (Nat.not_coprime_of_dvd_of_dvd
            (Nat.Prime.one_lt hr) hrd hrN hdN)
      have hres :
          N % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
        rw [AnalyticNumberTheory.Sieve.unitResidues]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr
              (Nat.mod_lt N (Nat.pos_of_mem_divisors hd.1)),
            hmodcop⟩
      have hinner :
          |liuMainCoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
            liuMainPanMaxL main N N d
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        rw [← liuMainPanCoprimeSum_eq_liuMainCoprimeSum]
        exact abs_liuMainPanCoprimeSum_le_maxL
          main N N d (N % d)
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) hres
      rw [hmu, one_mul]
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ ∑ q ∈ range (panModulusCutoff N B + 1),
          (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ q.primeFactors.card *
              liuMainPanMaxL main N N q
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter] at hd
        exact Finset.mem_range.mpr (by omega)
      · intro d _ _
        exact mul_nonneg
          (mul_nonneg (sq_nonneg _) (by positivity))
          (liuMainPanMaxL_nonneg main N N d
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))
    _ ≤ C * N / Real.log N ^ A := hpan


/-- The exact structural consumption bridge: a fixed-`N`, main-parametric Pan
mean-value inequality controls Liu's source-Q coprime majorant whenever its
source divisor cutoff is inside the Pan modulus cutoff. -/
theorem liuPaperQCoprimeRBound_of_liuMainPanMeanValueAt
    (main : ℝ → ℝ) (N : ℕ) (ε A B C : ℝ)
    (hcut : liuSourceDEpsilon N ε ≤ panModulusCutoff N B)
    (hpan : LiuMainPanMeanValueAt main N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C) :
    LiuPaperQCoprimeRBound main N ε A C := by
  classical
  have hQsq : Squarefree (liuPaperQModulus N ε) := by
    rw [liuPaperQModulus_eq_paperQStyleModulus]
    exact paperQStyleModulus_squarefree N (paperQSourceCutoff N ε)
  have hQN : Nat.Coprime (liuPaperQModulus N ε) N := by
    apply Nat.coprime_of_dvd'
    intro r hr hrQ hrN
    rw [liuPaperQModulus_eq_paperQStyleModulus] at hrQ
    exact False.elim (((prime_dvd_paperQStyleModulus hr).mp hrQ).2 hrN)
  unfold LiuPaperQCoprimeRBound
    liuPaperQSourceCoprimeDistributionMajorant
  calc
    (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
        (fun d => d ≤ liuSourceDEpsilon N ε),
        (3 : ℝ) ^ d.primeFactors.card *
          |liuMainCoprimeSum main N N d (N % d)
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) ≤
        ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ d.primeFactors.card *
              liuMainPanMaxY main N d N
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mem_filter] at hd
      have hdvd : d ∣ liuPaperQModulus N ε :=
        Nat.dvd_of_mem_divisors hd.1
      have hdsq : Squarefree d := hQsq.squarefree_of_dvd hdvd
      have hmu :
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 := by
        rw [← Int.cast_pow]
        exact_mod_cast
          ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq
      have hdN : Nat.Coprime d N :=
        Nat.Coprime.coprime_dvd_left hdvd hQN
      have hmodcop : (N % d).Coprime d := by
        apply Nat.coprime_of_dvd'
        intro r hr hrmod hrd
        have hrN : r ∣ N := by
          have hsum : r ∣ d * (N / d) + N % d :=
            Nat.dvd_add
              (by simpa [mul_comm] using
                (dvd_mul_of_dvd_right hrd (N / d)))
              hrmod
          have hNdef : d * (N / d) + N % d = N := by
            simpa [Nat.add_comm] using (Nat.mod_add_div N d)
          rw [← hNdef]
          exact hsum
        exact False.elim
          (Nat.not_coprime_of_dvd_of_dvd
            (Nat.Prime.one_lt hr) hrd hrN hdN)
      have hres :
          N % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
        rw [AnalyticNumberTheory.Sieve.unitResidues]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr
              (Nat.mod_lt N (Nat.pos_of_mem_divisors hd.1)),
            hmodcop⟩
      have hinner :
          |liuMainCoprimeSum main N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
            liuMainPanMaxY main N d N
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        rw [← liuMainPanCoprimeSum_eq_liuMainCoprimeSum]
        exact abs_liuMainPanCoprimeSum_le_maxY
          main N N d N (N % d)
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
          (le_refl N) hres
      rw [hmu, one_mul]
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ ∑ q ∈ range (panModulusCutoff N B + 1),
          (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ q.primeFactors.card *
              liuMainPanMaxY main N q N
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter] at hd
        exact Finset.mem_range.mpr (by omega)
      · intro d _ _
        exact mul_nonneg
          (mul_nonneg (sq_nonneg _) (by positivity))
          (liuMainPanMaxY_nonneg main N d N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))
    _ ≤ C * N / Real.log N ^ A := hpan

/-- The genuine logarithmic-integral specialization retains both the analytic
fixed-`N` Pan predicate and the cutoff inclusion as explicit hypotheses. -/
theorem liuLogarithmicIntegral_liuPaperQCoprimeRBound_of_panMeanValueAt
    (κ : ℝ) (N : ℕ) (ε A B C : ℝ)
    (hcut : liuSourceDEpsilon N ε ≤ panModulusCutoff N B)
    (hpan : LiuMainPanMeanValueAt (liuLogarithmicIntegral κ) N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral κ) N ε A C :=
  liuPaperQCoprimeRBound_of_liuMainPanMeanValueAt
    (liuLogarithmicIntegral κ) N ε A B C hcut hpan

/-- Beyond a threshold depending only on `ε` and `B`, the true logarithmic-
integral coprime bound requires only the fixed-`N` Pan mean-value input. -/
theorem exists_liuLogarithmicIntegral_liuPaperQCoprimeRBound_of_panMeanValueAt
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) (κ A C : ℝ), N₀ ≤ N →
      LiuMainPanMeanValueAt (liuLogarithmicIntegral κ) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C →
      LiuPaperQCoprimeRBound (liuLogarithmicIntegral κ) N ε A C := by
  rcases exists_liuSourceDEpsilon_le_panModulusCutoff ε B hε hB with
    ⟨N₀, hcut⟩
  refine ⟨N₀, fun N κ A C hN hpan ↦ ?_⟩
  exact liuLogarithmicIntegral_liuPaperQCoprimeRBound_of_panMeanValueAt
    κ N ε A B C (hcut N hN) hpan

private theorem abs_liuMainCoprimeSum_li_normalization_sub_le
    (κ₂ κ₁ : ℝ) (N d l : ℕ) (hd : 0 < d) :
    |liuMainCoprimeSum (liuLogarithmicIntegral κ₂) N N d l
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) -
      liuMainCoprimeSum (liuLogarithmicIntegral κ₁) N N d l
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| ≤
      |κ₂ - κ₁| / Nat.totient d *
        (∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a) := by
  classical
  rw [liuMainCoprimeSum, liuMainCoprimeSum, ← Finset.sum_sub_distrib]
  calc
    |∑ a ∈ range (N + 1),
        ((if a.Coprime d then
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              liuScaledAPError (liuLogarithmicIntegral κ₂) N a d l
          else 0) -
         (if a.Coprime d then
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              liuScaledAPError (liuLogarithmicIntegral κ₁) N a d l
          else 0))| ≤
      ∑ a ∈ range (N + 1),
        |(if a.Coprime d then
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              liuScaledAPError (liuLogarithmicIntegral κ₂) N a d l
          else 0) -
         (if a.Coprime d then
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
              liuScaledAPError (liuLogarithmicIntegral κ₁) N a d l
          else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ range (N + 1),
        (|κ₂ - κ₁| / Nat.totient d) *
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hcop : a.Coprime d
      · rw [if_pos hcop, if_pos hcop]
        rw [← mul_sub, liuScaledAPError_sub_normalization]
        have htot : (0 : ℝ) < Nat.totient d := by
          exact_mod_cast Nat.totient_pos.mpr hd
        rw [abs_mul, abs_div, abs_neg, abs_of_pos htot]
        have hw : 0 ≤ liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
          unfold liuWeight
          split <;> positivity
        rw [abs_of_nonneg hw]
        ring_nf
        exact le_rfl
      · rw [if_neg hcop, if_neg hcop, zero_sub, neg_zero, abs_zero]
        exact mul_nonneg (div_nonneg (abs_nonneg _) (by positivity)) (by
          unfold liuWeight
          split <;> positivity)
    _ = (|κ₂ - κ₁| / Nat.totient d) *
        (∑ a ∈ range (N + 1),
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a) := by
      rw [Finset.mul_sum]
    _ = (|κ₂ - κ₁| / Nat.totient d) *
        (∑ a ∈ Icc 1 N,
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a) := by
      congr 1
      symm
      apply Finset.sum_subset
      · intro a ha
        rw [Finset.mem_Icc] at ha
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha.2)
      · intro a haRange haOutside
        have ha0 : a = 0 := by
          rw [Finset.mem_range] at haRange
          rw [Finset.mem_Icc] at haOutside
          omega
        subst a
        unfold liuWeight
        rw [if_neg]
        intro hsupp
        rcases liuWeightSupport_iff.mp hsupp with ⟨p₁, p₂, hp, hzero⟩
        have hprod : 0 < p₁ * p₂ := Nat.mul_pos hp.1.pos hp.2.1.pos
        omega

/-- Changing only the additive normalization of the genuine logarithmic integral
costs the source mass times the full paper-Q divisor weight. -/
theorem liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    (κ₂ κ₁ : ℝ) (N : ℕ) (ε : ℝ) :
    liuPaperQSourceCoprimeDistributionMajorant
        (liuLogarithmicIntegral κ₂) N ε ≤
      liuPaperQSourceCoprimeDistributionMajorant
          (liuLogarithmicIntegral κ₁) N ε +
        |κ₂ - κ₁| *
          (∑ a ∈ Icc 1 N,
            liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a) *
          paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N ε) := by
  classical
  let mass : ℝ := ∑ a ∈ Icc 1 N,
    liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a
  have hQ0 : liuPaperQModulus N ε ≠ 0 := by
    rw [liuPaperQModulus_eq_paperQStyleModulus]
    exact paperQStyleModulus_ne_zero N (paperQSourceCutoff N ε)
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    apply Finset.sum_nonneg
    intro a ha
    unfold liuWeight
    split <;> positivity
  unfold liuPaperQSourceCoprimeDistributionMajorant
  calc
    (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
        (fun d => d ≤ liuSourceDEpsilon N ε),
        (3 : ℝ) ^ d.primeFactors.card *
          |liuMainCoprimeSum (liuLogarithmicIntegral κ₂) N N d (N % d)
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) ≤
      ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
        (fun d => d ≤ liuSourceDEpsilon N ε),
        (3 : ℝ) ^ d.primeFactors.card *
          (|liuMainCoprimeSum (liuLogarithmicIntegral κ₁) N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))| +
            |κ₂ - κ₁| / Nat.totient d * mass) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hddiv : d ∣ liuPaperQModulus N ε :=
        Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdmem).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddiv (Nat.pos_of_ne_zero hQ0)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hdiff := abs_liuMainCoprimeSum_li_normalization_sub_le
        κ₂ κ₁ N d (N % d) hdpos
      linarith [abs_sub_abs_le_abs_sub
        (liuMainCoprimeSum (liuLogarithmicIntegral κ₂) N N d (N % d)
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))
        (liuMainCoprimeSum (liuLogarithmicIntegral κ₁) N N d (N % d)
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))]
    _ = (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainCoprimeSum (liuLogarithmicIntegral κ₁) N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) +
        |κ₂ - κ₁| * mass *
          (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
            (fun d => d ≤ liuSourceDEpsilon N ε),
            (3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (∑ d ∈ (liuPaperQModulus N ε).divisors.filter
          (fun d => d ≤ liuSourceDEpsilon N ε),
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainCoprimeSum (liuLogarithmicIntegral κ₁) N N d (N % d)
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))|) +
        |κ₂ - κ₁| * mass *
          paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N ε) := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (abs_nonneg _) hmass)
      rw [liuPaperQModulus_eq_paperQStyleModulus]
      unfold paperQStyleFullDivisorWeightSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact (Finset.mem_filter.mp hd).1
      · intro d hd hdnot
        positivity

/-- Explicit finite `N^(2/3) log^3 N` normalization-loss bound. -/
theorem liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le_rpow
    (κ₂ κ₁ : ℝ) (N : ℕ) (ε : ℝ) (hN : 3 ≤ N) (hε : 0 ≤ ε) :
    liuPaperQSourceCoprimeDistributionMajorant
        (liuLogarithmicIntegral κ₂) N ε ≤
      liuPaperQSourceCoprimeDistributionMajorant
          (liuLogarithmicIntegral κ₁) N ε +
        (3 * paperQStyleDivisorWeightLogConstant) * |κ₂ - κ₁| *
          (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ 3 := by
  have hmass := sum_liuWeight_Icc_le_three_mul_rpow_two_thirds
    N (liuSourceZ10 N) (liuSourceY3 N) (by omega)
  have hcut : paperQSourceCutoff N ε ≤ N :=
    (paperQSourceCutoff_le_floor_cuberoot N ε (by omega) hε).trans
      (liuSourceY3_le N (by omega))
  have hdiv := paperQStyleFullDivisorWeightSum_le_log_cube
    N (paperQSourceCutoff N ε) hN hcut
  refine (liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    κ₂ κ₁ N ε).trans ?_
  apply add_le_add (le_refl _)
  have hdelta : 0 ≤ |κ₂ - κ₁| := abs_nonneg _
  have hmass0 : 0 ≤ ∑ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
    apply Finset.sum_nonneg
    intro a ha
    unfold liuWeight
    split <;> positivity
  calc
    |κ₂ - κ₁| *
        (∑ a ∈ Icc 1 N,
          liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a) *
        paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N ε) ≤
      |κ₂ - κ₁| * (3 * (N : ℝ) ^ (2 / 3 : ℝ)) *
        (paperQStyleDivisorWeightLogConstant * Real.log N ^ 3) :=
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hdelta)
        (by
          unfold paperQStyleFullDivisorWeightSum
          positivity)).trans
        (mul_le_mul_of_nonneg_left hdiv
          (mul_nonneg hdelta (mul_nonneg (by norm_num)
            (Real.rpow_nonneg (by positivity) _))))
    _ = (3 * paperQStyleDivisorWeightLogConstant) * |κ₂ - κ₁| *
        (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ 3 := by ring

/-- Any fixed multiple of `N^(2/3) log^3 N` is eventually absorbed by
`N / log^A N`, for an arbitrary fixed real logarithmic exponent `A`. -/
theorem eventually_mul_rpow_two_thirds_log_cube_le_div_log_rpow
    (C A : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ 3 ≤
        (N : ℝ) / Real.log N ^ A := by
  let η : ℝ := (C + 1)⁻¹
  have hC1 : 0 < C + 1 := by linarith
  have hη : 0 < η := inv_pos.mpr hC1
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (A + 3) (by norm_num : (0 : ℝ) < 1 / 3)).bound hη
  have hnat : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (N : ℝ) ^ (A + 3)‖ ≤
        η * ‖(N : ℝ) ^ (1 / 3 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with N hbound hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hbound' : Real.log (N : ℝ) ^ (A + 3) ≤
      η * (N : ℝ) ^ (1 / 3 : ℝ) := by
    simpa [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _)] using hbound
  have hCη : C * η ≤ 1 := by
    dsimp [η]
    rw [mul_inv_le_iff₀ hC1]
    linarith
  have hlogpow :
      Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ A =
        Real.log (N : ℝ) ^ (A + 3) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hlog]
    congr 1
    norm_num [add_comm]
  have hNpow :
      (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog A)]
  calc
    C * (N : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ 3 *
        Real.log N ^ A =
      (N : ℝ) ^ (2 / 3 : ℝ) *
        (C * Real.log N ^ (A + 3)) := by rw [← hlogpow]; ring
    _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) *
        (C * (η * (N : ℝ) ^ (1 / 3 : ℝ))) := by
      gcongr
    _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) *
        (N : ℝ) ^ (1 / 3 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hNpos.le _)
      calc
        C * (η * (N : ℝ) ^ (1 / 3 : ℝ)) =
            (C * η) * (N : ℝ) ^ (1 / 3 : ℝ) := by ring
        _ ≤ 1 * (N : ℝ) ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hCη (Real.rpow_nonneg hNpos.le _)
        _ = (N : ℝ) ^ (1 / 3 : ℝ) := one_mul _
    _ = (N : ℝ) := hNpow

/-- The additive-normalization loss in the aggregate coprime Pan majorant is
eventually absorbable into any prescribed inverse logarithmic power. -/
theorem eventually_liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    (κ₂ κ₁ ε A : ℝ) (hε : 0 ≤ ε) :
    ∀ᶠ N : ℕ in atTop,
      liuPaperQSourceCoprimeDistributionMajorant
          (liuLogarithmicIntegral κ₂) N ε ≤
        liuPaperQSourceCoprimeDistributionMajorant
            (liuLogarithmicIntegral κ₁) N ε +
          (N : ℝ) / Real.log N ^ A := by
  have habsorb :=
    eventually_mul_rpow_two_thirds_log_cube_le_div_log_rpow
      ((3 * paperQStyleDivisorWeightLogConstant) * |κ₂ - κ₁|) A
      (mul_nonneg
        (mul_nonneg (by norm_num) paperQStyleDivisorWeightLogConstant_nonneg)
        (abs_nonneg _))
  filter_upwards [habsorb, eventually_ge_atTop (3 : ℕ)] with N habsorbN hN
  exact (liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le_rpow
    κ₂ κ₁ N ε hN hε).trans (add_le_add (le_refl _) habsorbN)

set_option maxHeartbeats 800000 in
/-- Consequently, an eventual inverse-log bound for one additive normalization
transfers to every other normalization, at the cost of adding `1` to the fixed
constant. -/
theorem eventually_liuPaperQSourceCoprimeDistributionMajorant_li_normalization_transfer
    (κ₂ κ₁ ε A C : ℝ) (hε : 0 ≤ ε)
    (hκ₁ : ∀ᶠ N : ℕ in atTop,
      liuPaperQSourceCoprimeDistributionMajorant
          (liuLogarithmicIntegral κ₁) N ε ≤
        C * (N : ℝ) / Real.log N ^ A) :
    ∀ᶠ N : ℕ in atTop,
      liuPaperQSourceCoprimeDistributionMajorant
          (liuLogarithmicIntegral κ₂) N ε ≤
        (C + 1) * (N : ℝ) / Real.log N ^ A := by
  have hchange :=
    eventually_liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
      κ₂ κ₁ ε A hε
  filter_upwards [hκ₁, hchange] with N hκ₁N hchangeN
  calc
    liuPaperQSourceCoprimeDistributionMajorant
        (liuLogarithmicIntegral κ₂) N ε ≤
      liuPaperQSourceCoprimeDistributionMajorant
          (liuLogarithmicIntegral κ₁) N ε +
        (N : ℝ) / Real.log N ^ A := hchangeN
    _ ≤ C * (N : ℝ) / Real.log N ^ A +
        (N : ℝ) / Real.log N ^ A := add_le_add hκ₁N (le_refl _)
    _ = (C + 1) * (N : ℝ) / Real.log N ^ A := by ring

end MathlibNt.SieveTheory.LiuWeight
