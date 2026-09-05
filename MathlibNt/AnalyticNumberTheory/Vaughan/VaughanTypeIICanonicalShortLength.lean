

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMoment
import MathlibNt.AnalyticNumberTheory.LargeSieve.DyadicPrefixMaximal
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear

/-!
 # Short physical length on a canonical Vaughan Type-II shell

For `d` in the canonical shell of level `k`, the collected variable `t=e*m`
is supported on `t ≤ y / 2^k`.  Consequently the primitive (prefix-maximal)
large sieve is charged at this short length, not at the ambient length `y`.
The last lemmas record the cancellation of the outer Möbius energy `2^k`
against this length and retain the resulting `2^k Q^2` charge.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The common long-variable length on the canonical `d`-shell of level `k`. -/
def vaughanCanonicalTensorLength (y k : ℕ) : ℕ := y / 2 ^ k

/-- Tensor energy restricted to the actual common support of a canonical shell. -/
def vaughanCanonicalShortTensorEnergy
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y N u v k l : ℕ) : ℝ :=
  ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
    ∑ t ∈ Finset.Icc (1 : ℤ) (vaughanCanonicalTensorLength y k),
      ‖vaughanBilinearTensorCoeff β c y d
        (vaughanCanonicalDyadicBlock N v l) t‖ ^ 2

private lemma nat_of_int_Icc_le {t : ℤ} {X : ℕ}
    (ht : t ∈ Finset.Icc (1 : ℤ) X) : t.toNat ≤ X := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) (Finset.mem_Icc.mp ht).1
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
  exact_mod_cast htcast.trans_le (Finset.mem_Icc.mp ht).2

/-- Every actual `t=e*m` fibre on level `k` lies below `y / 2^k`.
This uses the closed lower shell endpoint `2^k ≤ d`; in particular `k=0`
gives the literal bound `t ≤ y`. -/
lemma vaughanTensorFiber_canonical_support
    (y N u v k l d : ℕ) (t : ℤ)
    (hd : d ∈ vaughanCanonicalDyadicBlock N u k)
    (ht : t ∈ Finset.Icc (1 : ℤ) y)
    (hne : (vaughanTensorFiber y d
      (vaughanCanonicalDyadicBlock N v l) t).Nonempty) :
    t.toNat ≤ vaughanCanonicalTensorLength y k := by
  have hdt : d * t.toNat ≤ y :=
    vaughanTensorFiber_support y d _ t
      (mem_vaughanCanonicalDyadicBlock.mp hd).1 ht hne
  have hk : 2 ^ k ≤ d := (vaughanCanonicalDyadicBlock_pow_bounds hd).1
  have hpow : 2 ^ k * t.toNat ≤ y :=
    (Nat.mul_le_mul_right t.toNat hk).trans hdt
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
    (by simpa [mul_comm] using hpow)

/-- Outside the short shell length the actual tensor coefficient vanishes. -/
lemma vaughanBilinearTensorCoeff_canonical_eq_zero
    (b : ℕ → ℂ) (y N u v k l d : ℕ) (t : ℤ)
    (hd : d ∈ vaughanCanonicalDyadicBlock N u k)
    (ht : t ∈ Finset.Icc (1 : ℤ) y)
    (hlt : vaughanCanonicalTensorLength y k < t.toNat) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d
      (vaughanCanonicalDyadicBlock N v l) t = 0 := by
  rw [vaughanBilinearTensorCoeff_eq_fiber b y d _ t
    (fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1)]
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  exact (not_le_of_gt hlt) (vaughanTensorFiber_canonical_support
    y N u v k l d t hd ht ⟨e, he⟩)

/-- The old ambient `t ≤ y` energy is exactly the energy on the short support. -/
theorem vaughanBilinearTensorEnergy_canonical_eq_short
    (b : ℕ → ℂ) (y N u v k l : ℕ) :
    vaughanBilinearTensorEnergy vaughanMangoldtCoeff b y
        (vaughanCanonicalDyadicBlock N u k)
        (vaughanCanonicalDyadicBlock N v l) =
      vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
        y N u v k l := by
  unfold vaughanBilinearTensorEnergy vaughanCanonicalShortTensorEnergy
  apply Finset.sum_congr rfl
  intro d hd
  have hL : vaughanCanonicalTensorLength y k ≤ y :=
    Nat.div_le_self y (2 ^ k)
  have hsub : Finset.Icc (1 : ℤ) (vaughanCanonicalTensorLength y k) ⊆
      Finset.Icc (1 : ℤ) y := Finset.Icc_subset_Icc_right (by exact_mod_cast hL)
  rw [← Finset.sum_subset hsub]
  intro t hty htL
  have hnot : vaughanCanonicalTensorLength y k < t.toNat := by
    have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp hty).1
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
    by_contra h
    have hle : t.toNat ≤ vaughanCanonicalTensorLength y k := le_of_not_gt h
    apply htL
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hty).1,
      by rw [← htcast]; exact_mod_cast hle⟩
  rw [vaughanBilinearTensorCoeff_canonical_eq_zero b y N u v k l d t hd hty hnot]
  norm_num

/-- The complete prefix maximum in the collected variable `t`, row by row. -/
def vaughanCanonicalTensorPrefixMaxEnergy
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
    primitiveCharacterPrefixMaxSquare
      (fun t => vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d
        (vaughanCanonicalDyadicBlock N v l) t)
      0 (vaughanCanonicalTensorLength y k) q χ

/-- Prefix-maximal primitive LS charged at `y / 2^k`, uniformly for every row
of the canonical shell.  The maximum remains inside the character sum. -/
theorem weighted_primitive_vaughanCanonicalTensorPrefix
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
          vaughanCanonicalTensorPrefixMaxEnergy b y N u v k l q χ) ≤
      vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
        (((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant (vaughanCanonicalTensorLength y k) Q *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
          y N u v k l := by
  let A := vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
    (vaughanCanonicalDyadicBlock N u k)
  let L := vaughanCanonicalTensorLength y k
  let T : ℕ → ℤ → ℂ := fun d t =>
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d
      (vaughanCanonicalDyadicBlock N v l) t
  have hA : 0 ≤ A := by
    dsimp [A, vaughanBilinearCoeffEnergy]
    positivity
  have hrow : ∀ d ∈ vaughanCanonicalDyadicBlock N u k,
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (T d) 0 L q χ) ≤
        (((Nat.log2 L + 1 : ℕ) : ℝ) ^ 2) *
          primitiveLargeSieveConstant L Q *
          ∑ t ∈ Finset.Icc (1 : ℤ) L, ‖T d t‖ ^ 2 := by
    intro d hd
    simpa using weighted_primitive_prefix_maximal (T d) 0 L Q hQ
  calc
    _ = A * ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            primitiveCharacterPrefixMaxSquare (T d) 0 L q χ) := by
      simp only [vaughanCanonicalTensorPrefixMaxEnergy]
      dsimp [A, L, T]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
      ring
    _ ≤ A * ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        ((((Nat.log2 L + 1 : ℕ) : ℝ) ^ 2) *
          primitiveLargeSieveConstant L Q *
          ∑ t ∈ Finset.Icc (1 : ℤ) L, ‖T d t‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Finset.sum_le_sum fun d hd => hrow d hd
    _ = _ := by
      dsimp [A, L, T]
      unfold vaughanCanonicalShortTensorEnergy
      simp_rw [Finset.mul_sum]
      ring

/-- Möbius energy on level `k` is at most `2^k`. -/
theorem vaughanMoebiusCoeffEnergy_canonical_le_pow (N u k : ℕ) :
    vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
        (vaughanCanonicalDyadicBlock N u k) ≤ ((2 ^ k : ℕ) : ℝ) :=
  (vaughanMoebiusCoeffEnergy_le_card _).trans (by
    exact_mod_cast card_vaughanCanonicalDyadicBlock_le_pow N u k)

/-- Exact natural cancellation of shell size against short length.  This also
covers `k=0`, where `2^0=1` and the quotient is exactly `y`. -/
theorem pow_mul_vaughanCanonicalTensorLength_le (y k : ℕ) :
    2 ^ k * vaughanCanonicalTensorLength y k ≤ y := by
  simpa [vaughanCanonicalTensorLength] using Nat.mul_div_le y (2 ^ k)

/-- Expanded scale audit: after paying the `2^k` outer energy, the length part
is at most `y`, while the modulus part is exactly charged by `2^k Q^2`. -/
theorem pow_mul_primitiveLargeSieveConstant_short_le
    (y k Q : ℕ) :
    ((2 ^ k : ℕ) : ℝ) *
        primitiveLargeSieveConstant (vaughanCanonicalTensorLength y k) Q ≤
      (y : ℝ) + ((2 ^ k : ℕ) : ℝ) *
        ((2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2) := by
  unfold primitiveLargeSieveConstant
  have hlen : ((2 ^ k * vaughanCanonicalTensorLength y k : ℕ) : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast pow_mul_vaughanCanonicalTensorLength_le y k
  push_cast at hlen ⊢
  nlinarith

/-- Primitive row-prefix bound with the shell energy already paid and the
short large-sieve constant expanded.  This is the formal cancellation
`2^k * (y / 2^k) ≤ y`; only the modulus term retains `2^k`. -/
theorem weighted_primitive_vaughanCanonicalTensorPrefix_explicit
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
          vaughanCanonicalTensorPrefixMaxEnergy b y N u v k l q χ) ≤
      (((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
      ((y : ℝ) + ((2 ^ k : ℕ) : ℝ) *
        ((2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2)) *
      vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
        y N u v k l := by
  refine (weighted_primitive_vaughanCanonicalTensorPrefix
    b y N u v k l Q hQ).trans ?_
  let L2 : ℝ := (((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2)
  let E : ℝ := vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
    y N u v k l
  have hL2 : 0 ≤ L2 := by dsimp [L2]; positivity
  have hE : 0 ≤ E := by
    dsimp [E, vaughanCanonicalShortTensorEnergy]
    positivity
  have hA := vaughanMoebiusCoeffEnergy_canonical_le_pow N u k
  have hC := pow_mul_primitiveLargeSieveConstant_short_le y k Q
  calc
    vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) * L2 *
        primitiveLargeSieveConstant (vaughanCanonicalTensorLength y k) Q * E
      ≤ ((2 ^ k : ℕ) : ℝ) * L2 *
        primitiveLargeSieveConstant (vaughanCanonicalTensorLength y k) Q * E := by
          gcongr
          · unfold primitiveLargeSieveConstant
            positivity
    _ = L2 * (((2 ^ k : ℕ) : ℝ) *
        primitiveLargeSieveConstant (vaughanCanonicalTensorLength y k) Q) * E := by ring
    _ ≤ L2 * ((y : ℝ) + ((2 ^ k : ℕ) : ℝ) *
        ((2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2)) * E := by gcongr
    _ = _ := by rfl

/-- Generic linear-harmonic transport of a nonnegative primitive family over a
conductor window.  This is the conductor aggregation used by the short Type-II
row-prefix bound. -/
theorem imprimitive_conductor_window_family_le_linear_typeII
    (F : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hF : ∀ d ψ, 0 ≤ F d ψ) (Q C : ℕ) (hC : 0 < C) :
    (∑ d ∈ Finset.Icc C (2 * C),
      imprimitiveConductorWeight Q d * ∑ ψ : PrimitiveCharacter d, F d ψ) ≤
      ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
        ∑ d ∈ Finset.Icc 1 (2 * C),
          ((d : ℝ) / (d.totient : ℝ)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc C (2 * C),
        (((d : ℝ) / (d.totient : ℝ)) * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 0 < d := hC.trans_le (Finset.mem_Icc.mp hdmem).1
      have hdiv : Q / d ≤ Q / C :=
        Nat.div_le_div_left (Finset.mem_Icc.mp hdmem).1 hC
      have hharm : conductorHarmonicFactor (Q / d) ≤
          conductorHarmonicFactor (Q / C) := by
        unfold conductorHarmonicFactor
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right hdiv
        · intro e he hnot
          positivity
      have hsum : 0 ≤ ∑ ψ : PrimitiveCharacter d, F d ψ :=
        Finset.sum_nonneg fun ψ _ => hF d ψ
      apply mul_le_mul_of_nonneg_right _ hsum
      refine (imprimitiveConductorWeight_le_linear_harmonic Q d hd).trans ?_
      have hh0 := conductorHarmonicFactor_nonneg (Q / d)
      gcongr
    _ ≤ ∑ d ∈ Finset.Icc 1 (2 * C),
        (((d : ℝ) / (d.totient : ℝ)) * ((Q / C : ℕ) : ℝ) *
          conductorHarmonicFactor (Q / C)) * ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨hC.trans_le (Finset.mem_Icc.mp hd).1,
          (Finset.mem_Icc.mp hd).2⟩
      · intro d hd hnot
        have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
        have hφ0 : (0 : ℝ) < d.totient := by
          exact_mod_cast Nat.totient_pos.mpr hd0
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (div_nonneg (by positivity) hφ0.le) (by positivity))
            (conductorHarmonicFactor_nonneg _))
          (Finset.sum_nonneg fun ψ _ => hF d ψ)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- Conductor-window summary for the complete row-prefix maximum.  Combining
this with `weighted_primitive_vaughanCanonicalTensorPrefix` at cap `2*C` and
`pow_mul_primitiveLargeSieveConstant_short_le` yields the advertised shell
charge `O(y) + O(2^k C^2)`, times only the displayed prefix/conductor logs and
the short tensor energy. -/
theorem imprimitive_conductor_window_vaughanCanonicalTensorPrefix
    (b : ℕ → ℂ) (y N Q C u v k l : ℕ) (hC : 0 < C) :
    (∑ d ∈ Finset.Icc C (2 * C), imprimitiveConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d,
        vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
          vaughanCanonicalTensorPrefixMaxEnergy b y N u v k l d ψ) ≤
      ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
      (vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
        (((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant (vaughanCanonicalTensorLength y k) (2 * C) *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
          y N u v k l) := by
  let F : (d : ℕ) → PrimitiveCharacter d → ℝ := fun d ψ =>
    vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
      (vaughanCanonicalDyadicBlock N u k) *
      vaughanCanonicalTensorPrefixMaxEnergy b y N u v k l d ψ
  have hF : ∀ d ψ, 0 ≤ F d ψ := by
    intro d ψ
    apply mul_nonneg
    · dsimp [vaughanBilinearCoeffEnergy]
      positivity
    · unfold vaughanCanonicalTensorPrefixMaxEnergy
      exact Finset.sum_nonneg fun d _ =>
        primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ _
  refine (imprimitive_conductor_window_family_le_linear_typeII F hF Q C hC).trans ?_
  apply mul_le_mul_of_nonneg_left
  · simpa [F] using weighted_primitive_vaughanCanonicalTensorPrefix
      b y N u v k l (2 * C) (Nat.mul_pos (by decide) hC)
  · exact mul_nonneg (by positivity) (conductorHarmonicFactor_nonneg _)

/-- Fully expanded conductor-window summary.  The complete `t`-prefix maximum
is retained, conductor multiplicity is linear-harmonic, and the primitive
charge is `y + 2^k * O(C^2)` rather than `2^k * (y + O(C^2))`. -/
theorem imprimitive_conductor_window_vaughanCanonicalTensorPrefix_explicit
    (b : ℕ → ℂ) (y N Q C u v k l : ℕ) (hC : 0 < C) :
    (∑ d ∈ Finset.Icc C (2 * C), imprimitiveConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d,
        vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
          vaughanCanonicalTensorPrefixMaxEnergy b y N u v k l d ψ) ≤
      ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
      (((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2 *
        ((y : ℝ) + ((2 ^ k : ℕ) : ℝ) *
          ((2 * (Nat.ceil
            (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
            ((2 * C : ℕ) : ℝ) ^ 2)) *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
          y N u v k l) := by
  let F : (d : ℕ) → PrimitiveCharacter d → ℝ := fun d ψ =>
    vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
      (vaughanCanonicalDyadicBlock N u k) *
      vaughanCanonicalTensorPrefixMaxEnergy b y N u v k l d ψ
  have hF : ∀ d ψ, 0 ≤ F d ψ := by
    intro d ψ
    dsimp [F]
    apply mul_nonneg
    · unfold vaughanBilinearCoeffEnergy
      positivity
    · unfold vaughanCanonicalTensorPrefixMaxEnergy
      exact Finset.sum_nonneg fun d _ =>
        primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ _
  refine (imprimitive_conductor_window_family_le_linear_typeII F hF Q C hC).trans ?_
  apply mul_le_mul_of_nonneg_left
  · simpa [F] using
      weighted_primitive_vaughanCanonicalTensorPrefix_explicit
        b y N u v k l (2 * C) (Nat.mul_pos (by decide) hC)
  · exact mul_nonneg (by positivity) (conductorHarmonicFactor_nonneg _)

end

end AnalyticNumberTheory.LargeSieve
