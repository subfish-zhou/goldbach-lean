

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIBilinearShell

/-!
 # Actual hyperbolic decomposition of the direct Vaughan Type-II mean

The prefix cutoff in Vaughan Type II is the genuine hyperbola `d * e * m ≤ y`.
This file does not replace it by a rowwise square estimate.  Instead it first
partitions the two divisor variables into the canonical dyadic rectangles, then
takes the finite maximum of each resulting collected `(d,t=e*m)` prefix over the
original prefix endpoint `y`.  Rectangles whose lower dyadic corner lies above
`N` are proved identically zero and removed before the direct mean is summed.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Canonical rectangles which can meet the hyperbola `d*e*m ≤ N` (`m ≥ 1`). -/
def vaughanTypeIIActiveCanonicalRectangles (N u v : ℕ) : Finset (ℕ × ℕ) :=
  (vaughanCanonicalDyadicRectangles N u v).filter
    (fun kl => 2 ^ kl.1 * 2 ^ kl.2 ≤ N)

@[simp] theorem mem_vaughanTypeIIActiveCanonicalRectangles {N u v : ℕ}
    {kl : ℕ × ℕ} :
    kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v ↔
      kl ∈ vaughanCanonicalDyadicRectangles N u v ∧
        2 ^ kl.1 * 2 ^ kl.2 ≤ N := by
  simp [vaughanTypeIIActiveCanonicalRectangles]

/-- The actual maximal collected-prefix square on one canonical rectangle.
The tensor collection is the exact substitution `t=e*m`; the maximum is still
over the original hyperbolic endpoint, so no rectangular majorization has been
inserted. -/
def vaughanCanonicalCollectedPrefixMaxSquare
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (N + 1)).image (fun y =>
      ‖vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
        y N u v k l q χ‖ ^ 2)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

lemma vaughanCanonicalCollectedPrefixMaxSquare_nonneg
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q) :
    0 ≤ vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ := by
  unfold vaughanCanonicalCollectedPrefixMaxSquare
  exact (sq_nonneg ‖(0 : ℂ)‖).trans (Finset.le_max' _ _
    (Finset.mem_image.mpr ⟨0, by simp,
      by simp [vaughanTypeIICanonicalBilinearBlock]⟩))

/-- AP-normalized direct mean of one actual canonical collected-prefix shell. -/
def apNormalizedVaughanActualCollectedShellMean
    (N Q u v k l : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)

lemma apNormalizedVaughanActualCollectedShellMean_nonneg
    (N Q u v k l : ℕ) :
    0 ≤ apNormalizedVaughanActualCollectedShellMean N Q u v k l := by
  unfold apNormalizedVaughanActualCollectedShellMean
  positivity

/-- On a hyperbolic row prefix `t ≤ y/d`, the tensor coefficient may be
formed at the ambient endpoint `N`: the condition `d*t ≤ y ≤ N` makes the
physical `m`-cutoff identical.  This is the elementary two-dimensional prefix
identity which prevents us from confusing a hyperbola with a rectangle. -/
private lemma vaughanBilinearTensorCoeff_eq_ambient_of_mem_divPrefix
    (b : ℕ → ℂ) {y N d : ℕ} (ES : Finset ℕ) (t : ℤ)
    (hyN : y ≤ N) (hd : 0 < d)
    (hES : ∀ e ∈ ES, 0 < e)
    (ht : t ∈ Finset.Icc (1 : ℤ) (y / d : ℕ)) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d ES t =
      vaughanBilinearTensorCoeff vaughanMangoldtCoeff b N d ES t := by
  have ht0 : 0 ≤ t := (Finset.mem_Icc.mp ht).1.trans' (by norm_num)
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
  have htt : t.toNat ≤ y / d := by
    exact_mod_cast htcast.trans_le (Finset.mem_Icc.mp ht).2
  have hdt : d * t.toNat ≤ y := by
    simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp htt
  have hfiber : vaughanTensorFiber y d ES t = vaughanTensorFiber N d ES t := by
    ext e
    simp only [vaughanTensorFiber, Finset.mem_filter]
    constructor
    · rintro ⟨he, m, hm, hmt⟩
      refine ⟨he, m, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, ?_⟩, hmt⟩
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hd (hES e he))).2
      exact ((Nat.le_div_iff_mul_le (Nat.mul_pos hd (hES e he))).1
        (Finset.mem_Icc.mp hm).2).trans hyN
    · rintro ⟨he, m, hm, hmt⟩
      refine ⟨he, m, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, ?_⟩, hmt⟩
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hd (hES e he))).2
      have hemt : e * m = t.toNat := by
        exact_mod_cast hmt.trans htcast.symm
      calc
        m * (d * e) = d * (e * m) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        _ = d * t.toNat := by rw [hemt]
        _ ≤ y := hdt
  rw [vaughanBilinearTensorCoeff_eq_fiber b y d ES t hES,
    vaughanBilinearTensorCoeff_eq_fiber b N d ES t hES, hfiber]

/-- Exact row-prefix form of a hyperbolic shell.  The endpoint in the `d`-th
row is `y/d`; in particular this statement does not identify the hyperbola
with a common rectangular prefix. -/
private lemma vaughanTypeIICanonicalBilinearBlock_eq_ambient_rowPrefixes
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q)
    (hyN : y ≤ N) :
    vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ =
      ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) *
          ∑ t ∈ Finset.Icc (1 : ℤ) (y / d : ℕ),
            vaughanBilinearTensorCoeff vaughanMangoldtCoeff b N d
              (vaughanCanonicalDyadicBlock N v l) t *
                χ.1 (t : ZMod q) := by
  change vaughanBilinearBlockOn vaughanMoebiusCoeff vaughanMangoldtCoeff b y
      (vaughanCanonicalDyadicBlock N u k)
      (vaughanCanonicalDyadicBlock N v l) q χ = _
  rw [vaughanBilinearBlockOn_eq_tensor]
  · apply Finset.sum_congr rfl
    intro d hdmem
    congr 1
    have hd : 0 < d := (mem_vaughanCanonicalDyadicBlock.mp hdmem).1
    have hdiv : y / d ≤ y := Nat.div_le_self y d
    have hsub : Finset.Icc (1 : ℤ) (y / d : ℕ) ⊆ Finset.Icc (1 : ℤ) y :=
      Finset.Icc_subset_Icc_right (by exact_mod_cast hdiv)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [vaughanBilinearTensorCoeff_eq_ambient_of_mem_divPrefix
        b (vaughanCanonicalDyadicBlock N v l) t hyN hd
        (fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1) ht]
    · intro t hty htshort
      have hfempty : vaughanTensorFiber y d
          (vaughanCanonicalDyadicBlock N v l) t = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hf
        have hsupport := vaughanTensorFiber_support y d
          (vaughanCanonicalDyadicBlock N v l) t hd hty hf
        have ht0 : 0 ≤ t := le_trans (by norm_num) (Finset.mem_Icc.mp hty).1
        have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
        have hnotle : ¬ t.toNat ≤ y / d := by
          intro hle
          apply htshort
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hty).1, by
            rw [← htcast]
            exact_mod_cast hle⟩
        exact hnotle ((Nat.le_div_iff_mul_le hd).2 (by
          simpa [mul_comm] using hsupport))
      rw [vaughanBilinearTensorCoeff_eq_fiber b y d
        (vaughanCanonicalDyadicBlock N v l) t
        (fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1), hfempty]
      simp
  · intro d hd
    exact (mem_vaughanCanonicalDyadicBlock.mp hd).1
  · intro e he
    exact (mem_vaughanCanonicalDyadicBlock.mp he).1

private lemma primitiveCharacterPrefixSquare_typeII_eq_full
    (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixSquare
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) 0 y q χ =
      ‖vaughanTypeIIFullPrefix (fun _ => 1) y u v q χ‖ ^ 2 := by
  unfold primitiveCharacterPrefixSquare vaughanTypeIIFullPrefix
  simp only [zero_add]
  have hsum := sum_Ioc_nat_eq_sum_Icc_int 0 0 y
    (fun z => vaughanTypeIICoeff vaughanUnitIntegerCoeff u v z *
      χ.1 (z : ZMod q))
  have hset : Finset.Ioc 0 y = Finset.Icc 1 y := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hsum
  have hsum' :
      (∑ x ∈ Finset.Icc (1 : ℤ) y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v x * χ.1 (x : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v (n : ℤ) *
          χ.1 ((n : ℤ) : ZMod q) := by
    simpa using hsum.symm
  rw [hsum']
  have hterms :
      (∑ n ∈ Finset.Icc 1 y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v (n : ℤ) *
          χ.1 ((n : ℤ) : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 y,
        1 * χ.1 (n : ZMod q) * vaughanTypeIIFullAt n u v := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [vaughanTypeIICoeff, vaughanUnitIntegerCoeff, one_mul,
      Int.toNat_natCast, vaughanTypeII, vaughanTypeIIFullAt_eq_vaughanThird,
      Int.cast_natCast]
    ring
  rw [hterms]

/-- A genuine hyperbolic shell is controlled by rowwise tensor prefix maxima.
Each row keeps its own endpoint `y/d`; Cauchy is applied only after the exact
row-prefix identity above. -/
theorem vaughanTypeIICanonicalBilinearBlock_norm_sq_le_rowPrefixMax
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q)
    (hyN : y ≤ N) :
    ‖vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ‖ ^ 2 ≤
      vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
        vaughanCanonicalTensorPrefixMaxEnergy b N N u v k l q χ := by
  rw [vaughanTypeIICanonicalBilinearBlock_eq_ambient_rowPrefixes
    b y N u v k l q χ hyN]
  let DS := vaughanCanonicalDyadicBlock N u k
  let T : ℕ → ℤ → ℂ := fun d t =>
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b N d
      (vaughanCanonicalDyadicBlock N v l) t
  let I : ℕ → ℂ := fun d =>
    ∑ t ∈ Finset.Icc (1 : ℤ) (y / d : ℕ), T d t * χ.1 (t : ZMod q)
  have hnorm := norm_sum_le DS
    (fun d => (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) * I d)
  have hsq :
      ‖∑ d ∈ DS, (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) * I d‖ ^ 2 ≤
        (∑ d ∈ DS, ‖vaughanMoebiusCoeff d * χ.1 (d : ZMod q)‖ * ‖I d‖) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa [norm_mul] using hnorm
  refine hsq.trans ((Finset.sum_mul_sq_le_sq_mul_sq DS
    (fun d => ‖vaughanMoebiusCoeff d * χ.1 (d : ZMod q)‖)
    (fun d => ‖I d‖)).trans ?_)
  apply mul_le_mul
  · unfold vaughanBilinearCoeffEnergy
    apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, mul_pow]
    have hχsq : ‖χ.1 (d : ZMod q)‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (DirichletCharacter.norm_le_one χ.1 (d : ZMod q)) 2
    simpa using mul_le_mul_of_nonneg_left hχsq
      (sq_nonneg ‖vaughanMoebiusCoeff d‖)
  · unfold vaughanCanonicalTensorPrefixMaxEnergy
    apply Finset.sum_le_sum
    intro d hdmem
    have hpow : 2 ^ k ≤ d := (vaughanCanonicalDyadicBlock_pow_bounds hdmem).1
    have hmul : 2 ^ k * (y / d) ≤ y :=
      (Nat.mul_le_mul_right (y / d) hpow).trans (Nat.mul_div_le y d)
    have hlen : y / d ≤ vaughanCanonicalTensorLength N k := by
      unfold vaughanCanonicalTensorLength
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).2
      simpa [mul_comm] using hmul.trans hyN
    simpa [I, T, primitiveCharacterPrefixSquare] using
      primitiveCharacterPrefixSquare_le_max (T d) 0 hlen χ
  · positivity
  · unfold vaughanBilinearCoeffEnergy
    positivity

/-- Maximizing the preceding pointwise estimate over the actual endpoint keeps
one fixed ambient tensor on the right. -/
theorem vaughanCanonicalCollectedPrefixMaxSquare_le_rowPrefixMax
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ ≤
      vaughanBilinearCoeffEnergy vaughanMoebiusCoeff
          (vaughanCanonicalDyadicBlock N u k) *
        vaughanCanonicalTensorPrefixMaxEnergy
          (fun _ => 1) N N u v k l q χ := by
  unfold vaughanCanonicalCollectedPrefixMaxSquare
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  exact vaughanTypeIICanonicalBilinearBlock_norm_sq_le_rowPrefixMax
    (fun _ => 1) y N u v k l q χ (by simpa [Finset.mem_range] using hy)

/-- A canonical rectangle above the lower-corner hyperbola contributes zero to
every prefix `y ≤ N`. -/
lemma vaughanTypeIICanonicalBilinearBlock_eq_zero_of_inactive
    {y N u v k l q : ℕ} (χ : PrimitiveCharacter q) (hyN : y ≤ N)
    (hinactive : N < 2 ^ k * 2 ^ l) :
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
      y N u v k l q χ = 0 := by
  unfold vaughanTypeIICanonicalBilinearBlock
  apply Finset.sum_eq_zero
  intro d hd
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro e he
  apply mul_eq_zero_of_right
  have hde : N < d * e := by
    have hdk : 2 ^ k ≤ d := (vaughanCanonicalDyadicBlock_pow_bounds hd).1
    have hel : 2 ^ l ≤ e := (vaughanCanonicalDyadicBlock_pow_bounds he).1
    exact hinactive.trans_le (Nat.mul_le_mul hdk hel)
  have hdiv : y / (d * e) = 0 := Nat.div_eq_of_lt (hyN.trans_lt hde)
  simp [hdiv]

/-- Exact finite reindexing: at every prefix endpoint the full Type-II form is
the sum of precisely the active canonical hyperbolic shells. -/
theorem vaughanTypeIIFullPrefix_eq_sum_active_canonical
    (y N u v q : ℕ) (χ : PrimitiveCharacter q) (hyN : y ≤ N) :
    vaughanTypeIIFullPrefix (fun _ => 1) y u v q χ =
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
          y N u v kl.1 kl.2 q χ := by
  rw [vaughanTypeIIFullPrefix_eq_sum_canonical_bilinear
    (fun _ => 1) y N u v q χ hyN]
  rw [← Finset.sum_product (f := fun kl : ℕ × ℕ =>
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1) y N u v kl.1 kl.2 q χ)]
  rw [vaughanTypeIIActiveCanonicalRectangles, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro kl hkl
  by_cases hactive : 2 ^ kl.1 * 2 ^ kl.2 ≤ N
  · simp [hactive]
  · rw [if_neg hactive]
    exact vaughanTypeIICanonicalBilinearBlock_eq_zero_of_inactive χ hyN
      (Nat.lt_of_not_ge hactive)

/-- The maximal full Type-II prefix of one primitive character is dominated by
the sum of the actual canonical collected-prefix shell maxima. -/
theorem primitivePrefixAmplitude_vaughanTypeII_le_active_collected_shells
    (N u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
          N u v kl.1 kl.2 q χ) := by
  let R : ℝ := ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
    Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
      N u v kl.1 kl.2 q χ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  change Real.sqrt (primitiveCharacterPrefixMaxSquare
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) 0 N q χ) ≤ R
  rw [← Real.sqrt_sq hR]
  apply Real.sqrt_le_sqrt
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  rw [primitiveCharacterPrefixSquare_typeII_eq_full]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [vaughanTypeIIFullPrefix_eq_sum_active_canonical y N u v q χ hyN]
  calc
    ‖∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
          y N u v kl.1 kl.2 q χ‖
      ≤ ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
          ‖vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
            y N u v kl.1 kl.2 q χ‖ := norm_sum_le _ _
    _ ≤ R := by
      dsimp [R]
      apply Finset.sum_le_sum
      intro kl hkl
      rw [← Real.sqrt_sq (norm_nonneg _)]
      apply Real.sqrt_le_sqrt
      unfold vaughanCanonicalCollectedPrefixMaxSquare
      apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨y, by simp [hyN], rfl⟩

/-- Shell coverage after summing primitive characters and moduli.  This is the
exact direct-mean decomposition; no rowwise `N²` estimate is used. -/
theorem apNormalizedVaughanTypeIIMean_le_active_collected_shells
    (N Q u v : ℕ) :
    apNormalizedVaughanTypeIIMean N Q u v ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        apNormalizedVaughanActualCollectedShellMean
          N Q u v kl.1 kl.2 := by
  unfold apNormalizedVaughanTypeIIMean apNormalizedPrimitiveMean
    apNormalizedVaughanActualCollectedShellMean
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ : PrimitiveCharacter q,
          ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
            Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
              N u v kl.1 kl.2 q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun χ _ =>
          primitivePrefixAmplitude_vaughanTypeII_le_active_collected_shells
            N u v q χ
      · positivity
    _ = _ := by
      calc
        _ = ∑ q ∈ Finset.Icc 1 Q,
            ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
              ((q.totient : ℝ)⁻¹) *
                ∑ χ : PrimitiveCharacter q,
                  Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
                    N u v kl.1 kl.2 q χ) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [Finset.sum_comm, Finset.mul_sum]
        _ = _ := by rw [Finset.sum_comm]

/-- The active family is finite with the same canonical `log² N` budget. -/
theorem card_vaughanTypeIIActiveCanonicalRectangles_le (N u v : ℕ) :
    (vaughanTypeIIActiveCanonicalRectangles N u v).card ≤
      (Nat.log 2 N + 1) ^ 2 := by
  exact (Finset.card_filter_le _ _).trans
    (card_vaughanCanonicalDyadicRectangles_le N u v)

/-- Canonical inhabitance of the existing AP-normalized Type-II input once the
physical bilinear estimate has been supplied for each *actual hyperbolic*
shell.  In particular the required scale retains the term `Q*N/sqrt(u+1)` and
never passes through a rowwise `N²` majorant. -/
theorem vaughanDirectAPNormalizedTypeIIInput_of_actual_collected_shells
    (N Q u v : ℕ) (logPay : ℝ)
    (hshell : ∀ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
      apNormalizedVaughanActualCollectedShellMean N Q u v kl.1 kl.2 ≤
        logPay * ((N : ℝ) +
          (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ))) :
    VaughanDirectAPNormalizedTypeIIInput N Q u v
      ((vaughanTypeIIActiveCanonicalRectangles N u v).card : ℝ) logPay := by
  exact vaughanDirectAPNormalizedTypeIIInput_of_bilinear_shells
    (vaughanTypeIIActiveCanonicalRectangles N u v)
    (fun kl => apNormalizedVaughanActualCollectedShellMean
      N Q u v kl.1 kl.2) N Q u v logPay
    (apNormalizedVaughanTypeIIMean_le_active_collected_shells N Q u v)
    hshell

end

end AnalyticNumberTheory.LargeSieve
