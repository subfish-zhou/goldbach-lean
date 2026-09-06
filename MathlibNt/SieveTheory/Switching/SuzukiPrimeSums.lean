import MathlibNt.SieveTheory.Switching.VaryingPrimeSieve

/-!
# Dimension-one prime sums and finite Abel identities

Local product bounds, finite prime nodes, and Abel summation establish the
dimension-one prime-sum comparison of Suzuki's Lemma 8.6.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- The standard dimension-one local-product condition
`V(z₁)/V(z₂) ≤ (log z₂/log z₁)(1 + K/log z₁)`.  The product is restricted to
the actual finite sieving primes, so omitted Goldbach primes dividing `N` are
handled without changing the abstract hypothesis. -/
def HasDimensionOneLocalProductBound (S : BoundingSieve) (K : ℝ) : Prop :=
  ∀ z₁ z₂ : ℝ, 2 ≤ z₁ → z₁ ≤ z₂ →
    ∏ p ∈ S.prodPrimes.primeFactors.filter
        (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂),
        (1 - S.nu p)⁻¹ ≤
      Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)

/-- The finite-support version of Suzuki's ratio `V(w) / V(z)`, restricted to
the actual sieving primes. -/
noncomputable def suzukiLocalRatio
    (S : BoundingSieve) (w z : ℝ) : ℝ :=
  ∏ p ∈ S.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
    (1 - S.nu p)⁻¹

/-- For nonnegative real cutoffs, the supported primes in `[w,z)` are exactly
those in the natural half-open interval `[⌈w⌉₊,⌈z⌉₊)`. -/
theorem suzuki_supportedPrimes_real_eq_inter_Ico
    (S : BoundingSieve) {w z : ℝ} (_hw : 0 ≤ w) (_hz : 0 ≤ z) :
    S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z) =
      S.prodPrimes.primeFactors ∩ Finset.Ico ⌈w⌉₊ ⌈z⌉₊ := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_Ico]
  rw [Nat.ceil_le, Nat.lt_ceil]

/-- Filter-form corollary of the exact real/natural carrier bridge. -/
theorem suzuki_supportedPrimes_real_eq_ceil
    (S : BoundingSieve) {w z : ℝ} (hw : 0 ≤ w) (hz : 0 ≤ z) :
    S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z) =
      S.prodPrimes.primeFactors.filter
        (fun p : ℕ => ⌈w⌉₊ ≤ p ∧ p < ⌈z⌉₊) := by
  rw [suzuki_supportedPrimes_real_eq_inter_Ico S hw hz]
  ext p
  simp

/-- Suzuki's dimension-one local-product error `E(w,z)`. -/
noncomputable def suzukiDimensionOneError
    (S : BoundingSieve) (w z : ℝ) : ℝ :=
  suzukiLocalRatio S w z - Real.log z / Real.log w

/-- Suzuki equation `(8.1)` in dimension one follows directly from the generic
local-product condition; no prime-specific PNT or Mertens theorem is used. -/
theorem suzukiDimensionOneError_le
    {S : BoundingSieve} {K w z : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hw : 2 ≤ w) (hwz : w ≤ z) :
    suzukiDimensionOneError S w z ≤
      K / Real.log w * (Real.log z / Real.log w) := by
  have h := hlocal w z hw hwz
  unfold suzukiDimensionOneError suzukiLocalRatio
  calc
    (∏ p ∈ S.prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - S.nu p)⁻¹) - Real.log z / Real.log w ≤
      (Real.log z / Real.log w * (1 + K / Real.log w)) -
        Real.log z / Real.log w := sub_le_sub_right h _
    _ = K / Real.log w * (Real.log z / Real.log w) := by ring

/-- The exact finite prime sum on the left side of Suzuki Lemma 8.6 in sieve
dimension one. The suffix product is the finite ratio `V(p)/V(z)`. -/
noncomputable def suzukiLemmaEightSixPrimeSum
    (S : BoundingSieve) (D w z : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∑ p ∈ S.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
    S.nu p *
      (∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z), (1 - S.nu q)⁻¹) *
      H (Real.log D / Real.log p)

/-- Supported primes below the natural cutoff `z`. -/
noncomputable def suzukiSupportedBelow (S : BoundingSieve) (z : ℕ) : Finset ℕ :=
  S.prodPrimes.primeFactors.filter (fun q => q < z)

/-- The finite suffix Euler ratio over supported primes `n ≤ q < z`. -/
noncomputable def suzukiSuffixRatio (S : BoundingSieve) (z n : ℕ) : ℝ :=
  ∏ q ∈ (suzukiSupportedBelow S z).filter (fun q => n ≤ q), (1 - S.nu q)⁻¹

/-- Exact bridge from real cutoffs to natural ceiling cutoffs. In particular,
an integral right endpoint retains the strict condition `p < z`. -/
theorem suzukiLocalRatio_eq_suzukiSuffixRatio_ceil
    (S : BoundingSieve) {w z : ℝ} (hw : 0 ≤ w) (hz : 0 ≤ z) :
    suzukiLocalRatio S w z = suzukiSuffixRatio S ⌈z⌉₊ ⌈w⌉₊ := by
  unfold suzukiLocalRatio suzukiSuffixRatio suzukiSupportedBelow
  rw [suzuki_supportedPrimes_real_eq_ceil S hw hz]
  congr 1
  ext p
  simp [and_assoc, and_left_comm, and_comm]

/-- At a natural right endpoint the ceiling bridge has no off-by-one shift. -/
theorem suzukiLocalRatio_nat_right
    (S : BoundingSieve) {w : ℝ} (z : ℕ) (hw : 0 ≤ w) :
    suzukiLocalRatio S w (z : ℝ) = suzukiSuffixRatio S z ⌈w⌉₊ := by
  simpa using suzukiLocalRatio_eq_suzukiSuffixRatio_ceil S hw
    (Nat.cast_nonneg z : (0 : ℝ) ≤ z)

lemma suzukiSuffixRatio_step_of_mem (S : BoundingSieve) (z n : ℕ)
    (hn : n ∈ suzukiSupportedBelow S z) :
    suzukiSuffixRatio S z n = (1 - S.nu n)⁻¹ * suzukiSuffixRatio S z (n + 1) := by
  have hnot : n ∉ (suzukiSupportedBelow S z).filter (fun q => n + 1 ≤ q) := by simp
  unfold suzukiSuffixRatio
  rw [show (suzukiSupportedBelow S z).filter (fun q => n ≤ q) =
      insert n ((suzukiSupportedBelow S z).filter (fun q => n + 1 ≤ q)) by
    ext q
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hq, hnq⟩
      by_cases hqn : q = n
      · exact Or.inl hqn
      · exact Or.inr ⟨hq, by omega⟩
    · rintro (rfl | ⟨hq, hnq⟩)
      · exact ⟨hn, le_rfl⟩
      · exact ⟨hq, by omega⟩]
  rw [prod_insert hnot]

lemma suzukiSuffixRatio_step_of_not_mem (S : BoundingSieve) (z n : ℕ)
    (hn : n ∉ suzukiSupportedBelow S z) :
    suzukiSuffixRatio S z n = suzukiSuffixRatio S z (n + 1) := by
  unfold suzukiSuffixRatio
  congr 1
  ext q
  simp only [mem_filter]
  constructor
  · rintro ⟨hq, hnq⟩
    exact ⟨hq, by
      have hne : q ≠ n := fun h => hn (h ▸ hq)
      omega⟩
  · rintro ⟨hq, hnq⟩
    exact ⟨hq, by omega⟩

/-- Exact difference of consecutive finite suffix Euler products.
The factor is `R n`, not `R (n+1)`. -/
theorem suzukiSuffixRatio_sub_succ (S : BoundingSieve) (z n : ℕ) :
    suzukiSuffixRatio S z n - suzukiSuffixRatio S z (n + 1) =
      if n ∈ suzukiSupportedBelow S z then S.nu n * suzukiSuffixRatio S z n else 0 := by
  by_cases hn : n ∈ suzukiSupportedBelow S z
  · rw [if_pos hn, suzukiSuffixRatio_step_of_mem S z n hn]
    have hnfac : n ∈ S.prodPrimes.primeFactors := (mem_filter.mp hn).1
    have hnprime : n.Prime := Nat.prime_of_mem_primeFactors hnfac
    have hndvd : n ∣ S.prodPrimes := Nat.dvd_of_mem_primeFactors hnfac
    have hne : 1 - S.nu n ≠ 0 := by
      have := S.nu_lt_one_of_prime n hnprime hndvd
      linarith
    field_simp
    ring
  · rw [if_neg hn, suzukiSuffixRatio_step_of_not_mem S z n hn]
    ring

/-- Natural-cutoff version of Suzuki's finite prime sum. -/
noncomputable def suzukiPrimeSumNat
    (S : BoundingSieve) (w z : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p => w ≤ p),
    S.nu p * suzukiSuffixRatio S z p * F p

/-- The Suzuki prime sum is exactly the finite Abel difference sum; unsupported
indices contribute zero by the suffix-product difference identity. -/
theorem suzukiPrimeSumNat_eq_abelSum (S : BoundingSieve) (w z : ℕ)
    (F : ℕ → ℝ) :
    suzukiPrimeSumNat S w z F =
      ∑ n ∈ Ico w z,
        (suzukiSuffixRatio S z n - suzukiSuffixRatio S z (n + 1)) * F n := by
  rw [suzukiPrimeSumNat]
  apply sum_subset_zero_on_sdiff
  · intro n hn
    simp only [mem_filter] at hn
    exact mem_Ico.mpr ⟨hn.2, (mem_filter.mp hn.1).2⟩
  · intro n hn
    have hnI : n ∈ Ico w z := (mem_sdiff.mp hn).1
    have hnP : n ∉ (suzukiSupportedBelow S z).filter (fun p => w ≤ p) :=
      (mem_sdiff.mp hn).2
    rw [suzukiSuffixRatio_sub_succ, if_neg]
    · simp
    · intro hs
      apply hnP
      exact mem_filter.mpr ⟨hs, (mem_Ico.mp hnI).1⟩
  · intro n hn
    have hs : n ∈ suzukiSupportedBelow S z := (mem_filter.mp hn).1
    rw [suzukiSuffixRatio_sub_succ, if_pos hs]

/-- Finite Abel (summation-by-parts) identity on a natural interval.  This
boundary convention remains valid for the empty interval `w = z`. -/
theorem finiteAbelIdentity (R F : ℕ → ℝ) (w z : ℕ) (hwz : w ≤ z) :
    (∑ n ∈ Ico w z, (R n - R (n + 1)) * F n) =
      R w * F w - R z * F z +
        ∑ n ∈ Ico (w + 1) (z + 1), R n * (F n - F (n - 1)) := by
  induction z, hwz using Nat.le_induction with
  | base => simp
  | succ z hwz ih =>
      rw [sum_Ico_succ_top hwz]
      rw [sum_Ico_succ_top (Nat.succ_le_succ hwz)]
      rw [ih]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring

/-- Suzuki's supported-prime sum in Abel boundary-plus-increment form. -/
theorem suzukiPrimeSumNat_abelIdentity (S : BoundingSieve) (w z : ℕ)
    (hwz : w ≤ z) (F : ℕ → ℝ) :
    suzukiPrimeSumNat S w z F =
      suzukiSuffixRatio S z w * F w - suzukiSuffixRatio S z z * F z +
        ∑ n ∈ Ico (w + 1) (z + 1),
          suzukiSuffixRatio S z n * (F n - F (n - 1)) := by
  rw [suzukiPrimeSumNat_eq_abelSum S w z F]
  exact finiteAbelIdentity (suzukiSuffixRatio S z) F w z hwz


/-- At integral cutoffs, the current Suzuki prime-sum interface is exactly the
natural supported-prime sum used by the finite Abel identity. -/
theorem suzukiLemmaEightSixPrimeSum_eq_nat
    (S : BoundingSieve) (D : ℝ) (w z : ℕ) (H : ℝ → ℝ) :
    suzukiLemmaEightSixPrimeSum S D (w : ℝ) (z : ℝ) H =
      suzukiPrimeSumNat S w z (fun p => H (Real.log D / Real.log p)) := by
  unfold suzukiLemmaEightSixPrimeSum suzukiPrimeSumNat suzukiSuffixRatio
    suzukiSupportedBelow
  apply sum_congr
  · ext p
    simp [and_assoc, and_left_comm, and_comm]
  · intro p hp
    congr 2
    apply prod_congr
    · ext q
      simp [and_assoc, and_left_comm, and_comm]
    · intro q hq
      rfl

/-- Thus the exact Suzuki prime sum at integral cutoffs has the Abel
boundary-plus-increment expansion. -/
theorem suzukiLemmaEightSixPrimeSum_abelIdentity
    (S : BoundingSieve) (D : ℝ) (w z : ℕ) (hwz : w ≤ z) (H : ℝ → ℝ) :
    suzukiLemmaEightSixPrimeSum S D (w : ℝ) (z : ℝ) H =
      suzukiSuffixRatio S z w * H (Real.log D / Real.log w) -
        suzukiSuffixRatio S z z * H (Real.log D / Real.log z) +
        ∑ n ∈ Ico (w + 1) (z + 1), suzukiSuffixRatio S z n *
          (H (Real.log D / Real.log n) -
            H (Real.log D / Real.log ((n - 1 : ℕ) : ℝ))) := by
  rw [suzukiLemmaEightSixPrimeSum_eq_nat]
  exact suzukiPrimeSumNat_abelIdentity S w z hwz
    (fun p => H (Real.log D / Real.log p))

/-- The generic local-product input specializes exactly to the natural suffix
ratio used by `suzukiFiniteAbel`. -/
theorem suzukiSuffixRatio_le
    {S : BoundingSieve} {K : ℝ} (hlocal : HasDimensionOneLocalProductBound S K)
    {x z : ℕ} (hx : 2 ≤ x) (hxz : x ≤ z) :
    suzukiSuffixRatio S z x ≤
      Real.log z / Real.log x * (1 + K / Real.log x) := by
  have h := hlocal (x : ℝ) (z : ℝ) (by exact_mod_cast hx) (by exact_mod_cast hxz)
  change suzukiLocalRatio S x z ≤ _ at h
  simpa only [suzukiLocalRatio_nat_right S z (Nat.cast_nonneg x), Nat.ceil_natCast]
    using h

/-- Equation (8.1) at natural endpoints, obtained without PNT or Mertens. -/
theorem suzukiNatDimensionOneError_le
    {S : BoundingSieve} {K : ℝ} (hlocal : HasDimensionOneLocalProductBound S K)
    {x z : ℕ} (hx : 2 ≤ x) (hxz : x ≤ z) :
    suzukiSuffixRatio S z x - Real.log z / Real.log x ≤
      K / Real.log x * (Real.log z / Real.log x) := by
  have h := suzukiSuffixRatio_le hlocal hx hxz
  calc
    suzukiSuffixRatio S z x - Real.log z / Real.log x ≤
        Real.log z / Real.log x * (1 + K / Real.log x) -
          Real.log z / Real.log x := sub_le_sub_right h _
    _ = K / Real.log x * (Real.log z / Real.log x) := by ring

/-- The source hypothesis that `t ↦ H(t)t` is antitone, together with
nonnegativity and positive coordinates, implies that `H` itself is antitone. -/
theorem antitoneOn_of_mul_id_antitoneOn
    {H : ℝ → ℝ} {s σ : ℝ} (hs : 0 < s)
    (hH0 : ∀ t ∈ Set.Icc s σ, 0 ≤ H t)
    (hmono : AntitoneOn (fun t => H t * t) (Set.Icc s σ)) :
    AntitoneOn H (Set.Icc s σ) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := hs.trans_le hx.1
  have hprod : H y * y ≤ H x * x := hmono hx hy hxy
  have hscale : H y * x ≤ H y * y :=
    mul_le_mul_of_nonneg_left hxy (hH0 y hy)
  have : H y * x ≤ H x * x := hscale.trans hprod
  nlinarith

/-- The supported primes in `[w,z)`, sorted and cast to real nodes. -/
noncomputable def suzukiSupportedPrimeNodes
    (S : BoundingSieve) (w z : ℝ) : List ℝ :=
  ((S.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).sort (· ≤ ·)).map
    (fun p : ℕ => (p : ℝ))

/-- The complete real node list: the genuine lower endpoint, all supported
prime jumps, and the genuine upper endpoint. -/
noncomputable def suzukiFiniteNodes
    (S : BoundingSieve) (w z : ℝ) : List ℝ :=
  w :: suzukiSupportedPrimeNodes S w z ++ [z]

/-- The local prime/jump atom attached to two consecutive real nodes. -/
noncomputable def suzukiFiniteNodeAtom
    (S : BoundingSieve) (z x y : ℝ) : ℝ :=
  suzukiLocalRatio S x z - suzukiLocalRatio S y z

/-- Suzuki's source prime atom `ω(p) V(p) / V(z)`. -/
noncomputable def suzukiFinitePrimeAtom
    (S : BoundingSieve) (z : ℝ) (p : ℕ) : ℝ :=
  S.nu p * suzukiLocalRatio S p z

/-- If `y` is the node immediately after a supported prime `p`, the successive
node atom is exactly Suzuki's source prime atom.  The hypotheses only express
that no supported prime lies strictly between these two nodes. -/
theorem suzukiFiniteNodeAtom_eq_primeAtom
    (S : BoundingSieve) (z y : ℝ) (p : ℕ)
    (hp : p ∈ S.prodPrimes.primeFactors) (hpz : (p : ℝ) < z)
    (hpy : (p : ℝ) < y)
    (hgap : ∀ q ∈ S.prodPrimes.primeFactors,
      p < q → (q : ℝ) < y → False) :
    suzukiFiniteNodeAtom S z p y = suzukiFinitePrimeAtom S z p := by
  classical
  let tail := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => y ≤ (q : ℝ) ∧ (q : ℝ) < z)
  have hfilter :
      S.prodPrimes.primeFactors.filter
          (fun q : ℕ => (p : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < z) =
        insert p tail := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert, tail]
    constructor
    · rintro ⟨hq, hpq, hqz⟩
      by_cases hqp : q = p
      · exact Or.inl hqp
      · right
        refine ⟨hq, ?_, hqz⟩
        have hpqNat : p ≤ q := by exact_mod_cast hpq
        have hpq' : p < q := lt_of_le_of_ne hpqNat (Ne.symm hqp)
        by_contra hqy
        exact hgap q hq hpq' (lt_of_not_ge hqy)
    · rintro (rfl | ⟨hq, hyq, hqz⟩)
      · exact ⟨hp, le_rfl, hpz⟩
      · exact ⟨hq, hpy.le.trans hyq, hqz⟩
  have hpnot : p ∉ tail := by
    simp [tail, not_le.mpr hpy]
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
  have hden : 1 - S.nu p ≠ 0 :=
    ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hprime hpdiv))
  rw [suzukiFiniteNodeAtom, suzukiFinitePrimeAtom,
    suzukiLocalRatio, suzukiLocalRatio, hfilter,
    Finset.prod_insert hpnot]
  field_simp
  ring

@[simp] theorem suzukiLocalRatio_self
    (S : BoundingSieve) (z : ℝ) :
    suzukiLocalRatio S z z = 1 := by
  have hempty :
      S.prodPrimes.primeFactors.filter
        (fun p : ℕ => z ≤ (p : ℝ) ∧ (p : ℝ) < z) = ∅ := by
    ext p
    simp
  rw [suzukiLocalRatio, hempty]
  simp

/-- Suzuki finite-node Abel summation.  Unlike a natural-interval version, its
boundary terms are exactly `g w` and `g z`.  The summands on the left are the
successive local-ratio (prime-jump) atoms. -/
theorem suzukiFiniteNodeAbel
    (S : BoundingSieve) (w z : ℝ) (g : ℝ → ℝ) :
    LinearSieve.finiteNodeAtomSum (fun x => suzukiLocalRatio S x z) g
        (suzukiFiniteNodes S w z) =
      suzukiLocalRatio S w z * g w - g z +
        LinearSieve.finiteNodeVariationSum (fun x => suzukiLocalRatio S x z) g
          (suzukiFiniteNodes S w z) := by
  rw [suzukiFiniteNodes, LinearSieve.finiteNodeAbel]
  simp only [suzukiLocalRatio_self, one_mul]

/-- The Suzuki node-atom sum over consecutive pairs of a list. -/
noncomputable def suzukiFiniteNodeAtomSum
    (S : BoundingSieve) (z : ℝ) (g : ℝ → ℝ) : List ℝ → ℝ
  | x :: y :: xs =>
      suzukiFiniteNodeAtom S z x y * g x +
        suzukiFiniteNodeAtomSum S z g (y :: xs)
  | _ => 0

lemma suzukiFiniteNodeAtomSum_eq
    (S : BoundingSieve) (z : ℝ) (g : ℝ → ℝ) (nodes : List ℝ) :
    suzukiFiniteNodeAtomSum S z g nodes =
      LinearSieve.finiteNodeAtomSum (fun x => suzukiLocalRatio S x z) g nodes := by
  induction nodes with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          rw [suzukiFiniteNodeAtomSum, LinearSieve.finiteNodeAtomSum, suzukiFiniteNodeAtom,
            ih]

/-- The same specialization with the left side visibly written using Suzuki's
successive local-ratio atoms. -/
theorem suzukiFiniteNodeAbel_atoms
    (S : BoundingSieve) (w z : ℝ) (g : ℝ → ℝ) :
    suzukiFiniteNodeAtomSum S z g (suzukiFiniteNodes S w z) =
      suzukiLocalRatio S w z * g w - g z +
        LinearSieve.finiteNodeVariationSum (fun x => suzukiLocalRatio S x z) g
          (suzukiFiniteNodes S w z) := by
  rw [suzukiFiniteNodeAtomSum_eq]
  exact suzukiFiniteNodeAbel S w z g

private theorem suzukiFiniteNodeAtomSum_tail_eq_primeSum
    (S : BoundingSieve) (z : ℝ) (g : ℝ → ℝ) (x : ℕ)
    (hx : x ∈ S.prodPrimes.primeFactors) (hxz : (x : ℝ) < z) :
    ∀ s : Finset ℕ,
      s = S.prodPrimes.primeFactors.filter
        (fun q : ℕ => (x : ℝ) < (q : ℝ) ∧ (q : ℝ) < z) →
      suzukiFiniteNodeAtomSum S z g
          ((x : ℝ) :: (s.sort (· ≤ ·)).map (fun q : ℕ => (q : ℝ)) ++ [z]) =
        suzukiFinitePrimeAtom S z x * g x +
          ∑ q ∈ s, suzukiFinitePrimeAtom S z q * g q := by
  classical
  intro s
  revert x
  refine Finset.strongInductionOn s ?_
  intro s ih x hx hxz hs
  by_cases hne : s.Nonempty
  · let y : ℕ := s.min' hne
    have hy_mem : y ∈ s := Finset.min'_mem s hne
    have hy_data : y ∈ S.prodPrimes.primeFactors ∧
        (x : ℝ) < (y : ℝ) ∧ (y : ℝ) < z := by
      rw [hs] at hy_mem
      exact Finset.mem_filter.mp hy_mem
    have hxy_nat : x < y := by exact_mod_cast hy_data.2.1
    have hy_min : ∀ q ∈ s, y ≤ q := by
      intro q hq
      exact Finset.min'_le s q hq
    have hy_not : y ∉ s.erase y := by simp
    have hcons : Finset.cons y (s.erase y) hy_not = s := by
      ext q
      simp [hy_mem]
    have hsort : s.sort (· ≤ ·) = y :: (s.erase y).sort (· ≤ ·) := by
      calc
        s.sort (· ≤ ·) = (Finset.cons y (s.erase y) hy_not).sort (· ≤ ·) :=
          congrArg (fun t : Finset ℕ => t.sort (· ≤ ·)) hcons.symm
        _ = y :: (s.erase y).sort (· ≤ ·) :=
          Finset.sort_cons (· ≤ ·)
            (fun q hq => hy_min q (Finset.mem_of_mem_erase hq)) hy_not
    have hedge : suzukiFiniteNodeAtom S z x y = suzukiFinitePrimeAtom S z x := by
      apply suzukiFiniteNodeAtom_eq_primeAtom S z y x hx hxz hy_data.2.1
      intro q hq hxq hqy
      have hqs : q ∈ s := by
        rw [hs]
        exact Finset.mem_filter.mpr ⟨hq, by exact_mod_cast hxq, lt_trans (by exact_mod_cast hqy) hy_data.2.2⟩
      have hyq : y ≤ q := hy_min q hqs
      exact (not_lt_of_ge (by exact_mod_cast hyq : (y : ℝ) ≤ (q : ℝ))) hqy
    have herase : s.erase y = S.prodPrimes.primeFactors.filter
        (fun q : ℕ => (y : ℝ) < (q : ℝ) ∧ (q : ℝ) < z) := by
      ext q
      constructor
      · intro hq
        have hqs : q ∈ s := Finset.mem_of_mem_erase hq
        have hqne : q ≠ y := (Finset.mem_erase.mp hq).1
        have hyq : y < q := lt_of_le_of_ne (hy_min q hqs) (Ne.symm hqne)
        rw [hs] at hqs
        have hqd := Finset.mem_filter.mp hqs
        exact Finset.mem_filter.mpr ⟨hqd.1, by exact_mod_cast hyq, hqd.2.2⟩
      · intro hq
        have hqd := Finset.mem_filter.mp hq
        have hxy : (x : ℝ) < (y : ℝ) := hy_data.2.1
        have hqs : q ∈ s := by
          rw [hs]
          exact Finset.mem_filter.mpr ⟨hqd.1, lt_trans hxy hqd.2.1, hqd.2.2⟩
        exact Finset.mem_erase.mpr ⟨by
          intro hqy
          subst q
          exact (lt_irrefl (y : ℝ)) hqd.2.1, hqs⟩
    have herase_ssubset : s.erase y ⊂ s := Finset.erase_ssubset hy_mem
    have htail := ih (s.erase y) herase_ssubset y
      hy_data.1 hy_data.2.2 herase
    have htail' : suzukiFiniteNodeAtomSum S z g
          (↑y :: (((s.erase y).sort (· ≤ ·)).map
            (fun q : ℕ => (q : ℝ)) ++ [z])) =
        suzukiFinitePrimeAtom S z y * g y +
          ∑ q ∈ s.erase y, suzukiFinitePrimeAtom S z q * g q := by
      simpa only [List.cons_append] using htail
    rw [hsort]
    simp only [List.map_cons, List.cons_append]
    rw [suzukiFiniteNodeAtomSum, hedge, htail']
    congr 1
    rw [add_comm, Finset.sum_erase_add s
      (fun q => suzukiFinitePrimeAtom S z q * g q) hy_mem]
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hgap : ∀ q ∈ S.prodPrimes.primeFactors,
        x < q → (q : ℝ) < z → False := by
      intro q hq hxq hqz
      have hqs : q ∈ s := by
        rw [hs]
        exact Finset.mem_filter.mpr ⟨hq, by exact_mod_cast hxq, hqz⟩
      simp [hs_empty] at hqs
    have hedge := suzukiFiniteNodeAtom_eq_primeAtom S z z x hx hxz hxz hgap
    simp [hs_empty, suzukiFiniteNodeAtomSum, hedge]

/-- The real finite-node atom sum, with genuine endpoints `w,z`, is exactly
Suzuki's finite prime sum for `g x = H (log D / log x)`. -/
theorem suzukiFiniteNodeAtomSum_eq_lemmaEightSixPrimeSum
    (S : BoundingSieve) (D w z : ℝ) (H : ℝ → ℝ) (_hwz : w ≤ z) :
    suzukiFiniteNodeAtomSum S z (fun x => H (Real.log D / Real.log x))
        (suzukiFiniteNodes S w z) =
      suzukiLemmaEightSixPrimeSum S D w z H := by
  classical
  let carrier : Finset ℕ := S.prodPrimes.primeFactors.filter
    (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  let g : ℝ → ℝ := fun x => H (Real.log D / Real.log x)
  change suzukiFiniteNodeAtomSum S z g
      (w :: (carrier.sort (· ≤ ·)).map (fun p : ℕ => (p : ℝ)) ++ [z]) = _
  by_cases hne : carrier.Nonempty
  · let p : ℕ := carrier.min' hne
    have hp_mem : p ∈ carrier := Finset.min'_mem carrier hne
    have hp_data : p ∈ S.prodPrimes.primeFactors ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
      dsimp [carrier] at hp_mem
      exact Finset.mem_filter.mp hp_mem
    have hp_min : ∀ q ∈ carrier, p ≤ q := by
      intro q hq
      exact Finset.min'_le carrier q hq
    have hp_not : p ∉ carrier.erase p := by simp
    have hcons : Finset.cons p (carrier.erase p) hp_not = carrier := by
      ext q
      simp [hp_mem]
    have hsort : carrier.sort (· ≤ ·) = p :: (carrier.erase p).sort (· ≤ ·) := by
      calc
        carrier.sort (· ≤ ·) =
            (Finset.cons p (carrier.erase p) hp_not).sort (· ≤ ·) :=
          congrArg (fun t : Finset ℕ => t.sort (· ≤ ·)) hcons.symm
        _ = p :: (carrier.erase p).sort (· ≤ ·) :=
          Finset.sort_cons (· ≤ ·)
            (fun q hq => hp_min q (Finset.mem_of_mem_erase hq)) hp_not
    have hfilter :
        S.prodPrimes.primeFactors.filter
            (fun q : ℕ => w ≤ (q : ℝ) ∧ (q : ℝ) < z) =
          S.prodPrimes.primeFactors.filter
            (fun q : ℕ => (p : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < z) := by
      ext q
      constructor
      · intro hq
        have hqc : q ∈ carrier := by simpa [carrier] using hq
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
          by exact_mod_cast hp_min q hqc, (Finset.mem_filter.mp hq).2.2⟩
      · intro hq
        have hqd := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hqd.1, hp_data.2.1.trans hqd.2.1, hqd.2.2⟩
    have hfirst : suzukiFiniteNodeAtom S z w p = 0 := by
      unfold suzukiFiniteNodeAtom suzukiLocalRatio
      rw [hfilter]
      ring
    have herase : carrier.erase p = S.prodPrimes.primeFactors.filter
        (fun q : ℕ => (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < z) := by
      ext q
      constructor
      · intro hq
        have hqc : q ∈ carrier := Finset.mem_of_mem_erase hq
        have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
        have hpq : p < q := lt_of_le_of_ne (hp_min q hqc) (Ne.symm hqne)
        have hqd : q ∈ S.prodPrimes.primeFactors ∧ w ≤ (q : ℝ) ∧ (q : ℝ) < z := by
          simpa [carrier] using hqc
        exact Finset.mem_filter.mpr ⟨hqd.1, by exact_mod_cast hpq, hqd.2.2⟩
      · intro hq
        have hqd := Finset.mem_filter.mp hq
        have hqc : q ∈ carrier := by
          dsimp [carrier]
          exact Finset.mem_filter.mpr ⟨hqd.1,
            hp_data.2.1.trans (le_of_lt hqd.2.1), hqd.2.2⟩
        exact Finset.mem_erase.mpr ⟨by
          intro hqp
          subst q
          exact (lt_irrefl (p : ℝ)) hqd.2.1, hqc⟩
    have htail := suzukiFiniteNodeAtomSum_tail_eq_primeSum S z g p
      hp_data.1 hp_data.2.2 (carrier.erase p) herase
    rw [hsort]
    simp only [List.map_cons, List.cons_append]
    rw [suzukiFiniteNodeAtomSum, hfirst, zero_mul, zero_add]
    have htail' : suzukiFiniteNodeAtomSum S z g
          (↑p :: (((carrier.erase p).sort (· ≤ ·)).map
            (fun q : ℕ => (q : ℝ)) ++ [z])) =
        suzukiFinitePrimeAtom S z p * g p +
          ∑ q ∈ carrier.erase p, suzukiFinitePrimeAtom S z q * g q := by
      simpa only [List.cons_append] using htail
    rw [htail']
    rw [add_comm, Finset.sum_erase_add carrier
      (fun q => suzukiFinitePrimeAtom S z q * g q) hp_mem]
    unfold suzukiFinitePrimeAtom suzukiLocalRatio
    unfold suzukiLemmaEightSixPrimeSum
    simp [carrier, g, Nat.cast_le, mul_assoc]
  · have hc_empty : carrier = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hw_filter : S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z) = ∅ := by
      simpa [carrier] using hc_empty
    have hz_filter : S.prodPrimes.primeFactors.filter
        (fun p : ℕ => z ≤ (p : ℝ) ∧ (p : ℝ) < z) = ∅ := by
      ext p
      simp
    have hedge : suzukiFiniteNodeAtom S z w z = 0 := by
      unfold suzukiFiniteNodeAtom suzukiLocalRatio
      rw [hw_filter, hz_filter]
      simp
    simp [hc_empty, carrier, suzukiFiniteNodeAtomSum, hedge, suzukiLemmaEightSixPrimeSum]

/-- The Suzuki transform is increasing in the underlying variable. -/
theorem transformedH_monotoneOn
    {D w z s σ : ℝ} {H : ℝ → ℝ}
    (hD : 1 < D) (hw : 1 < w) (_hwz : w ≤ z)
    (hcoord : ∀ x ∈ Set.Icc w z, Real.log D / Real.log x ∈ Set.Icc s σ)
    (hH : ∀ t ∈ Set.Icc s σ, 0 ≤ H t)
    (hHt : AntitoneOn (fun t => H t * t) (Set.Icc s σ)) :
    MonotoneOn (fun x => H (Real.log D / Real.log x)) (Set.Icc w z) := by
  intro x hx y hy hxy
  have hx1 : 1 < x := lt_of_lt_of_le hw hx.1
  have hy1 : 1 < y := lt_of_lt_of_le hx1 hxy
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn (by exact hx1.trans' zero_lt_one)
      (by exact hy1.trans' zero_lt_one) hxy
  let tx := Real.log D / Real.log x
  let ty := Real.log D / Real.log y
  have htx : tx ∈ Set.Icc s σ := hcoord x hx
  have hty : ty ∈ Set.Icc s σ := hcoord y hy
  have htypos : 0 < ty := div_pos hlogD hlogy
  have htyle : ty ≤ tx := by
    dsimp [tx, ty]
    apply (div_le_div_iff₀ hlogy hlogx).2
    nlinarith
  have hprod : H tx * tx ≤ H ty * ty := hHt hty htx htyle
  have hHx : 0 ≤ H tx := hH tx htx
  have haux : H tx * ty ≤ H tx * tx := mul_le_mul_of_nonneg_left htyle hHx
  have := le_trans haux hprod
  nlinarith

theorem suzukiSupportedPrimeNodes_pairwise
    (S : BoundingSieve) (w z : ℝ) :
    (suzukiSupportedPrimeNodes S w z).Pairwise (· ≤ ·) := by
  classical
  rw [suzukiSupportedPrimeNodes, List.pairwise_map]
  apply (Multiset.pairwise_sort _ (· ≤ ·)).imp
  intro a b hab
  exact_mod_cast hab

theorem mem_suzukiSupportedPrimeNodes
    {S : BoundingSieve} {w z x : ℝ}
    (hx : x ∈ suzukiSupportedPrimeNodes S w z) : w ≤ x ∧ x < z := by
  classical
  rw [suzukiSupportedPrimeNodes, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [Finset.mem_sort, Finset.mem_filter] at hp
  exact hp.2

theorem suzukiFiniteNodes_pairwise
    (S : BoundingSieve) {w z : ℝ} (hwz : w ≤ z) :
    (suzukiFiniteNodes S w z).Pairwise (· ≤ ·) := by
  classical
  unfold suzukiFiniteNodes
  apply List.pairwise_cons.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (List.mem_append.mp hx) with hx | hx
    · exact (mem_suzukiSupportedPrimeNodes hx).1
    · have : x = z := by simpa using hx
      subst x
      exact hwz
  apply List.pairwise_append.mpr
  refine ⟨suzukiSupportedPrimeNodes_pairwise S w z, ?_, ?_⟩
  · simp
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact (mem_suzukiSupportedPrimeNodes hx).2.le

theorem mem_suzukiFiniteNodes_Icc
    {S : BoundingSieve} {w z x : ℝ} (hwz : w ≤ z)
    (hx : x ∈ suzukiFiniteNodes S w z) : x ∈ Set.Icc w z := by
  unfold suzukiFiniteNodes at hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with hxpre | hxz
  · rcases hxpre with rfl | hx
    · exact ⟨le_rfl, hwz⟩
    · exact ⟨(mem_suzukiSupportedPrimeNodes hx).1,
        (mem_suzukiSupportedPrimeNodes hx).2.le⟩
  · have : x = z := by simpa using hxz
    subst x
    exact ⟨hwz, le_rfl⟩

theorem pairwise_imp_of_mem {α : Type*} {R T : α → α → Prop} {l : List α}
    (hR : l.Pairwise R)
    (hT : ∀ x ∈ l, ∀ y ∈ l, R x y → T x y) : l.Pairwise T := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.pairwise_cons] at hR ⊢
      refine ⟨?_, ih hR.2 ?_⟩
      · intro b hb
        exact hT a (by simp) b (by simp [hb]) (hR.1 b hb)
      · intro x hx y hy hxy
        exact hT x (by simp [hx]) y (by simp [hy]) hxy

/-- Every forward finite-node variation increment `g y - g x` is nonnegative.
In particular this holds for each adjacent pair used by the Abel variation sum. -/
theorem transformedH_suzukiFiniteNodes_increments_nonneg
    {D w z s σ : ℝ} {H : ℝ → ℝ}
    (S : BoundingSieve)
    (hD : 1 < D) (hw : 1 < w) (hwz : w ≤ z)
    (hcoord : ∀ x ∈ Set.Icc w z, Real.log D / Real.log x ∈ Set.Icc s σ)
    (hH : ∀ t ∈ Set.Icc s σ, 0 ≤ H t)
    (hHt : AntitoneOn (fun t => H t * t) (Set.Icc s σ)) :
    (suzukiFiniteNodes S w z).Pairwise
      (fun x y => 0 ≤ H (Real.log D / Real.log y) -
        H (Real.log D / Real.log x)) := by
  apply pairwise_imp_of_mem (suzukiFiniteNodes_pairwise S hwz)
  intro x hx y hy hxy
  apply sub_nonneg.mpr
  apply transformedH_monotoneOn hD hw hwz hcoord hH hHt
  · exact mem_suzukiFiniteNodes_Icc hwz hx
  · exact mem_suzukiFiniteNodes_Icc hwz hy
  · exact hxy

@[simp] theorem suzukiDimensionOneError_self
    (S : BoundingSieve) {z : ℝ} (hz : Real.log z ≠ 0) :
    suzukiDimensionOneError S z z = 0 := by
  simp [suzukiDimensionOneError, suzukiLocalRatio_self, hz]

/-- Exact finite-node decomposition of Suzuki's local Euler ratio into its
`log z / log x` main ratio and the dimension-one error. -/
theorem suzukiFiniteNodeAbel_mainRatio_errorVariation
    (S : BoundingSieve) (w z : ℝ) (g : ℝ → ℝ) :
    LinearSieve.finiteNodeAtomSum (fun x => suzukiLocalRatio S x z) g
        (suzukiFiniteNodes S w z) =
      LinearSieve.finiteNodeMainRatioSum z g (suzukiFiniteNodes S w z) +
        (suzukiDimensionOneError S w z * g w -
          suzukiDimensionOneError S z z * g z +
          LinearSieve.finiteNodeVariationSum
            (fun x => suzukiDimensionOneError S x z) g
            (suzukiFiniteNodes S w z)) := by
  unfold suzukiFiniteNodes
  apply LinearSieve.finiteNodeAbel_mainRatio_errorVariation
  intro x
  simp only [suzukiDimensionOneError, LinearSieve.finiteNodeLogRatio]
  ring

/-- Source-faithful exact main/error split for the Suzuki Lemma 8.6 prime sum.
The upper endpoint error vanishes when `log z ≠ 0`. -/
theorem suzukiLemmaEightSixPrimeSum_mainErrorSplit
    (S : BoundingSieve) (D w z : ℝ) (H : ℝ → ℝ)
    (hwz : w ≤ z) (hz : Real.log z ≠ 0) :
    suzukiLemmaEightSixPrimeSum S D w z H =
      LinearSieve.finiteNodeMainRatioSum z
        (fun x => H (Real.log D / Real.log x)) (suzukiFiniteNodes S w z) +
      (suzukiDimensionOneError S w z * H (Real.log D / Real.log w) +
        LinearSieve.finiteNodeVariationSum
          (fun x => suzukiDimensionOneError S x z)
          (fun x => H (Real.log D / Real.log x))
          (suzukiFiniteNodes S w z)) := by
  rw [← suzukiFiniteNodeAtomSum_eq_lemmaEightSixPrimeSum S D w z H hwz,
    suzukiFiniteNodeAtomSum_eq,
    suzukiFiniteNodeAbel_mainRatio_errorVariation,
    suzukiDimensionOneError_self S hz, zero_mul, sub_zero]

/-- The finite error expression in Suzuki Lemma 8.6. -/
noncomputable def suzukiFiniteErrorVariation
    (S : BoundingSieve) (D w z : ℝ) (H : ℝ → ℝ) : ℝ :=
  let E := fun x => suzukiDimensionOneError S x z
  let g := fun x => H (Real.log D / Real.log x)
  E w * g w + LinearSieve.finiteNodeVariationSum E g (suzukiFiniteNodes S w z)


/-- Suzuki Lemma 8.6's finite error-variation estimate.  Only the one-sided
local-product error bound is used; no absolute-value estimate for `E` is needed. -/
theorem suzukiFiniteErrorVariation_le
    {S : BoundingSieve} {D w z s σ K : ℝ} {H : ℝ → ℝ}
    (hD : 1 < D) (hw2 : 2 ≤ w) (hwz : w ≤ z)
    (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ))
    (hH0 : ∀ t ∈ Set.Icc s σ, 0 ≤ H t)
    (hHt : AntitoneOn (fun t => H t * t) (Set.Icc s σ))
    (hK : 0 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiFiniteErrorVariation S D w z H ≤ 2 * K * H s / Real.log w := by
  let t : ℝ → ℝ := fun x => Real.log D / Real.log x
  let g : ℝ → ℝ := fun x => H (t x)
  let E : ℝ → ℝ := fun x => suzukiDimensionOneError S x z
  have hσ : 0 < σ := hs.trans_le hsσ
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hw1 : 1 < w := lt_of_lt_of_le (by norm_num) hw2
  have hz1 : 1 < z := hw1.trans_le hwz
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hend : t w = σ ∧ t z = s := ⟨
    SuzukiPowerCoordinates.coordinate_at_lower hD (hs.trans_le hsσ) hw,
    SuzukiPowerCoordinates.coordinate_at_upper hD hs hz⟩
  have htw : t w = σ := hend.1
  have htz : t z = s := hend.2
  have hcoord : ∀ x ∈ Set.Icc w z, t x ∈ Set.Icc s σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hs hsσ hz hw hx
  have hnodes : ∀ x ∈ suzukiFiniteNodes S w z, x ∈ Set.Icc w z := by
    intro x hx
    exact mem_suzukiFiniteNodes_Icc hwz hx
  have hpair : (suzukiFiniteNodes S w z).Pairwise (· ≤ ·) :=
    suzukiFiniteNodes_pairwise S hwz
  let C : ℝ := K / (s * Real.log D)
  let B : ℝ → ℝ := fun x => C * (t x)^2
  have hC0 : 0 ≤ C := div_nonneg hK (mul_nonneg hs.le hlogD.le)
  have hlogz_formula : Real.log z = Real.log D / s := by
    have hD0 : 0 < D := lt_trans (by norm_num) hD
    rw [hz, Real.log_rpow hD0]
    ring
  have hEmono : (suzukiFiniteNodes S w z).Pairwise
      (fun x y => E y * (g y - g x) ≤ B y * (g y - g x)) := by
    apply pairwise_imp_of_mem hpair
    intro x hx y hy hxy
    have hxi := hnodes x hx
    have hyi := hnodes y hy
    have hy1 : 1 < y := hw1.trans_le hyi.1
    have hinc : 0 ≤ g y - g x :=
      sub_nonneg.mpr
        (transformedH_monotoneOn hD hw1 hwz hcoord hH0 hHt hxi hyi hxy)
    have hy2 : 2 ≤ y := hw2.trans hyi.1
    have hEraw := suzukiDimensionOneError_le hlocal hy2 hyi.2
    have hE : E y ≤ B y := by
      dsimp [E, B, C, t]
      calc
        suzukiDimensionOneError S y z ≤ K / Real.log y * (Real.log z / Real.log y) := hEraw
        _ = K / (s * Real.log D) * (Real.log D / Real.log y)^2 := by
          rw [hlogz_formula]
          field_simp
    exact mul_le_mul_of_nonneg_right hE hinc
  have hvarmono := LinearSieve.finiteNodeVariationSum_mono_of_pairwise E B g
    (suzukiFiniteNodes S w z) hEmono
  have hquadEdge : (suzukiFiniteNodes S w z).Pairwise
      (fun x y => ((t x)^2 - (t y)^2) * g x ≤
        (2 * (s * H s)) * (t x - t y)) := by
    apply pairwise_imp_of_mem hpair
    intro x hx y hy hxy
    have hxi := hnodes x hx
    have hyi := hnodes y hy
    have htxi := hcoord x hxi
    have htyi := hcoord y hyi
    have hx1 : 1 < x := hw1.trans_le hxi.1
    have hy1 : 1 < y := hw1.trans_le hyi.1
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    have hy0 : 0 < y := lt_trans zero_lt_one hy1
    have hlogxy : Real.log x ≤ Real.log y :=
      Real.strictMonoOn_log.monotoneOn hx0 hy0 hxy
    have htytx : t y ≤ t x := by
      dsimp [t]
      apply (div_le_div_iff₀ (Real.log_pos hy1) (Real.log_pos hx1)).2
      nlinarith
    have htx0 : 0 ≤ t x := hs.le.trans htxi.1
    have hdiff0 : 0 ≤ t x - t y := sub_nonneg.mpr htytx
    have hHx0 : 0 ≤ H (t x) := hH0 _ htxi
    have hprod_xs : t x * H (t x) ≤ s * H s := by
      have hp := hHt (show s ∈ Set.Icc s σ from ⟨le_rfl, hsσ⟩) htxi htxi.1
      nlinarith
    have hsum : (t x + t y) * H (t x) ≤ 2 * (s * H s) := by
      have hsum0 : t x + t y ≤ 2 * t x := by linarith
      have hh := mul_le_mul_of_nonneg_right hsum0 hHx0
      nlinarith
    calc
      ((t x)^2 - (t y)^2) * g x =
          (t x - t y) * ((t x + t y) * H (t x)) := by
        dsimp [g]
        ring
      _ ≤ (t x - t y) * (2 * (s * H s)) :=
        mul_le_mul_of_nonneg_left hsum hdiff0
      _ = (2 * (s * H s)) * (t x - t y) := by ring
  have hatom := LinearSieve.finiteNodeAtomSum_le_telescope (fun x => (t x)^2) g t
    (2 * (s * H s)) w z (suzukiSupportedPrimeNodes S w z) hquadEdge
  rw [htw, htz] at hatom
  have hquad : σ^2 * H σ + LinearSieve.finiteNodeVariationSum (fun x => (t x)^2) g
      (suzukiFiniteNodes S w z) ≤ 2 * s * σ * H s := by
    have habel := LinearSieve.finiteNodeAbel (fun x => (t x)^2) g w z
      (suzukiSupportedPrimeNodes S w z)
    change LinearSieve.finiteNodeAtomSum (fun x => (t x)^2) g (suzukiFiniteNodes S w z) =
      (t w)^2 * g w - (t z)^2 * g z +
        LinearSieve.finiteNodeVariationSum (fun x => (t x)^2) g
          (suzukiFiniteNodes S w z) at habel
    simp only [htw, htz] at habel
    have hgw : g w = H σ := by dsimp [g]; rw [htw]
    have hgz : g z = H s := by dsimp [g]; rw [htz]
    rw [hgw, hgz] at habel
    calc
      σ^2 * H σ + LinearSieve.finiteNodeVariationSum (fun x => (t x)^2) g
          (suzukiFiniteNodes S w z) =
          LinearSieve.finiteNodeAtomSum (fun x => (t x)^2) g (suzukiFiniteNodes S w z) +
            s^2 * H s := by
          rw [habel]
          ring
      _ ≤ (2 * (s * H s)) * (σ - s) + s^2 * H s := by
        simpa [suzukiFiniteNodes] using add_le_add_right hatom (s^2 * H s)
      _ ≤ 2 * s * σ * H s := by
        have hHs0 : 0 ≤ H s := hH0 s ⟨le_rfl, hsσ⟩
        nlinarith [mul_nonneg hs.le hHs0]
  have hHs0 : 0 ≤ H s := hH0 s ⟨le_rfl, hsσ⟩
  have hHw0 : 0 ≤ g w := by
    dsimp [g]
    rw [htw]
    exact hH0 σ ⟨hsσ, le_rfl⟩
  have hEw_raw := suzukiDimensionOneError_le hlocal hw2 hwz
  have hEw : E w ≤ B w := by
    dsimp [E, B, C, t]
    calc
      suzukiDimensionOneError S w z ≤ K / Real.log w * (Real.log z / Real.log w) := hEw_raw
      _ = K / (s * Real.log D) * (Real.log D / Real.log w)^2 := by
        rw [hlogz_formula]
        field_simp
  have hboundary : E w * g w ≤ B w * g w :=
    mul_le_mul_of_nonneg_right hEw hHw0
  unfold suzukiFiniteErrorVariation
  dsimp only
  change E w * g w + LinearSieve.finiteNodeVariationSum E g (suzukiFiniteNodes S w z) ≤ _
  calc
    E w * g w + LinearSieve.finiteNodeVariationSum E g (suzukiFiniteNodes S w z) ≤
        B w * g w + LinearSieve.finiteNodeVariationSum B g (suzukiFiniteNodes S w z) :=
      add_le_add hboundary hvarmono
    _ = C * (σ^2 * H σ + LinearSieve.finiteNodeVariationSum (fun x => (t x)^2) g
          (suzukiFiniteNodes S w z)) := by
      dsimp [B, g]
      rw [htw]
      have hscale := LinearSieve.finiteNodeVariationSum_smul_left C (fun x => (t x)^2) g
        (suzukiFiniteNodes S w z)
      rw [hscale]
      ring
    _ ≤ C * (2 * s * σ * H s) := mul_le_mul_of_nonneg_left hquad hC0
    _ = 2 * K * H s / Real.log w := by
      have hlogw_formula : Real.log w = Real.log D / σ := by
        have hD0 : 0 < D := lt_trans (by norm_num) hD
        rw [hw, Real.log_rpow hD0]
        ring
      dsimp [C]
      rw [hlogw_formula]
      field_simp

/-- Suzuki Lemma 8.6 in dimension one, with the source-faithful main term
`(1/s) ∫ₛ^σ H(t) dt`.  It follows from the generic local Euler-product bound;
no prime-specific PNT or Mertens theorem is used. -/
theorem suzukiLemmaEightSixDimensionOne
    {S : BoundingSieve} {D w z s σ K : ℝ} {H : ℝ → ℝ}
    (hD : 1 < D) (hw2 : 2 ≤ w)
    (hs : 0 < s) (hsσ : s ≤ σ)
    (hz : z = D ^ (1 / s)) (hw : w = D ^ (1 / σ))
    (hHcont : Continuous H)
    (hH0 : ∀ t ∈ Set.Icc s σ, 0 ≤ H t)
    (hHt : AntitoneOn (fun t => H t * t) (Set.Icc s σ))
    (hK : 0 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSixPrimeSum S D w z H ≤
      (1 / s) * (∫ t in s..σ, H t) + 2 * K * H s / Real.log w := by
  have hord := SuzukiPowerCoordinates.endpoints_order hD hs hsσ hz hw
  have hw1 : 1 < w := hord.1
  have hwz : w ≤ z := hord.2
  have hz1 : 1 < z := hw1.trans_le hwz
  have hlogz : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz1)
  have hcoord : ∀ x ∈ Set.Icc w z,
      Real.log D / Real.log x ∈ Set.Icc s σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hs hsσ hz hw hx
  let g : ℝ → ℝ := fun x => H (Real.log D / Real.log x)
  have hg : MonotoneOn g (Set.Icc w z) := by
    exact transformedH_monotoneOn hD hw1 hwz hcoord hH0 hHt
  have hmain0 := LinearSieve.finiteNodeMainRatioSum_le_integral g
    (suzukiSupportedPrimeNodes S w z) hw1 hwz
    (suzukiFiniteNodes_pairwise S hwz) hg
  have hmain : LinearSieve.finiteNodeMainRatioSum z g
      (suzukiFiniteNodes S w z) ≤
      ∫ x in w..z, g x * (Real.log z / (x * (Real.log x) ^ 2)) := by
    simpa only [suzukiFiniteNodes] using hmain0
  have hmainNorm :=
    SuzukiMainTermNormalization.stieltjesMainTerm_changeOfVariables
      (D := D) (w := w) (z := z) (s := s) (σ := σ) (H := H)
      hD hs hsσ hz hw hHcont
  have herr := suzukiFiniteErrorVariation_le
    (S := S) (D := D) (w := w) (z := z) (s := s) (σ := σ) (K := K) (H := H)
    hD hw2 hwz hs hsσ hz hw hH0 hHt hK hlocal
  have hsplit := suzukiLemmaEightSixPrimeSum_mainErrorSplit S D w z H hwz hlogz
  change suzukiLemmaEightSixPrimeSum S D w z H =
      LinearSieve.finiteNodeMainRatioSum z g (suzukiFiniteNodes S w z) +
        suzukiFiniteErrorVariation S D w z H at hsplit
  calc
    suzukiLemmaEightSixPrimeSum S D w z H =
        LinearSieve.finiteNodeMainRatioSum z g (suzukiFiniteNodes S w z) +
          suzukiFiniteErrorVariation S D w z H := hsplit
    _ ≤ (∫ x in w..z, g x *
          (Real.log z / (x * (Real.log x) ^ 2))) +
          2 * K * H s / Real.log w := add_le_add hmain herr
    _ = (1 / s) * (∫ t in s..σ, H t) + 2 * K * H s / Real.log w := by
      have hn : (∫ x in w..z, g x *
          (Real.log z / (x * (Real.log x) ^ 2))) =
          (1 / s) * ∫ t in s..σ, H t := by
        simpa only [g] using hmainNorm
      exact congrArg (fun r : ℝ => r + 2 * K * H s / Real.log w) hn

end MathlibNt.SieveTheory.SwitchingPrinciple
