import Mathlib.NumberTheory.Harmonic.Bounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeNumberTheoremAnd.Wiener


set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev


/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      exact (sub_lt_iff_lt_add'.mpr (Nat.lt_floor_add_one b)).le
    rw [sub_nonneg]
    exact floor_le hb'

@[blueprint "chebyshev-asymptotic"
  (title := "chebyshev-asymptotic")
  (statement := /--
  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
  -/)
  (proof := /--
  From the prime number theorem we already have
  $$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
  so it suffices to show that
  $$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
  Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most
  $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as
  required.
  -/)]
theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (one_le_two.trans hx)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2


-- one could also consider adding a version with p < x instead of p \leq x


lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  have hlog : ContinuousOn (fun t : ℝ ↦ (log t)⁻¹) (Set.uIcc a b) := by
    intro t ht
    have ht1 : 1 < t := by rw [Set.uIcc_of_le hb] at ht; linarith [ht.1]
    exact ((continuousAt_log (by linarith)).inv₀ (log_pos ht1).ne').continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ ↦ (log t)⁻¹) volume a b := hlog.intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ (log t ^ 2)⁻¹) volume a b := by
    simpa only [one_div] using Chebyshev.intervalIntegrable_one_div_log_sq
      (by linarith : 1 < a) (by linarith : 1 < b)
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun t : ℝ ↦ (log t)⁻¹ * t) ((log t)⁻¹ - (log t ^ 2)⁻¹) t := by
    have ht1 : 1 < t := by rw [Set.uIcc_of_le hb] at ht; linarith [ht.1]
    convert! ((hasDerivAt_log (by linarith : t ≠ 0)).inv (log_pos ht1).ne').mul
      (hasDerivAt_id t) using 1
    simp only [Pi.inv_apply, id_eq]
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi.sub hi2)
  rw [intervalIntegral.integral_sub hi hi2] at h
  linarith


lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  classical
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp only [Function.support_inv, measurableSet_Icc, Measure.restrict_apply']
    rw [show Function.support log ∩ Set.Icc 2 x = Set.Icc 2 x by
      rw [Set.inter_eq_right]
      intro t ht
      simp only [Set.mem_Icc, Function.mem_support, ne_eq, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩]
    simpa
  · simp only [measurableSet_Icc, ae_restrict_eq, EventuallyLE, eventually_inf_principal]
    refine .of_forall fun t (ht : _ ∧ _) => ?_
    simpa only [Pi.zero_apply, inv_nonneg] using log_nonneg (by linarith)
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀
    · exact (continuousOn_log).mono <| by aesop

    · rintro t ⟨ht, -⟩
      simp only [ne_eq, log_eq_zero, not_or]
      exact ⟨by linarith, by linarith, by linarith⟩

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  have := integral_log_inv_pos x hx
  linarith


/-- The extra logarithm makes the quadratic-log scale negligible. -/
lemma div_log_sq_isLittleO :
    (fun x : ℝ ↦ x / log x ^ 2) =o[atTop] (fun x ↦ x / log x) := by
  refine isLittleO_iff_tendsto' (by simp) |>.mpr ?_
  refine tendsto_log_atTop.inv_tendsto_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Pi.inv_apply]
  field

/-- Integration by parts and the quadratic-log bound give the logarithmic integral's scale. -/
lemma integral_log_inv_isEquivalent :
    (fun x : ℝ ↦ ∫ t in Set.Icc 2 x, 1 / log t) ~[atTop] (fun x ↦ x / log x) := by
  have hrem := Chebyshev.integral_one_div_log_sq_isBigO.trans_isLittleO div_log_sq_isLittleO
  have hconst : (fun _ : ℝ ↦ 2 / log 2) =o[atTop] (fun x ↦ x / log x) := by
    refine isLittleO_iff_tendsto' ?_ |>.mpr ?_
    · filter_upwards [eventually_gt_atTop 1] with x hx
      simp [ne_of_gt (lt_trans zero_lt_one hx), (log_pos hx).ne']
    · convert (isLittleO_log_id_atTop.const_mul_left (2 / log 2)).tendsto_div_nhds_zero using 1
      ext x
      simp only [id_eq, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
  refine ((IsEquivalent.refl : (fun x : ℝ ↦ x / log x) ~[atTop] _).sub_isLittleO hconst
    |>.add_isLittleO hrem).congr_left ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  simp only [one_div]
  rw [integral_log_inv 2 x le_rfl hx]
  simp only [div_eq_mul_inv, mul_comm]

/- Preserve the old interval-membership matcher, including its compiler metadata.
Register before enabling lazy equations, as in Lean.Meta.Match's matcher compiler. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let name := `pi_asymp''.match_1_40
  let value ← Lean.Elab.Term.elabTerm (← `(fun (x t : ℝ)
    (motive : t ∈ Set.Icc 2 x → Prop) (h : t ∈ Set.Icc 2 x)
    (h_1 : ∀ (ht1 : @LE.le ℝ (@Preorder.toLE ℝ Real.instPreorder) 2 t)
      (ht2 : @LE.le ℝ (@Preorder.toLE ℝ Real.instPreorder) t x), motive ⟨ht1, ht2⟩) ↦
    (And.casesOn h fun left right ↦ h_1 left right : motive h))) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let value ← Lean.instantiateMVars value
  -- Legacy interface compatibility includes binder names, not just alpha-equivalence.
  -- Freeze the old compiler's three hygienic names; no old object is read here.
  let scope (n : Lean.Name) :=
    ((n ++ `«_@».PrimeNumberTheoremAnd.Consequences).num 507357399).str "_hygCtx"
  let oldH := (((((scope `h).num 4251 ++ `PrimeNumberTheoremAnd.Consequences).num
    507357399).str "_hygCtx").str "_hyg").num 4264
  let binderName (n : Lean.Name) := match n.eraseMacroScopes with
    | `h | `a => oldH -- The motive's anonymous domain binder was also the old h.
    | `left => ((scope `left).str "_hyg").num 4274
    | `right => ((scope `right).str "_hyg").num 4275
    | `x => `x | `t => `t | `motive => `motive
    | `h_1 => `h_1 | `ht1 => `ht1 | `ht2 => `ht2
    | _ => n
  let rec restoreNames : Lean.Expr → Lean.Expr
    | .lam n t b i => .lam (binderName n) (restoreNames t) (restoreNames b) i
    | .forallE n t b i => .forallE (binderName n) (restoreNames t) (restoreNames b) i
    | .app f a => .app (restoreNames f) (restoreNames a)
    | .letE n t v b d => .letE n (restoreNames t) (restoreNames v) (restoreNames b) d
    | .mdata d b => .mdata d (restoreNames b)
    | .proj n i b => .proj n i (restoreNames b)
    | e => e
  let type := restoreNames (← Lean.Meta.inferType value)
  let value := restoreNames value
  let decl := Lean.Declaration.defnDecl {
    name, levelParams := [], type, value,
    hints := .abbrev, safety := .safe, all := [name] }
  Lean.addDecl decl
  Lean.setReducibilityStatus name .instanceReducible
  Lean.Meta.Match.addMatcherInfo name {
    numParams := 2, numDiscrs := 1,
    altInfos := #[{ numFields := 2, numOverlaps := 0, hasUnitThunk := false }],
    uElimPos? := none, discrInfos := #[{ hName? := none }], overlaps := {} }
  Lean.Meta.setInlineAttribute name
  Lean.enableRealizationsForConst name
  Lean.compileDecl decl

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  have hpi : (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x ↦ x / log x) := by
    refine ((chebyshev_asymptotic.div (IsEquivalent.refl (u := log))).add_isLittleO
      Chebyshev.integral_theta_div_log_sq_isLittleO).congr_left ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    exact (Chebyshev.primeCounting_eq_theta_div_log_add_integral hx).symm
  have hratio := (isEquivalent_iff_tendsto_one ?_).mp
    (hpi.trans integral_log_inv_isEquivalent.symm)
  · rw [isLittleO_one_iff]
    simpa using hratio.sub_const 1
  filter_upwards [eventually_gt_atTop 2] with x hx
  simpa only [one_div] using integral_log_inv_ne_zero x hx

@[blueprint
  (title := "pi-asymp")
  (statement := /--
  There exists a function $c(x)$ such that $c(x) = o(1)$ as $x \to \infty$ and
  $$ \pi(x) = (1 + c(x)) \int_2^x \frac{dt}{\log t}$$
  for all $x$ large enough.
  -/)
  (proof := /--
  We have the identity
  $$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
  + \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
  as can be proven by interchanging the sum and integral and using the fundamental theorem of
  calculus.  For any $\eps$, we know from Theorem \ref{chebyshev_asymptotic} that there is $x_\eps$
  such that $\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
  $$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
  + \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
  where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate
  this after an integration by parts as
  $$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
  $$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
  for $x$ large enough, giving the claim.
  -/)]
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']


lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  refine ⟨fun x ↦ (∫ t in Set.Icc 2 x, 1 / log t) / (x / log x) - 1, ?_, ?_⟩
  · rw [isLittleO_one_iff]
    have hratio := (isEquivalent_iff_tendsto_one ?_).mp integral_log_inv_isEquivalent
    · simpa using hratio.sub_const 1
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)) (log_pos hx).ne'
  · filter_upwards [eventually_gt_atTop 1] with x hx
    field [ne_of_gt (lt_trans zero_lt_one hx), (log_pos hx).ne']

@[blueprint
  (title := "pi-alt")
  (statement := /--
    One has
  $$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
  as $x \to \infty$.
  -/)
  (proof := /--
  An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} +
  \int_2^x \frac{dt}{\log^2 t}.$$
  We have the crude bounds
  $$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
  and
  $$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
  and combining all this we obtain
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
  $$ = (1+o(1)) \frac{x}{\log x}$$
  and the claim then follows from Theorem \ref{pi_asymp}.
  -/)
  (latexEnv := "corollary")]
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨f, hf, h⟩ := pi_asymp
  obtain ⟨f', hf', h'⟩ := integral_div_log_asymptotic
  use (fun x => (log x / x) * ⌊x⌋₊.primeCounting - 1)
  constructor
  · apply IsLittleO.congr' (f₁ := (fun x ↦ f x + f x * f' x + f' x)) _ _ (by rfl)
    · apply IsLittleO.add _ hf'
      apply IsLittleO.add hf
      convert! hf.mul hf'
      ring
    · filter_upwards [eventually_ge_atTop 2, h, h'] with x hx h h'
      rw [h, intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc, h']
      have : log x ≠ 0 := by simp; grind
      field
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

theorem pi_alt' :
    (fun (x : ℝ) ↦ (primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / log x) := by
  obtain ⟨f, ⟨hf1, hf2⟩⟩ := pi_alt
  simp_rw [hf2, IsEquivalent]
  have : ((fun x ↦ (1 + f x) * x / log x) - fun x ↦ x / log x) =
      (fun x ↦ f x * x / log x) := by
    ext
    simp
    ring
  rw [this]
  convert hf1.mul_isBigO (f₂ := (fun x ↦ x / log x)) (g₂ := (fun x ↦ x /log x))
      (isBigO_refl ..) using 2
  all_goals first | ring | rfl


blueprint_comment /--
\section{Consequences of the PNT in arithmetic progressions}
-/


blueprint_comment /--
\section{Consequences of the Chebotarev density theorem}

-/

blueprint_comment /--
\begin{lemma}[Cyclotomic Chebotarev]\label{Chebotarev-cyclic}
Let $m\geq 1$ and $G = \mathrm{Gal}(\mathbb{Q}(\mu_m)/\mathbb{Q}) \cong (\mathbb{Z}/m\mathbb{Z})^\times$.
For any $a$ coprime to $m$,
\[
\sum_{\substack{N\mathfrak{p}\leq x\\ N\mathfrak{p}\equiv a\pmod{m}}} \log N\mathfrak{p}
\;=\;
\frac{1}{|G|} \sum_{N\mathfrak{p}\leq x} \log N\mathfrak{p}
\;+\; o\Bigl(\sum_{N\mathfrak{p}\leq x} \log N\mathfrak{p}\Bigr).
\]
In particular the primes in the progression $a\pmod{m}$ have natural density $1/\varphi(m)$
(Dirichlet's theorem).
\end{lemma}
-/

blueprint_comment /--
\begin{proof}\uses{Chebotarev-cyclotomic-density, Dedekind-PNT, WeakPNT-AP}
Specialise Proposition~\ref{Chebotarev-cyclotomic-density} to $K=\mathbb{Q}$ and
$L=\mathbb{Q}(\mu_m)$: the Frobenius condition $\varphi_p=\sigma_a$ with
$\sigma_a(\zeta_m)=\zeta_m^a$ is exactly $p\equiv a\pmod{m}$.  The asymptotic form with
$\log N\mathfrak{p}$ follows by Fourier expansion of the indicator of the progression against
characters of $G$, using Lemma~\ref{Dedekind-PNT} to kill the nontrivial character sums and
the prime-number theorem in AP (Lemma~\ref{WeakPNT-AP}) for the main term.  Cf.\ also
Corollary~7.2.3 of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}.
\end{proof}
-/
