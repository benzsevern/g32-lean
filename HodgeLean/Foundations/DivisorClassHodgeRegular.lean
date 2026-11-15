import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.Regular.Free
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Regular local rings are factorial (DC1, sub-stage f)

The Auslander–Buchsbaum theorem in the form used by `dc1_locallyPrincipal`: a Noetherian local
ring all of whose localizations at primes are regular local rings is a unique factorization
domain (`dcl_ufd_of_isRegularRing`, `dcl_ufd_localization_atPrime`). The proof is Kaplansky's:

* a regular local ring is a domain, and for `x ∈ 𝔪 \ 𝔪²` the quotient `R ⧸ (x)` is regular local
  of one lower dimension (`dcl_isDomain_of_ringKrullDim_eq`, `dcl_exists_quotient_regular`);
* over a regular local ring of dimension `n` every `n`-th syzygy of a finitely generated module
  is free (`dcl_syzFree_of_isRegularLocalRing`), by reduction modulo such an `x`
  (`dcl_reduceKerEquiv`, `dcl_SyzFree_of_quotSMulTop`); so finitely generated modules have
  finite free resolutions, which localize (`dcl_HasFFR.localization`), and a projective module
  with one is stably free (`dcl_HasFFR.isStablyFree`);
* a nonzero finitely generated ideal of a domain that is principal near every maximal ideal is
  an invertible module (`dcl_invertible_of_locally_principal`);
* induction on the dimension: `x` is prime, the localizations of `R[1/x]` at primes are
  factorial by induction, so a height-one prime of `R[1/x]` is invertible and stably free, hence
  free (`Module.free_of_isStablyFree_of_invertible`) and principal; Nagata's criterion
  (`UniqueFactorizationMonoid.iff_localizationAway_of_prime`) concludes.

Source: Matsumura, *Commutative Ring Theory*, Theorem 20.3 (Auslander–Buchsbaum), Theorem 19.2
and Lemma 19.1 (finite free resolutions over regular local rings), Theorem 14.3 (regular local
rings are domains), Theorem 20.2 (Nagata); Kaplansky, *Commutative Rings*, Theorem 184.
HC no distance; AV milestone no distance.
-/

noncomputable section

open IsLocalRing Pointwise

universe u

namespace HodgeLean.Foundations

section RegularLocal

/-- A Noetherian local ring has finite Krull dimension. -/
theorem dcl_exists_ringKrullDim_eq_natCast (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ∃ n : ℕ, ringKrullDim R = n := by
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim R := ringKrullDim_nonneg_of_nontrivial
  have h1 := ringKrullDim_le_spanFinrank_maximalIdeal R
  generalize ringKrullDim R = e at h0 h1
  induction e using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h1 (by rw [not_le]; exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
    | coe m => exact ⟨m, rfl⟩

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The quotient of a local ring by an element of the maximal ideal is local. -/
theorem dcl_quotient_isLocalRing {x : A} (hx : x ∈ maximalIdeal A) :
    IsLocalRing (A ⧸ Ideal.span {x}) := by
  have : Nontrivial (A ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (mem_maximalIdeal x).mp hx)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Quotienting by an element of `𝔪` outside the minimal primes lowers the dimension by one. -/
theorem dcl_ringKrullDim_quotient_succ {x : A} (hx : x ∈ maximalIdeal A)
    (hmin : ∀ p ∈ minimalPrimes A, x ∉ p) :
    ringKrullDim (A ⧸ Ideal.span {x}) + 1 = ringKrullDim A := by
  have hann : Module.annihilator A A = ⊥ :=
    Module.annihilator_eq_bot.mpr
      ((faithfulSMul_iff_algebraMap_injective A A).mpr fun {a₁ a₂} a ↦ a)
  have h := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (M := A) (x := x) (by rw [hann]; exact hmin) hx
  have hsp : Ideal.span {x} = x • (⊤ : Ideal A) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [Module.supportDim_self_eq_ringKrullDim] at h
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq A hsp).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim]
  exact h

/-- If `𝔪 = 𝔪²` the local ring is a field (Nakayama), so it has dimension `0`. -/
theorem dcl_ringKrullDim_eq_zero_of_maximalIdeal_le_sq
    (h : maximalIdeal A ≤ maximalIdeal A ^ 2) : ringKrullDim A = 0 := by
  have hid : IsIdempotentElem (maximalIdeal A) := by
    rw [IsIdempotentElem, ← pow_two]
    exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing _).mp hid with h0 | h0
  · exact ringKrullDim_eq_zero_of_isField ((isField_iff_maximalIdeal_eq).mpr h0)
  · exact absurd h0 (maximalIdeal.isMaximal A).ne_top

/-- In positive dimension some `x ∈ 𝔪` avoids `𝔪²` and every minimal prime (prime avoidance). -/
theorem dcl_exists_mem_maximalIdeal_regular (h : 0 < ringKrullDim A) :
    ∃ x ∈ maximalIdeal A, x ∉ maximalIdeal A ^ 2 ∧ ∀ p ∈ minimalPrimes A, x ∉ p := by
  by_contra H
  push Not at H
  classical
  let s : Finset (Ideal A) :=
    (minimalPrimes.finite_of_isNoetherianRing A).toFinset
  have hsub : ((maximalIdeal A : Ideal A) : Set A) ⊆
      ((id (maximalIdeal A ^ 2) : Ideal A) : Set A) ∪
        ((id (maximalIdeal A ^ 2) : Ideal A) : Set A) ∪ ⋃ i ∈ (↑s : Set (Ideal A)), ((id i : Ideal A) : Set A) := by
    intro x hx
    by_cases hx2 : x ∈ maximalIdeal A ^ 2
    · exact Or.inl (Or.inl hx2)
    · obtain ⟨p, hp, hxp⟩ := H x hx hx2
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨p, ?_, hxp⟩)
      simpa [s] using hp
  rcases (Ideal.subset_union_prime' (s := s) (f := id) (a := maximalIdeal A ^ 2)
      (b := maximalIdeal A ^ 2) (fun i hi ↦ by
        have hi' : i ∈ minimalPrimes A := by simpa [s] using hi
        exact hi'.1.1)).mp hsub with h2 | h2 | ⟨p, hp, hle⟩
  · exact h.ne' (dcl_ringKrullDim_eq_zero_of_maximalIdeal_le_sq h2)
  · exact h.ne' (dcl_ringKrullDim_eq_zero_of_maximalIdeal_le_sq h2)
  · have hp' : p ∈ minimalPrimes A := by simpa [s] using hp
    have : p.IsPrime := hp'.1.1
    have heq : p = maximalIdeal A := le_antisymm (le_maximalIdeal this.ne_top) hle
    have h0 : (maximalIdeal A).height = 0 := by
      rw [← heq]
      exact Ideal.height_eq_zero_iff.mpr hp'
    rw [← maximalIdeal_height_eq_ringKrullDim, h0] at h
    exact lt_irrefl _ h

end RegularLocal

section RegularLocal'

/-- For `x ∈ 𝔪 \ 𝔪²` outside the minimal primes, `R ⧸ (x)` is again regular local. -/
theorem dcl_quotient_isRegularLocalRing {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {x : A} (hx : x ∈ maximalIdeal A) (hx2 : x ∉ maximalIdeal A ^ 2)
    (hmin : ∀ p ∈ minimalPrimes A, x ∉ p) :
    IsRegularLocalRing (A ⧸ Ideal.span {x}) := by
  let := dcl_quotient_isLocalRing hx
  let S := A ⧸ Ideal.span {x}
  have : IsLocalHom (algebraMap A S) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hsum := spanFinrank_maximalIdeal_add_finrank_eq_of_surjective (R := A) (S := S)
    Ideal.Quotient.mk_surjective
  set W := Submodule.map (toCotangentSpace A)
    (Submodule.comap (Submodule.subtype (maximalIdeal A)) (RingHom.ker (algebraMap A S)))
  have hW : 1 ≤ Module.finrank (ResidueField A) W := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h0
    have hmem : toCotangentSpace A ⟨x, hx⟩ ∈ W := by
      refine Submodule.mem_map_of_mem ?_
      simp [S]
    rw [h0, Submodule.mem_bot, toCotangentSpace_apply, Ideal.toCotangent_eq_zero] at hmem
    exact hx2 hmem
  have hA : ringKrullDim A = (maximalIdeal A).spanFinrank :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have hdim := dcl_ringKrullDim_quotient_succ hx hmin
  obtain ⟨e, he⟩ := dcl_exists_ringKrullDim_eq_natCast S
  change ringKrullDim S + 1 = _ at hdim
  rw [he, hA] at hdim
  have he' : e + 1 = (maximalIdeal A).spanFinrank := by exact_mod_cast hdim
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  change ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim S
  rw [he]
  exact_mod_cast (by omega : (maximalIdeal S).spanFinrank ≤ e)
/-- A regular local ring is a domain, by induction on its dimension. -/
theorem dcl_isDomain_of_ringKrullDim_eq : ∀ (n : ℕ) (R : Type u) [CommRing R]
    [IsRegularLocalRing R], ringKrullDim R = n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    have h0 : (maximalIdeal R).spanFinrank = 0 := by
      have := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R))
      rw [h] at this
      exact_mod_cast this
    rw [Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing] at h0
    let := ((isField_iff_maximalIdeal_eq).mpr h0).toField
    infer_instance
  | succ n ih =>
    intro R _ _ h
    obtain ⟨x, hx, hx2, hmin⟩ := dcl_exists_mem_maximalIdeal_regular (A := R)
      (by rw [h]; exact_mod_cast Nat.succ_pos n)
    let := dcl_quotient_isLocalRing hx
    have hreg := dcl_quotient_isRegularLocalRing hx hx2 hmin
    have hdim := dcl_ringKrullDim_quotient_succ hx hmin
    rw [h] at hdim
    have hdim' : ringKrullDim (R ⧸ Ideal.span {x}) = n := by
      obtain ⟨e, he⟩ := dcl_exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})
      rw [he] at hdim ⊢
      have : e + 1 = n + 1 := by exact_mod_cast hdim
      exact_mod_cast (by omega : e = n)
    have hdom := ih (R ⧸ Ideal.span {x}) hdim'
    have hprime : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ Ideal.span {x})
    have hpp : p.IsPrime := hp.1.1
    have hxp : x ∉ p := hmin p hp
    have hle : p ≤ Ideal.span {x} • p := by
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (hpx hy)
      have ha : a ∈ p := (hpp.mem_or_mem hy).resolve_right hxp
      have := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) ha
      rwa [smul_eq_mul (a := x), mul_comm x a] at this
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ p
      (p.fg_of_isNoetherianRing) hle (by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact (maximalIdeal_le_jacobson _) hx)
    rw [hbot] at hpp
    exact IsDomain.of_bot_isPrime R

/-- A regular local ring is a domain. -/
instance (priority := 100) dcl_IsRegularLocalRing.isDomain (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R := by
  obtain ⟨n, hn⟩ := dcl_exists_ringKrullDim_eq_natCast R
  exact dcl_isDomain_of_ringKrullDim_eq n R hn

end RegularLocal'

section Syzygy

/-- Every `n`-th syzygy of `M` built from the finite free modules `Fin k → R` is free: for
`n = 0`, `M` itself is free; for `n + 1`, the kernel of every surjection `R^k → M` has free
`n`-th syzygies.
Source: Matsumura, *Commutative Ring Theory*, §19 (syzygies and projective dimension over a local
ring); Serre, *Algèbre locale, multiplicités*, Ch. IV. -/
def dcl_SyzFree (R : Type u) [CommRing R] :
    ℕ → (M : Type u) → [AddCommGroup M] → [Module R M] → Prop
  | 0, M, _, _ => Module.Free R M
  | n + 1, M, _, _ => ∀ (k : ℕ) (f : (Fin k → R) →ₗ[R] M), Function.Surjective f →
      dcl_SyzFree R n (LinearMap.ker f)

/-- A ring has free `0`-th syzygies over itself. -/
example (R : Type u) [CommRing R] : dcl_SyzFree R 0 R := by
  unfold dcl_SyzFree
  infer_instance

/-- Free syzygies are invariant under linear equivalence. -/
theorem dcl_SyzFree.of_equiv {R : Type u} [CommRing R] :
    ∀ (n : ℕ) {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
      (M ≃ₗ[R] N) → dcl_SyzFree R n M → dcl_SyzFree R n N
  | 0, M, N, _, _, _, _, e, h => by
    unfold dcl_SyzFree at h ⊢
    exact Module.Free.of_equiv e
  | n + 1, M, N, _, _, _, _, e, h => by
    unfold dcl_SyzFree at h ⊢
    intro k f hf
    have h' := h k (e.symm.toLinearMap ∘ₗ f) (e.symm.surjective.comp hf)
    have hk : LinearMap.ker (e.symm.toLinearMap ∘ₗ f) = LinearMap.ker f :=
      LinearEquiv.ker_comp e.symm f
    rw [hk] at h'
    exact h'


section Reduction

variable {R : Type u} [CommRing R] (x : R)

/-- The reduction modulo `x` of a map `f` out of `R^k`, as a map out of `(R ⧸ (x))^k`.
Source: Matsumura, *Commutative Ring Theory*, Lemma 19.1 (reduction of a resolution modulo a
regular element). -/
noncomputable def dcl_reduceMap {N : Type u} [AddCommGroup N] [Module R N] {k : ℕ}
    (f : (Fin k → R) →ₗ[R] N) :
    (Fin k → R ⧸ Ideal.span {x}) →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N :=
  Fintype.linearCombination (R ⧸ Ideal.span {x})
    (fun i ↦ Submodule.Quotient.mk (f (Pi.single i 1)))

/-- The reduction of a map vanishes at `0`. -/
example {N : Type u} [AddCommGroup N] [Module R N] {k : ℕ} (f : (Fin k → R) →ₗ[R] N) :
    dcl_reduceMap x f 0 = 0 := map_zero _

/-- The reduction of `f` on reduced vectors is the reduction of `f`. -/
theorem dcl_reduceMap_apply {N : Type u} [AddCommGroup N] [Module R N] {k : ℕ}
    (f : (Fin k → R) →ₗ[R] N) (v : Fin k → R) :
    dcl_reduceMap x f (fun i ↦ Ideal.Quotient.mk _ (v i)) = Submodule.Quotient.mk (f v) := by
  rw [dcl_reduceMap, Fintype.linearCombination_apply]
  conv_rhs => rw [pi_eq_sum_univ v, map_sum, ← Submodule.mkQ_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, Submodule.mkQ_apply, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  rw [← Submodule.Quotient.mk_smul]
  congr 3
  funext j
  simp [Pi.single_apply, eq_comm]

variable {N : Type u} [AddCommGroup N] [Module R N] {k : ℕ} (f : (Fin k → R) →ₗ[R] N)

/-- The reduction of a surjection is a surjection. -/
theorem dcl_reduceMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (dcl_reduceMap x f) := by
  intro q
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨v, rfl⟩ := hf n
  exact ⟨_, dcl_reduceMap_apply x f v⟩

/-- Reduction modulo `x` of an element of the kernel of `f`.
Source: Matsumura, *Commutative Ring Theory*, Lemma 19.1. -/
noncomputable def dcl_reduceKer : LinearMap.ker f →ₗ[R] LinearMap.ker (dcl_reduceMap x f) where
  toFun c := ⟨fun i ↦ Ideal.Quotient.mk _ ((c : Fin k → R) i), by
    rw [LinearMap.mem_ker, dcl_reduceMap_apply, LinearMap.mem_ker.mp c.2]
    rfl⟩
  map_add' c d := by ext i; simp
  map_smul' r c := by
    ext i
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]

/-- The reduction of the zero kernel element is zero. -/
example : dcl_reduceKer x f 0 = 0 := map_zero _

/-- Coordinates of the reduction of a kernel element. -/
theorem dcl_reduceKer_apply (c : LinearMap.ker f) (i : Fin k) :
    ((dcl_reduceKer x f c : LinearMap.ker (dcl_reduceMap x f)) : Fin k → R ⧸ Ideal.span {x}) i =
      Ideal.Quotient.mk _ ((c : Fin k → R) i) := rfl

/-- The reduction map, from `ker f ⧸ x` to the kernel of the reduction of `f`.
Source: Matsumura, *Commutative Ring Theory*, Lemma 19.1. -/
noncomputable def dcl_reduceKerQuot :
    QuotSMulTop x (LinearMap.ker f) →ₗ[R ⧸ Ideal.span {x}] LinearMap.ker (dcl_reduceMap x f) :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((x • (⊤ : Submodule R (LinearMap.ker f))).liftQ (dcl_reduceKer x f) (by
      intro y hy
      obtain ⟨c, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [LinearMap.mem_ker, map_smul]
      ext i
      simp [dcl_reduceKer_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]))

/-- The reduction map on classes of kernel elements. -/
theorem dcl_reduceKerQuot_mk (c : LinearMap.ker f) :
    dcl_reduceKerQuot x f (Submodule.Quotient.mk c) = dcl_reduceKer x f c := rfl

/-- The reduction of the zero kernel element is zero. -/
example : dcl_reduceKerQuot x f 0 = 0 := map_zero _

/-- For `x` regular on the target, reduction identifies `ker f ⧸ x` with `ker (f mod x)`. -/
theorem dcl_reduceKerQuot_bijective (hf : Function.Surjective f) (hN : IsSMulRegular N x) :
    Function.Bijective (dcl_reduceKerQuot x f) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [dcl_reduceKerQuot_mk] at hq
    have hc : ∀ i, ∃ d : R, d * x = (c : Fin k → R) i := fun i ↦ by
      have := congrArg (fun w : LinearMap.ker (dcl_reduceMap x f) ↦
        (w : Fin k → R ⧸ Ideal.span {x}) i) hq
      simp only [dcl_reduceKer_apply, ZeroMemClass.coe_zero, Pi.zero_apply,
        Ideal.Quotient.eq_zero_iff_mem] at this
      exact Ideal.mem_span_singleton'.mp this
    choose d hd using hc
    have hcd : (c : Fin k → R) = x • d := by
      funext i; simp [← hd i, mul_comm]
    have hfd : f d = 0 := by
      apply hN
      change x • f d = x • 0
      rw [smul_zero, ← map_smul, ← hcd]
      exact LinearMap.mem_ker.mp c.2
    have : c = x • (⟨d, LinearMap.mem_ker.mpr hfd⟩ : LinearMap.ker f) := by
      ext1; exact hcd
    rw [this, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · intro w
    let v : Fin k → R := fun i ↦ Function.surjInv Ideal.Quotient.mk_surjective
      ((w : Fin k → R ⧸ Ideal.span {x}) i)
    have hv : (fun i ↦ Ideal.Quotient.mk _ (v i)) = (w : Fin k → R ⧸ Ideal.span {x}) := by
      funext i; exact Function.surjInv_eq _ _
    have hfv : f v ∈ x • (⊤ : Submodule R N) := by
      have h := LinearMap.mem_ker.mp w.2
      rw [← hv, dcl_reduceMap_apply] at h
      exact (Submodule.Quotient.mk_eq_zero _).mp h
    obtain ⟨n, -, hn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hfv
    obtain ⟨u, rfl⟩ := hf n
    have hc : v - x • u ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hn, sub_self]
    refine ⟨Submodule.Quotient.mk ⟨v - x • u, hc⟩, ?_⟩
    rw [dcl_reduceKerQuot_mk]
    ext i
    rw [dcl_reduceKer_apply, ← hv]
    simp

/-- `ker f ⧸ x ≃ ker (f mod x)` for `x` regular on the target.
Source: Matsumura, *Commutative Ring Theory*, Lemma 19.1 (`Tor₁(M, R ⧸ (x)) = 0` for `x`
regular on `M`). -/
noncomputable def dcl_reduceKerEquiv (hf : Function.Surjective f) (hN : IsSMulRegular N x) :
    QuotSMulTop x (LinearMap.ker f) ≃ₗ[R ⧸ Ideal.span {x}] LinearMap.ker (dcl_reduceMap x f) :=
  LinearEquiv.ofBijective _ (dcl_reduceKerQuot_bijective x f hf hN)

/-- On classes of kernel elements the equivalence is the reduction map. -/
example (hf : Function.Surjective f) (hN : IsSMulRegular N x) (c : LinearMap.ker f) :
    dcl_reduceKerEquiv x f hf hN (Submodule.Quotient.mk c) = dcl_reduceKer x f c := rfl

end Reduction

/-- In a regular local ring of dimension `n + 1` there is `x ∈ 𝔪 \ 𝔪²`; it is regular and
`R ⧸ (x)` is regular local of dimension `n`. -/
theorem dcl_exists_quotient_regular {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (h : ringKrullDim R = (n + 1 : ℕ)) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ IsSMulRegular R x ∧
      IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧ ringKrullDim (R ⧸ Ideal.span {x}) = n := by
  obtain ⟨x, hx, hx2, hmin⟩ := dcl_exists_mem_maximalIdeal_regular (A := R)
    (by rw [h]; exact_mod_cast Nat.succ_pos n)
  let := dcl_quotient_isLocalRing hx
  have hreg := dcl_quotient_isRegularLocalRing hx hx2 hmin
  have hdim := dcl_ringKrullDim_quotient_succ hx hmin
  rw [h] at hdim
  have hdim' : ringKrullDim (R ⧸ Ideal.span {x}) = n := by
    obtain ⟨e, he⟩ := dcl_exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})
    rw [he] at hdim ⊢
    have : e + 1 = n + 1 := by exact_mod_cast hdim
    exact_mod_cast (by omega : e = n)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (Submodule.zero_mem _)
  exact ⟨x, hx, hx2, (IsRegular.of_ne_zero hx0).isSMulRegular, hreg, hdim'⟩

/-- A regular element of `R` is regular on every submodule of `R^k`. -/
theorem dcl_isSMulRegular_ker {R : Type u} [CommRing R] {x : R} (hxR : IsSMulRegular R x)
    {N : Type u} [AddCommGroup N] [Module R N] {k : ℕ} (f : (Fin k → R) →ₗ[R] N) :
    IsSMulRegular (LinearMap.ker f) x := by
  intro a b hab
  ext i
  have := congrArg (fun c : LinearMap.ker f ↦ (c : Fin k → R) i) hab
  exact hxR (by simpa using this)

/-- Reduction modulo a regular element `x ∈ 𝔪`: if the `n`-th syzygies of `N ⧸ x N` over
`R ⧸ (x)` are free and `x` is regular on `N`, the `n`-th syzygies of `N` are free. -/
theorem dcl_SyzFree_of_quotSMulTop {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) :
    ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsSMulRegular N x → dcl_SyzFree (R ⧸ Ideal.span {x}) n (QuotSMulTop x N) →
        dcl_SyzFree R n N
  | 0, N, _, _, _, hN, h => by
    unfold dcl_SyzFree at h ⊢
    have : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
    exact (Module.free_quotSMulTop_iff_free R N ((maximalIdeal_le_jacobson ⊥) hx) hN).mp h
  | n + 1, N, _, _, _, hN, h => by
    unfold dcl_SyzFree at h ⊢
    intro k f hf
    have h' := h k (dcl_reduceMap x f) (dcl_reduceMap_surjective x f hf)
    have h'' := dcl_SyzFree.of_equiv n (dcl_reduceKerEquiv x f hf hN).symm h'
    exact dcl_SyzFree_of_quotSMulTop hx hxR n (LinearMap.ker f) (dcl_isSMulRegular_ker hxR f) h''

/-- **Syzygy theorem.** Over a regular local ring of dimension `n`, every `n`-th syzygy of a
finitely generated module is free. -/
theorem dcl_syzFree_of_isRegularLocalRing : ∀ (n : ℕ) (R : Type u) [CommRing R]
    [IsRegularLocalRing R], ringKrullDim R = n → ∀ (M : Type u) [AddCommGroup M] [Module R M]
      [Module.Finite R M], dcl_SyzFree R n M := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h M _ _ _
    unfold dcl_SyzFree
    have h0 : (maximalIdeal R).spanFinrank = 0 := by
      have := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R))
      rw [h] at this
      exact_mod_cast this
    rw [Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing] at h0
    let := ((isField_iff_maximalIdeal_eq).mpr h0).toField
    exact Module.Free.of_divisionRing R M
  | succ n ih =>
    intro R _ _ h M _ _ _
    obtain ⟨x, hx, -, hxR, hreg, hdim⟩ := dcl_exists_quotient_regular h
    unfold dcl_SyzFree
    intro k f hf
    have : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x (LinearMap.ker f)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    exact dcl_SyzFree_of_quotSMulTop hx hxR n (LinearMap.ker f) (dcl_isSMulRegular_ker hxR f)
      (ih (R ⧸ Ideal.span {x}) hdim _)

end Syzygy

section Resolution

/-- `M` has a finite resolution of length `n` by finite free modules: `M` is finite free, or a
finite free module surjects onto `M` with a kernel that has such a resolution of length `n - 1`.
Source: Matsumura, *Commutative Ring Theory*, §19 (finite free resolutions); Kaplansky,
*Commutative Rings*, §4.2. -/
inductive dcl_HasFFR (R : Type u) [CommRing R] :
    ℕ → (M : Type u) → [AddCommGroup M] → [Module R M] → Prop
  | free {M : Type u} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
      dcl_HasFFR R 0 M
  | step {n : ℕ} {M : Type u} [AddCommGroup M] [Module R M] (F : Type u) [AddCommGroup F]
      [Module R F] [Module.Free R F] [Module.Finite R F] (f : F →ₗ[R] M)
      (hf : Function.Surjective f) (h : dcl_HasFFR R n (LinearMap.ker f)) :
      dcl_HasFFR R (n + 1) M

/-- A ring has a finite free resolution of length `0` over itself. -/
example (R : Type u) [CommRing R] : dcl_HasFFR R 0 R := .free

variable {R : Type u} [CommRing R]

/-- A split surjection `f` with section `s` identifies its source with `ker f × M`.
Source: Matsumura, *Commutative Ring Theory*, §2 (split exact sequences). -/
def dcl_splitEquiv {F M : Type u} [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (f : F →ₗ[R] M) (s : M →ₗ[R] F) (hs : f ∘ₗ s = LinearMap.id) :
    F ≃ₗ[R] LinearMap.ker f × M where
  toFun v := (⟨v - s (f v), by
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply f s, hs, LinearMap.id_apply,
      sub_self]⟩, f v)
  invFun p := (p.1 : F) + s p.2
  map_add' v w := by ext <;> simp; abel
  map_smul' r v := by ext <;> simp [smul_sub]
  left_inv v := by simp
  right_inv p := by
    have h1 : f (s p.2) = p.2 := by rw [← LinearMap.comp_apply f s, hs, LinearMap.id_apply]
    have h2 : f (p.1 : F) = 0 := LinearMap.mem_ker.mp p.1.2
    ext <;> simp [h1, h2]

/-- The second component of the splitting is `f`. -/
example {F M : Type u} [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (f : F →ₗ[R] M) (s : M →ₗ[R] F) (hs : f ∘ₗ s = LinearMap.id) (v : F) :
    (dcl_splitEquiv f s hs v).2 = f v := rfl

/-- A projective module with a finite free resolution is stably free. -/
theorem dcl_HasFFR.isStablyFree : ∀ {n : ℕ} {M : Type u} [AddCommGroup M] [Module R M],
    dcl_HasFFR R n M → Module.Projective R M → Module.IsStablyFree R M := by
  intro n M _ _ h
  induction h with
  | free => intro _; infer_instance
  | @step n M _ _ F _ _ _ _ f hf h ih =>
    intro hM
    obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
    let e := dcl_splitEquiv f s hs
    have hK : Module.Projective R (LinearMap.ker f) :=
      Module.Projective.of_split (LinearMap.ker f).subtype
        ((LinearMap.fst R _ M) ∘ₗ e.toLinearMap) (by ext x; simp [e, dcl_splitEquiv])
    have : Module.IsStablyFree R (LinearMap.ker f) := ih hK
    have hKf : Module.Finite R (LinearMap.ker f) :=
      Module.Finite.of_surjective ((LinearMap.fst R _ M) ∘ₗ e.toLinearMap)
        (fun k ↦ ⟨k, by simp [e, dcl_splitEquiv]⟩)
    obtain ⟨N, _, _, _, _, hfree⟩ := Module.IsStablyFree.exist_free_prod R (LinearMap.ker f)
    have : Module.Free R (M × (LinearMap.ker f × N)) :=
      Module.Free.of_equiv ((e.prodCongr (LinearEquiv.refl R N)) ≪≫ₗ
        ((LinearEquiv.prodComm R _ M).prodCongr (LinearEquiv.refl R N)) ≪≫ₗ
        (LinearEquiv.prodAssoc R M _ N))
    exact Module.IsStablyFree.of_free_prod R M (LinearMap.ker f × N)


/-- Finite free resolutions localize. -/
theorem dcl_HasFFR.localization (S : Submonoid R) : ∀ {n : ℕ} {M : Type u} [AddCommGroup M]
    [Module R M], dcl_HasFFR R n M → ∀ {Mₛ : Type u} [AddCommGroup Mₛ] [Module R Mₛ]
      [Module (Localization S) Mₛ] [IsScalarTower R (Localization S) Mₛ] (g : M →ₗ[R] Mₛ)
      [IsLocalizedModule S g], dcl_HasFFR (Localization S) n Mₛ := by
  intro n M _ _ h
  induction h with
  | free =>
    intro Mₛ _ _ _ _ g _
    have := Module.free_of_isLocalizedModule (Rₛ := Localization S) S g
    have := Module.Finite.of_isLocalizedModule S (Rₚ := Localization S) g
    exact .free
  | @step n M _ _ F _ _ _ _ f hf h ih =>
    intro Mₛ _ _ _ _ g _
    let ℓ := LocalizedModule.mkLinearMap S F
    let φ := IsLocalizedModule.map S ℓ g f
    let fₛ := φ.extendScalarsOfIsLocalization S (Localization S)
    have hsurj : Function.Surjective fₛ := IsLocalizedModule.map_surjective S ℓ g f hf
    have := Module.free_of_isLocalizedModule (Rₛ := Localization S) S ℓ
    have := Module.Finite.of_isLocalizedModule S (Rₚ := Localization S) ℓ
    let e : LinearMap.ker φ ≃ₗ[R] LinearMap.ker fₛ :=
      { toFun := fun y ↦ ⟨y.1, y.2⟩
        invFun := fun y ↦ ⟨y.1, y.2⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have := LinearMap.toKerLocalized_isLocalizedModule (Localization S) S ℓ g f
    have : IsLocalizedModule S (e.toLinearMap ∘ₗ LinearMap.toKerIsLocalized S ℓ g f) :=
      IsLocalizedModule.of_linearEquiv S _ e
    exact .step (LocalizedModule S F) fₛ hsurj
      (ih (e.toLinearMap ∘ₗ LinearMap.toKerIsLocalized S ℓ g f))

/-- Over a Noetherian ring, free `n`-th syzygies of a finitely generated module give a finite free
resolution of length `n`. -/
theorem dcl_SyzFree.hasFFR {R : Type u} [CommRing R] [IsNoetherianRing R] :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      dcl_SyzFree R n M → dcl_HasFFR R n M
  | 0, M, _, _, _, h => by
    unfold dcl_SyzFree at h
    exact .free
  | n + 1, M, _, _, _, h => by
    unfold dcl_SyzFree at h
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    exact .step (Fin k → R) f hf (dcl_SyzFree.hasFFR n (LinearMap.ker f) (h k f hf))

end Resolution

section Invertible

variable {B : Type u} [CommRing B] [IsDomain B]

/-- A nonzero finitely generated ideal of a domain, principal near every maximal ideal, is a unit
fractional ideal: `I · (1 / I) = 1`. -/
theorem dcl_one_le_mul_div (I : Ideal B) (hfg : I.FG) (hI : I ≠ ⊥)
    (hloc : ∀ Q : Ideal B, Q.IsMaximal → ∃ a ∈ I, ∀ i ∈ I, ∃ s ∉ Q, s * i ∈ Ideal.span {a}) :
    let K := FractionRing B
    let I' : Submodule B K := Submodule.map (Algebra.linearMap B K) I
    I' * (1 / I') = 1 := by
  intro K I'
  classical
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro y hy k hk
    rw [Submodule.mem_div_iff_forall_mul_mem] at hk
    simpa [mul_comm] using hk y hy
  · let T : Ideal B := Submodule.comap (Algebra.linearMap B K) (I' * (1 / I'))
    suffices hT : T = ⊤ by
      intro x hx
      obtain ⟨b, rfl⟩ := (Submodule.mem_one).mp hx
      have hb : b ∈ T := hT ▸ Submodule.mem_top
      exact hb
    by_contra hT
    obtain ⟨Q, hQ, hTQ⟩ := Ideal.exists_le_maximal T hT
    obtain ⟨a, haI, ha⟩ := hloc Q hQ
    obtain ⟨G, hG⟩ := hfg
    have hs : ∀ g ∈ G, ∃ s ∉ Q, s * g ∈ Ideal.span {a} := fun g hg ↦
      ha g (hG ▸ Ideal.subset_span hg)
    choose! sg hsgQ hsg using hs
    let s := ∏ g ∈ G, sg g
    have hsQ : s ∉ Q := by
      simpa [s] using (Ideal.IsPrime.prod_mem_iff (hp := hQ.isPrime)).not.mpr
        (by push Not; exact fun g hg ↦ hsgQ g hg)
    have hsI : ∀ i ∈ I, s * i ∈ Ideal.span {a} := by
      intro i hi
      rw [← hG] at hi
      refine Submodule.span_induction (fun g hg ↦ ?_) (by simp) (fun x y _ _ hx hy ↦ ?_)
        (fun r x _ hx ↦ ?_) hi
      · have : s = (∏ g' ∈ G.erase g, sg g') * sg g := (Finset.prod_erase_mul _ _ hg).symm
        rw [this, mul_assoc]
        exact Ideal.mul_mem_left _ _ (hsg g hg)
      · rw [mul_add]; exact Ideal.add_mem _ hx hy
      · rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hI
      rw [eq_bot_iff]
      intro i hi
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hsI i hi)
      rw [Ideal.mem_bot]
      have : s * i = 0 := by rw [← hr, mul_zero]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (h ▸ Q.zero_mem) hsQ
      · exact h
    let k : K := algebraMap B K s / algebraMap B K a
    have hk : k ∈ 1 / I' := by
      rw [Submodule.mem_div_iff_forall_mul_mem]
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hsI i hi)
      refine ⟨r, ?_⟩
      have hane : algebraMap B K a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr ha0
      simp only [Algebra.linearMap_apply, k]
      rw [div_mul_eq_mul_div, eq_div_iff hane, LinearMap.toSpanSingleton_apply, Algebra.smul_def,
        mul_one, ← map_mul, ← map_mul, hr]
    have hmem : algebraMap B K a * k ∈ I' * (1 / I') :=
      Submodule.mul_mem_mul (Submodule.mem_map_of_mem haI) hk
    have hak : algebraMap B K a * k = algebraMap B K s := by
      have hane : algebraMap B K a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr ha0
      simp only [k]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hane]
    rw [hak] at hmem
    exact hsQ (hTQ hmem)

/-- A nonzero finitely generated ideal of a domain that is principal near every maximal ideal is
an invertible module. -/
theorem dcl_invertible_of_locally_principal (I : Ideal B) (hfg : I.FG) (hI : I ≠ ⊥)
    (hloc : ∀ Q : Ideal B, Q.IsMaximal → ∃ a ∈ I, ∀ i ∈ I, ∃ s ∉ Q, s * i ∈ Ideal.span {a}) :
    Module.Invertible B I := by
  let K := FractionRing B
  let I' : Submodule B K := Submodule.map (Algebra.linearMap B K) I
  have h : I' * (1 / I') = 1 := dcl_one_le_mul_div I hfg hI hloc
  let u : (Submodule B K)ˣ := Units.mkOfMulEqOne I' (1 / I') h
  have hu : Module.Invertible B (u : Submodule B K) := inferInstance
  change Module.Invertible B I' at hu
  exact Module.Invertible.congr (Submodule.equivMapOfInjective (Algebra.linearMap B K)
    (IsFractionRing.injective B K) I).symm

end Invertible

section Factorial

/-- Localizations of a regular ring at primes are regular rings. -/
theorem dcl_isRegularRing_localization {A : Type u} [CommRing A] [IsRegularRing A]
    (M : Submonoid A) : IsRegularRing (Localization M) := by
  have : IsNoetherianRing (Localization M) := IsLocalization.isNoetherianRing M _ inferInstance
  rw [isRegularRing_iff]
  intro Q _
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv
    (Q.comap (algebraMap A (Localization M))).primeCompl
    (Localization.AtPrime (Q.comap (algebraMap A (Localization M))))
    (Localization.AtPrime Q)).toRingEquiv


/-- A free ideal of rank one is principal. -/
theorem dcl_isPrincipal_of_linearEquiv {B : Type u} [CommRing B] (I : Ideal B)
    (e : I ≃ₗ[B] B) : I.IsPrincipal := by
  refine ⟨⟨(e.symm 1 : B), ?_⟩⟩
  apply le_antisymm
  · intro p hp
    rw [Submodule.mem_span_singleton]
    refine ⟨e ⟨p, hp⟩, ?_⟩
    have : e.symm (e ⟨p, hp⟩ • 1) = ⟨p, hp⟩ := by rw [smul_eq_mul, mul_one, e.symm_apply_apply]
    rw [map_smul] at this
    exact congrArg Subtype.val this
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (e.symm 1).2

/-- If every localization at a maximal ideal is factorial, a height-one prime is principal near
every maximal ideal. -/
theorem dcl_locally_principal {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (hB : ∀ (Q : Ideal B) [Q.IsMaximal], UniqueFactorizationMonoid (Localization.AtPrime Q))
    (P : Ideal B) [P.IsPrime] (hP : P.height = 1) (Q : Ideal B) (hQ : Q.IsMaximal) :
    ∃ a ∈ P, ∀ i ∈ P, ∃ s ∉ Q, s * i ∈ Ideal.span {a} := by
  by_cases hPQ : P ≤ Q
  · have := hB Q
    let BQ := Localization.AtPrime Q
    have hdisj : Disjoint (Q.primeCompl : Set B) (P : Set B) := by
      rw [Set.disjoint_left]
      intro y hy hyP
      exact hy (hPQ hyP)
    have hprime : (P.map (algebraMap B BQ)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl BQ P inferInstance hdisj
    have hheight : (P.map (algebraMap B BQ)).height = 1 := by
      rw [IsLocalization.height_map_of_disjoint Q.primeCompl P hdisj, hP]
    obtain ⟨g, hg⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight
    have hgmem : g ∈ P.map (algebraMap B BQ) := by
      rw [hg]; exact Submodule.mem_span_singleton_self g
    obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl BQ).mp hgmem
    refine ⟨a, a.2, fun i hi ↦ ?_⟩
    have himem : algebraMap B BQ i ∈ P.map (algebraMap B BQ) := Ideal.mem_map_of_mem _ hi
    rw [hg, Submodule.mem_span_singleton] at himem
    obtain ⟨c, hc⟩ := himem
    obtain ⟨⟨r, w⟩, hrw⟩ := IsLocalization.surj Q.primeCompl c
    -- `i * w * t = r * a` in `BQ`
    have heq : algebraMap B BQ (i * (w * t)) = algebraMap B BQ (r * a) := by
      simp only [map_mul]
      rw [← hc, smul_eq_mul]
      simp only at hat hrw
      rw [← hrw, ← hat]
      ring
    obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists Q.primeCompl BQ).mp heq
    refine ⟨u * (w * t), ?_, ?_⟩
    · exact Q.primeCompl.mul_mem u.2 (Q.primeCompl.mul_mem w.2 t.2)
    · rw [Ideal.mem_span_singleton]
      exact ⟨u * r, by linear_combination hu⟩
  · obtain ⟨a, haP, haQ⟩ := Set.not_subset.mp hPQ
    exact ⟨a, haP, fun i _ ↦ ⟨a, haQ, Ideal.mem_span_singleton.mpr ⟨i, by ring⟩⟩⟩

/-- A finite free resolution of an ideal localizes to one of its extension. -/
theorem dcl_hasFFR_map {A : Type u} [CommRing A] (S : Submonoid A) (P : Ideal A) {n : ℕ}
    (h : dcl_HasFFR A n P) :
    dcl_HasFFR (Localization S) n (P.map (algebraMap A (Localization S))) := by
  have heq : Submodule.localized' (Localization S) S (Algebra.linearMap A (Localization S)) P =
      P.map (algebraMap A (Localization S)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  let e := (LinearEquiv.ofEq _ _ heq).restrictScalars A
  have : IsLocalizedModule S (e.toLinearMap ∘ₗ
      Submodule.toLocalized' (Localization S) S (Algebra.linearMap A (Localization S)) P) :=
    IsLocalizedModule.of_linearEquiv S _ e
  exact h.localization S (e.toLinearMap ∘ₗ
      Submodule.toLocalized' (Localization S) S (Algebra.linearMap A (Localization S)) P)

/-- **Auslander–Buchsbaum.** A Noetherian local ring whose localizations at primes are all
regular local rings is a unique factorization domain. -/
theorem dcl_ufd_of_isRegularRing : ∀ (n : ℕ) (A : Type u) [CommRing A] [IsLocalRing A]
    [IsRegularRing A], ringKrullDim A ≤ n → UniqueFactorizationMonoid A := by
  intro n
  induction n with
  | zero =>
    intro A _ _ _ hle
    have := IsRegularLocalRing.of_isRegularRing_of_isLocalRing A
    rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
    intro p _ h1
    have := (Ideal.height_le_ringKrullDim_of_isPrime (I := p)).trans hle
    rw [h1] at this
    exact absurd this (by decide)
  | succ n ih =>
    intro A _ _ _ hle
    have := IsRegularLocalRing.of_isRegularRing_of_isLocalRing A
    by_cases hn : ringKrullDim A ≤ n
    · exact ih A hn
    have hdim : ringKrullDim A = (n + 1 : ℕ) := by
      obtain ⟨e, he⟩ := dcl_exists_ringKrullDim_eq_natCast A
      rw [he] at hle hn ⊢
      have h1 : e ≤ n + 1 := by exact_mod_cast hle
      have h2 : ¬ e ≤ n := fun h ↦ hn (by exact_mod_cast h)
      exact_mod_cast (by omega : e = n + 1)
    obtain ⟨x, hx, hx2, hxR, hq, hqdim⟩ := dcl_exists_quotient_regular hdim
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx2 (Submodule.zero_mem _)
    have hxp : Prime x := (Ideal.span_singleton_prime hx0).mp
      ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)
    rw [UniqueFactorizationMonoid.iff_localizationAway_of_prime hxp]
    let B := Localization.Away x
    have : IsDomain B := IsLocalization.Away.isDomain B hx0
    have : IsNoetherianRing B :=
      IsLocalization.isNoetherianRing (Submonoid.powers x) B inferInstance
    rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
    intro P' _ h1
    have hB : ∀ (Q : Ideal B) [Q.IsMaximal],
        UniqueFactorizationMonoid (Localization.AtPrime Q) := by
      intro Q _
      let q := Q.comap (algebraMap A B)
      have hxq : x ∉ q := by
        intro h
        exact (inferInstance : Q.IsMaximal).ne_top
          (Ideal.eq_top_of_isUnit_mem Q h (IsLocalization.Away.algebraMap_isUnit (S := B) x))
      have hqm : q < maximalIdeal A :=
        lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
          (fun h ↦ hxq (h ▸ hx))
      have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime hqm
      have hm : ((maximalIdeal A).height : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
        rw [maximalIdeal_height_eq_ringKrullDim, hdim]
      have hm' : (maximalIdeal A).height = ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast hm
      rw [hm'] at hlt
      have hqdim : ringKrullDim (Localization.AtPrime q) ≤ n := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height q]
        have : q.height ≤ n := by
          exact Order.le_of_lt_add_one (by exact_mod_cast hlt)
        exact_mod_cast this
      have := dcl_isRegularRing_localization q.primeCompl
      have hufd : UniqueFactorizationMonoid (Localization.AtPrime q) := ih _ hqdim
      let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (Localization.AtPrime Q)
      exact e.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid hufd
    have hP'0 : P' ≠ ⊥ := Ideal.ne_bot_of_height_eq_one h1
    have hinv : Module.Invertible B P' :=
      dcl_invertible_of_locally_principal P' (IsNoetherian.noetherian P') hP'0
        (fun Q hQ ↦ dcl_locally_principal hB P' h1 Q hQ)
    let P := P'.comap (algebraMap A B)
    have hffr := dcl_SyzFree.hasFFR (n + 1) P (dcl_syzFree_of_isRegularLocalRing (n + 1) A hdim P)
    have hffr' := dcl_hasFFR_map (Submonoid.powers x) P hffr
    have hmap : P.map (algebraMap A B) = P' := IsLocalization.map_under (Submonoid.powers x) B P'
    rw [hmap] at hffr'
    have := hffr'.isStablyFree inferInstance
    have := Module.free_of_isStablyFree_of_invertible B P'
    obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := B) (M := P')).mp this
    exact dcl_isPrincipal_of_linearEquiv P' e

/-- The localization of a regular ring at a prime is factorial. -/
theorem dcl_ufd_localization_atPrime {A : Type u} [CommRing A] [IsRegularRing A] (q : Ideal A)
    [q.IsPrime] : UniqueFactorizationMonoid (Localization.AtPrime q) := by
  have := dcl_isRegularRing_localization (A := A) q.primeCompl
  have := IsRegularLocalRing.of_isRegularRing_of_isLocalRing (Localization.AtPrime q)
  obtain ⟨n, hn⟩ := dcl_exists_ringKrullDim_eq_natCast (Localization.AtPrime q)
  exact dcl_ufd_of_isRegularRing n _ hn.le

end Factorial

end HodgeLean.Foundations
