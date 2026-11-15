import HodgeLean.Foundations.CMLieBlocksDefs
import HodgeLean.Adapters.PowersVocabulary

/-! # Proofs for the `Lie(G_k)_ℂ` block-form spec (stage A2b)

The agent's working file. Fill every proof hole. **Do not change the statement of
any `_aux` theorem**: `CMLieBlocks.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files; prefix them `a2b_`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations
open NumberField

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

section General

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- The complexification of a kernel, computed through an injective comparison map. -/
theorem a2b_complexSpan_ker [FiniteDimensional ℚ V] {M M' : Type*} [AddCommGroup M]
    [Module ℚ M] [AddCommGroup M'] [Module ℂ M'] (f : Module.End ℚ V →ₗ[ℚ] M)
    (g : Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ] M') (ψ : ℂ ⊗[ℚ] M →ₗ[ℂ] M') (hψ : Function.Injective ψ)
    (h : ∀ X, g (X.baseChange ℂ) = ψ (1 ⊗ₜ f X)) :
    complexSpan (LinearMap.ker f) = LinearMap.ker g := by
  have key : ∀ y, ψ (f.baseChange ℂ y) = g (endBaseChangeEquiv V y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul z X =>
      rw [LinearMap.baseChange_tmul, endBaseChangeEquiv_apply, tensorProductEnd_tmul, map_smul, h,
        ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  ext c
  rw [mem_complexSpan_iff, ← ker_baseChange_eq, LinearMap.mem_ker, LinearMap.mem_ker,
    ← hψ.eq_iff, map_zero, key, LinearEquiv.apply_symm_apply]

/-- The commutator map `X ↦ X T - T X`.
Source: constructed here; the same map as the private `eqwACommMap` (`Foundations/EQWCoreProofs.lean`). -/
abbrev a2bCommMap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T : Module.End K W) : Module.End K W →ₗ[K] Module.End K W :=
  LinearMap.mulRight K T - LinearMap.mulLeft K T

example (T X : Module.End ℚ V) : a2bCommMap T X = X * T - T * X := rfl

theorem a2b_mem_ker_commMap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T X : Module.End K W) : X ∈ LinearMap.ker (a2bCommMap T) ↔ X * T = T * X := by
  simp [a2bCommMap, sub_eq_zero]

theorem a2b_complexSpan_ker_commMap [FiniteDimensional ℚ V] (T : Module.End ℚ V) :
    complexSpan (LinearMap.ker (a2bCommMap T)) =
      LinearMap.ker (a2bCommMap (T.baseChange ℂ)) := by
  refine a2b_complexSpan_ker _ _ (endBaseChangeEquiv V).toLinearMap
    (endBaseChangeEquiv V).injective fun X => ?_
  simp only [a2bCommMap, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe, endBaseChangeEquiv_apply, tensorProductEnd_one_tmul,
    LinearMap.baseChange_sub, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

theorem a2b_complexSpan_finsetInf [FiniteDimensional ℚ V] {κ : Type*}
    (s : Finset κ) (W : κ → Submodule ℚ (Module.End ℚ V)) :
    complexSpan (s.inf W) = s.inf fun i => complexSpan (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using complexSpan_top
  | insert i s _ ih => rw [Finset.inf_insert, Finset.inf_insert, complexSpan_inf, ih]

theorem spec_a2b_mem_complexSpan_gkLie_iff_aux [FiniteDimensional ℚ V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule ↔
      (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) ∧
      (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) X = 0 ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) ((ι u).baseChange ℂ * X) = 0 := by
  let R : Submodule ℚ (Module.End ℚ V) := Subalgebra.toSubmodule ι.range
  let b := Module.finBasis ℚ R
  -- membership in the span of the basis
  have hspan : ∀ {P : Module.End ℚ V → Prop}, P 0 → (∀ S T, P S → P T → P (S + T)) →
      (∀ (q : ℚ) S, P S → P (q • S)) → (∀ i, P (b i)) → ∀ r ∈ R, P r := by
    intro P h0 hadd hsmul hb r hr
    have hr' : (⟨r, hr⟩ : R) ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    have := Submodule.span_induction (p := fun (s : R) _ => P s)
      (by rintro _ ⟨i, rfl⟩; exact hb i) h0 (fun s t _ _ hs ht => hadd s t hs ht)
      (fun q s _ hs => hsmul q s hs) hr'
    exact this
  have hgk : (gkLie E ι.range (ι u)).toSubmodule = (weilSU E (ι u)).toSubmodule ⊓
      Finset.univ.inf fun i => LinearMap.ker (a2bCommMap ((b i : R) : Module.End ℚ V)) := by
    ext Y
    simp only [LieSubalgebra.mem_toSubmodule, Submodule.mem_inf, Submodule.mem_finsetInf,
      Finset.mem_univ, true_imp_iff, a2b_mem_ker_commMap]
    refine and_congr_right fun _ => ⟨fun h i => h _ (b i).2, fun h r hr => ?_⟩
    exact hspan (P := fun r => Y * r = r * Y) (by simp)
      (fun S T hS hT => by rw [mul_add, add_mul, hS, hT])
      (fun q S hS => by rw [mul_smul_comm, smul_mul_assoc, hS]) h r hr
  rw [hgk, complexSpan_inf, a2b_complexSpan_finsetInf, Submodule.mem_inf,
    spec_eqw_mem_complexSpan_weilSU_iff, Submodule.mem_finsetInf]
  simp only [Finset.mem_univ, true_imp_iff, a2b_complexSpan_ker_commMap, a2b_mem_ker_commMap]
  constructor
  · rintro ⟨⟨-, h2, h3, h4⟩, h1⟩
    refine ⟨fun a => ?_, h2, h3, h4⟩
    refine hspan (P := fun r => X * r.baseChange ℂ = r.baseChange ℂ * X) (by simp)
      (fun S T hS hT => by rw [LinearMap.baseChange_add, mul_add, add_mul, hS, hT])
      (fun q S hS => ?_) h1 (ι a) ⟨a, rfl⟩
    rw [LinearMap.baseChange_smul, mul_smul_comm, smul_mul_assoc, hS]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1 u, h2, h3, h4⟩, fun i => ?_⟩
    obtain ⟨a, ha⟩ := (b i).2
    rw [← ha]
    exact h1 a

end General

section NumberField

variable {L : Type*} [Field L] [NumberField L] [FiniteDimensional ℚ V]

omit [FiniteDimensional ℚ V] in
theorem a2b_mem_of_commute (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ cmEigenspace ι τ) : X x ∈ cmEigenspace ι τ := by
  simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
  intro a
  rw [← Module.End.mul_apply, ← hX a, Module.End.mul_apply, hx a, map_smul]

theorem a2b_cmProjection_of_mem (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    {y : ℂ ⊗[ℚ] V} (hy : y ∈ cmEigenspace ι τ) : cmProjection ι τ y = ⟨y, hy⟩ := by
  classical
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_same
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩) ⟨y, hy⟩

theorem spec_a2b_cmBlock_apply_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (x : cmEigenspace ι τ) :
    ((cmBlock ι τ X x : cmEigenspace ι τ) : ℂ ⊗[ℚ] V) = X x := by
  change ((cmProjection ι τ (X x) : cmEigenspace ι τ) : ℂ ⊗[ℚ] V) = X x
  rw [a2b_cmProjection_of_mem ι τ (a2b_mem_of_commute ι τ X hX x.2)]

theorem spec_a2b_cmBlock_mul_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hY : ∀ a : L, Y * (ι a).baseChange ℂ = (ι a).baseChange ℂ * Y) :
    cmBlock ι τ (X * Y) = cmBlock ι τ X * cmBlock ι τ Y := by
  ext x
  change ((cmProjection ι τ (X (Y x)) : cmEigenspace ι τ) : ℂ ⊗[ℚ] V) =
    ((cmProjection ι τ (X ((cmBlock ι τ Y x : cmEigenspace ι τ) : ℂ ⊗[ℚ] V)) :
      cmEigenspace ι τ) : ℂ ⊗[ℚ] V)
  rw [spec_a2b_cmBlock_apply_aux ι τ Y hY x]

theorem spec_a2b_contragredient_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (τ : L →ₐ[ℚ] ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
        (cmEigenspace ι (cmConjEmbedding τ)) ∘ₗ cmBlock ι (cmConjEmbedding τ) X =
      SchurWeyl.dualLie ℂ (cmEigenspace ι τ) (cmBlock ι τ X) ∘ₗ
        WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
          (cmEigenspace ι (cmConjEmbedding τ)) := by
  ext y x
  change E.baseChange ℂ x ((cmBlock ι (cmConjEmbedding τ) X y : _) : ℂ ⊗[ℚ] V) =
    -(E.baseChange ℂ ((cmBlock ι τ X x : _) : ℂ ⊗[ℚ] V) y)
  rw [spec_a2b_cmBlock_apply_aux ι _ X hX y, spec_a2b_cmBlock_apply_aux ι τ X hX x, hs, neg_neg]

theorem spec_a2b_finrank_complexSpan_gkLie_of_subsingleton_aux [Subsingleton V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L) :
    Module.finrank ℂ (complexSpan (gkLie E ι.range (ι u)).toSubmodule) = 0 := by
  have _hfin := ‹FiniteDimensional ℚ V›
  exact Module.finrank_zero_of_subsingleton

variable [IsCMField L]

theorem spec_a2b_trace_cmBlock_conj_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ : L →ₐ[ℚ] ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    LinearMap.trace ℂ _ (cmBlock ι (cmConjEmbedding τ) X) =
      -LinearMap.trace ℂ _ (cmBlock ι τ X) := by
  let φ := LinearEquiv.ofBijective _ (spec_a2a_duality_bijective ι E hE hRos τ)
  have h4 := spec_a2b_contragredient_aux ι E τ X hX hs
  have hconj : cmBlock ι (cmConjEmbedding τ) X =
      φ.symm.conj (SchurWeyl.dualLie ℂ (cmEigenspace ι τ) (cmBlock ι τ X)) := by
    apply LinearMap.ext
    intro y
    apply φ.injective
    rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun h4 y
  rw [hconj, LinearMap.trace_conj', SchurWeyl.dualLie_apply, map_neg]
  exact congrArg Neg.neg (LinearMap.trace_transpose' _)

theorem a2b_omegaC_sq {d : ℚ} (hd : 0 < d) :
    HodgeBlocks.WeilAction.omegaC d ^ 2 = -(d : ℂ) := by
  have h : ((Real.sqrt (d : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hd.le), Complex.ofReal_ratCast]
  rw [HodgeBlocks.WeilAction.omegaC, mul_pow, Complex.I_sq, h, neg_one_mul]

theorem a2b_conj_omegaC (d : ℚ) :
    starRingEnd ℂ (HodgeBlocks.WeilAction.omegaC d) = -HodgeBlocks.WeilAction.omegaC d := by
  rw [HodgeBlocks.WeilAction.omegaC, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

omit [IsCMField L] in
theorem a2b_cmConjEmbedding_involutive :
    Function.Involutive (cmConjEmbedding : (L →ₐ[ℚ] ℂ) → (L →ₐ[ℚ] ℂ)) := by
  intro τ
  ext a
  change starRingEnd ℂ (starRingEnd ℂ (τ a)) = τ a
  exact Complex.conj_conj _

omit [IsCMField L] in
theorem a2b_eval_eq_or (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (τ : L →ₐ[ℚ] ℂ) :
    τ u = HodgeBlocks.WeilAction.omegaC d ∨ τ u = -HodgeBlocks.WeilAction.omegaC d := by
  have h1 : τ u ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hu, AlgHom.commutes, map_neg, eq_ratCast]
  have h2 := a2b_omegaC_sq hd
  have h3 : (τ u - HodgeBlocks.WeilAction.omegaC d) *
      (τ u + HodgeBlocks.WeilAction.omegaC d) = 0 := by
    linear_combination h1 - h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem a2b_omegaC_ne_neg {d : ℚ} (hd : 0 < d) :
    HodgeBlocks.WeilAction.omegaC d ≠ -HodgeBlocks.WeilAction.omegaC d := by
  intro h
  have h0 : HodgeBlocks.WeilAction.omegaC d = 0 := by linear_combination h / 2
  have h2 := a2b_omegaC_sq hd
  rw [h0] at h2
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  exact this (by linear_combination h2)

theorem spec_a2b_trace_J_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    LinearMap.trace ℂ (ℂ ⊗[ℚ] V) ((ι u).baseChange ℂ * X) =
      2 * HodgeBlocks.WeilAction.omegaC d *
        ∑ v : cmPlusEmb L u d, LinearMap.trace ℂ _ (cmBlock ι v.1 X) := by
  classical
  have hint : DirectSum.IsInternal (cmEigenspace ι) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩
  have hJX : ∀ a : L, ((ι u).baseChange ℂ * X) * (ι a).baseChange ℂ =
      (ι a).baseChange ℂ * ((ι u).baseChange ℂ * X) := by
    intro a
    rw [mul_assoc, hX a, ← mul_assoc, (a2a_baseChange_commute ι u a).eq, mul_assoc]
  have hmaps : ∀ τ : L →ₐ[ℚ] ℂ, Set.MapsTo ((ι u).baseChange ℂ * X)
      (cmEigenspace ι τ) (cmEigenspace ι τ) :=
    fun τ x hx => a2b_mem_of_commute ι τ _ hJX hx
  have hres : ∀ τ : L →ₐ[ℚ] ℂ, ((ι u).baseChange ℂ * X).restrict (hmaps τ) =
      τ u • cmBlock ι τ X := by
    intro τ
    ext x
    have hXx := a2b_mem_of_commute ι τ X hX x.2
    simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hXx
    change ((ι u).baseChange ℂ * X) (x : ℂ ⊗[ℚ] V) =
      τ u • ((cmBlock ι τ X x : cmEigenspace ι τ) : ℂ ⊗[ℚ] V)
    rw [spec_a2b_cmBlock_apply_aux ι τ X hX x, Module.End.mul_apply, hXx u]
  rw [LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  simp only [hres, map_smul, smul_eq_mul]
  set f : (L →ₐ[ℚ] ℂ) → ℂ := fun τ => τ u * LinearMap.trace ℂ _ (cmBlock ι τ X)
    with hf
  have hconj : ∀ τ : L →ₐ[ℚ] ℂ, cmConjEmbedding τ u = -τ u := by
    intro τ
    change starRingEnd ℂ (τ u) = -τ u
    rcases a2b_eval_eq_or u hd hu τ with h | h
    · rw [h, a2b_conj_omegaC]
    · rw [h, map_neg, a2b_conj_omegaC]
  have hfc : ∀ τ, f (cmConjEmbedding τ) = f τ := by
    intro τ
    simp only [hf, hconj, spec_a2b_trace_cmBlock_conj_aux ι E hE hRos τ X hX hs, neg_mul_neg]
  have h1 : ∑ τ, f τ = ∑ τ, (if τ u = HodgeBlocks.WeilAction.omegaC d then f τ else 0) +
      ∑ τ, (if τ u = HodgeBlocks.WeilAction.omegaC d then 0 else f τ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp
  have h2 : ∑ τ, (if τ u = HodgeBlocks.WeilAction.omegaC d then 0 else f τ) =
      ∑ τ, (if τ u = HodgeBlocks.WeilAction.omegaC d then f τ else 0) := by
    refine Fintype.sum_equiv (a2b_cmConjEmbedding_involutive.toPerm _) _ _ fun τ => ?_
    simp only [Function.Involutive.coe_toPerm, hconj]
    have hne := (a2b_omegaC_ne_neg hd).symm
    rcases a2b_eval_eq_or u hd hu τ with h | h
    · simp only [h, hne, ite_true, ite_false]
    · simp only [h, neg_neg, hne, ite_true, ite_false, hfc]
  have h3 : ∑ τ, (if τ u = HodgeBlocks.WeilAction.omegaC d then f τ else 0) =
      ∑ v : cmPlusEmb L u d, f v.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun τ => by simp) f
  change ∑ τ, f τ = _
  rw [h1, h2, h3, ← two_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [hf, v.2]
  ring

theorem spec_a2b_cmBlock_mem_traceZero_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule) :
    (fun v : cmPlusEmb L u d => cmBlock ι v.1 X) ∈ cmBlockTraceZero ι u d := by
  obtain ⟨hc, hs, -, htr⟩ := (spec_a2b_mem_complexSpan_gkLie_iff_aux ι E u X).mp hX
  rw [spec_a2b_trace_J_aux ι E hE hRos u hd hu X hc hs] at htr
  have h2 : (2 : ℂ) * HodgeBlocks.WeilAction.omegaC d ≠ 0 :=
    mul_ne_zero two_ne_zero fun h0 => a2b_omegaC_ne_neg hd (by rw [h0, neg_zero])
  have hsum := (mul_eq_zero.mp htr).resolve_left h2
  simpa [cmBlockTraceZero] using hsum

omit [IsCMField L] in
theorem a2b_cmConjEmbedding_cmConjEmbedding (τ : L →ₐ[ℚ] ℂ) :
    cmConjEmbedding (cmConjEmbedding τ) = τ := by
  ext a
  simp [cmConjEmbedding]

omit [IsCMField L] in
/-- Every embedding sends `u` to `i√d` or to `-i√d`. -/
theorem a2b_apply_u_eq (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (τ : L →ₐ[ℚ] ℂ) :
    τ u = HodgeBlocks.WeilAction.omegaC d ∨ τ u = -HodgeBlocks.WeilAction.omegaC d := by
  have h : τ u ^ 2 = HodgeBlocks.WeilAction.omegaC d ^ 2 := by
    rw [HodgeBlocks.WeilAction.omegaC_sq hd, ← map_pow, hu, AlgHom.commutes]
    simp
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

omit [IsCMField L] in
/-- An embedding sends `u` to `i√d` exactly when its conjugate sends `u` to `-i√d`. -/
theorem a2b_cmConjEmbedding_apply_u (u : L) {d : ℚ} (τ : L →ₐ[ℚ] ℂ)
    (h : τ u = -HodgeBlocks.WeilAction.omegaC d) :
    cmConjEmbedding τ u = HodgeBlocks.WeilAction.omegaC d := by
  change starRingEnd ℂ (τ u) = _
  rw [h, map_neg, a2b_conj_omegaC, neg_neg]

theorem spec_a2b_eq_of_cmBlock_eq_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule)
    (hY : Y ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule)
    (h : ∀ v : cmPlusEmb L u d, cmBlock ι v.1 X = cmBlock ι v.1 Y) :
    X = Y := by
  have hZ := sub_mem hX hY
  obtain ⟨hZc, hZs, -, -⟩ := (spec_a2b_mem_complexSpan_gkLie_iff_aux ι E u _).mp hZ
  have hZb : ∀ v : cmPlusEmb L u d, cmBlock ι v.1 (X - Y) = 0 := fun v => by
    rw [map_sub, h v, sub_self]
  have hplus : ∀ τ : L →ₐ[ℚ] ℂ, τ u = HodgeBlocks.WeilAction.omegaC d →
      ∀ x ∈ cmEigenspace ι τ, (X - Y) x = 0 := by
    intro τ hτ x hx
    rw [← spec_a2b_cmBlock_apply_aux ι τ _ hZc ⟨x, hx⟩, hZb ⟨τ, hτ⟩]
    rfl
  have hall : ∀ τ : L →ₐ[ℚ] ℂ, ∀ x ∈ cmEigenspace ι τ, (X - Y) x = 0 := by
    intro τ
    rcases a2b_apply_u_eq u hd hu τ with hτ | hτ
    · exact hplus τ hτ
    · have hσ := a2b_cmConjEmbedding_apply_u u τ hτ
      rw [← a2b_cmConjEmbedding_cmConjEmbedding τ]
      set σ := cmConjEmbedding τ
      have hc := spec_a2b_contragredient_aux ι E σ _ hZc hZs
      rw [hZb ⟨σ, hσ⟩, map_zero, LinearMap.zero_comp] at hc
      intro x hx
      have hx0 : cmBlock ι (cmConjEmbedding σ) (X - Y) ⟨x, hx⟩ = 0 := by
        apply (spec_a2a_duality_bijective ι E hE hRos σ).1
        rw [map_zero]
        exact LinearMap.congr_fun hc ⟨x, hx⟩
      rw [← spec_a2b_cmBlock_apply_aux ι _ _ hZc ⟨x, hx⟩, hx0]
      rfl
  have hker : LinearMap.ker (X - Y) = ⊤ := by
    rw [eq_top_iff, ← spec_a2a_iSup_eq_top ι]
    exact iSup_le fun τ x hx => hall τ x hx
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp hker)

omit [IsCMField L] in
theorem a2b_isInternal (ι : L →ₐ[ℚ] Module.End ℚ V) [DecidableEq (L →ₐ[ℚ] ℂ)] :
    DirectSum.IsInternal (cmEigenspace ι) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩

omit [IsCMField L] in
theorem a2b_cmProjection_of_mem_b (ι : L →ₐ[ℚ] Module.End ℚ V) {σ : L →ₐ[ℚ] ℂ}
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ cmEigenspace ι σ) :
    cmProjection ι σ x = ⟨x, hx⟩ := by
  classical
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem (a2b_isInternal ι) hx

omit [IsCMField L] in
theorem a2b_cmProjection_of_mem_ne (ι : L →ₐ[ℚ] Module.End ℚ V) {σ τ : L →ₐ[ℚ] ℂ}
    (h : σ ≠ τ) {x : ℂ ⊗[ℚ] V} (hx : x ∈ cmEigenspace ι σ) :
    cmProjection ι τ x = 0 := by
  classical
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne (a2b_isInternal ι) h hx

omit [IsCMField L] in
/-- Two linear maps out of `ℂ ⊗ V` that agree on every `W_τ` are equal. -/
theorem a2b_linearMap_ext (ι : L →ₐ[ℚ] Module.End ℚ V) {N : Type*} [AddCommGroup N]
    [Module ℂ N] {f g : (ℂ ⊗[ℚ] V) →ₗ[ℂ] N}
    (h : ∀ τ : L →ₐ[ℚ] ℂ, ∀ x ∈ cmEigenspace ι τ, f x = g x) : f = g := by
  have hker : LinearMap.ker (f - g) = ⊤ := by
    rw [eq_top_iff, ← spec_a2a_iSup_eq_top ι]
    exact iSup_le fun τ x hx => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, h τ x hx, sub_self]
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp hker)

omit [FiniteDimensional ℚ V] [IsCMField L] in
theorem a2b_mem_cmEigenspace_iff (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (x : ℂ ⊗[ℚ] V) :
    x ∈ cmEigenspace ι τ ↔ ∀ a : L, (ι a).baseChange ℂ x = τ a • x := by
  simp [cmEigenspace]

omit [IsCMField L] in
/-- For `X` commuting with `ι(L)_ℂ`, `tr X = Σ_τ tr X_τ`. -/
theorem a2b_trace_eq_sum_cmBlock (ι : L →ₐ[ℚ] Module.End ℚ V) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) :
    LinearMap.trace ℂ _ X = ∑ τ : L →ₐ[ℚ] ℂ, LinearMap.trace ℂ _ (cmBlock ι τ X) := by
  classical
  have hmaps : ∀ τ : L →ₐ[ℚ] ℂ, Set.MapsTo X (cmEigenspace ι τ) (cmEigenspace ι τ) :=
    fun τ x hx => by
      rw [← spec_a2b_cmBlock_apply_aux ι τ X hX ⟨x, hx⟩]
      exact Submodule.coe_mem _
  rw [LinearMap.trace_eq_sum_trace_restrict (a2b_isInternal ι) hmaps]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext x
  rw [spec_a2b_cmBlock_apply_aux ι τ X hX]
  rfl

/-- For `X` commuting with `ι(L)_ℂ` and `E`-skew, `tr X = 0`: the blocks at `τ` and `τ̄` have
opposite traces. -/
theorem a2b_trace_eq_zero (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) :
    LinearMap.trace ℂ _ X = 0 := by
  rw [a2b_trace_eq_sum_cmBlock ι X hX]
  have hinv : Function.Involutive (cmConjEmbedding (L := L)) :=
    a2b_cmConjEmbedding_cmConjEmbedding
  have h : ∑ τ : L →ₐ[ℚ] ℂ, LinearMap.trace ℂ _ (cmBlock ι (cmConjEmbedding τ) X) =
      ∑ τ : L →ₐ[ℚ] ℂ, LinearMap.trace ℂ _ (cmBlock ι τ X) :=
    Equiv.sum_comp hinv.toPerm (fun τ : L →ₐ[ℚ] ℂ => LinearMap.trace ℂ _ (cmBlock ι τ X))
  rw [Finset.sum_congr rfl fun τ _ => spec_a2b_trace_cmBlock_conj_aux ι E hE hRos τ X hX hs,
    Finset.sum_neg_distrib] at h
  linear_combination -h / 2

/-- The contragredient block: for `σ` and `τ = σ̄`, every `f ∈ 𝔤𝔩(W_σ)` has a `g ∈ 𝔤𝔩(W_τ)` with
`E_ℂ(x, g y) = -E_ℂ(f x, y)`. -/
theorem a2b_exists_contragredient (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (σ τ : L →ₐ[ℚ] ℂ) (hστ : cmConjEmbedding σ = τ) (f : Module.End ℂ (cmEigenspace ι σ)) :
    ∃ g : Module.End ℂ (cmEigenspace ι τ), ∀ (x : cmEigenspace ι σ) (y : cmEigenspace ι τ),
      E.baseChange ℂ x (g y) = -E.baseChange ℂ (f x) y := by
  subst hστ
  let φ := LinearEquiv.ofBijective _ (spec_a2a_duality_bijective ι E hE hRos σ)
  refine ⟨φ.symm.toLinearMap ∘ₗ SchurWeyl.dualLie ℂ _ f ∘ₗ φ.toLinearMap, fun x y => ?_⟩
  exact LinearMap.congr_fun (φ.apply_symm_apply (SchurWeyl.dualLie ℂ _ f (φ y))) x

theorem spec_a2b_exists_of_mem_traceZero_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (Y : ∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1))
    (hY : Y ∈ cmBlockTraceZero ι u d) :
    ∃ X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule,
      ∀ v : cmPlusEmb L u d, cmBlock ι v.1 X = Y v := by
  classical
  set ω := HodgeBlocks.WeilAction.omegaC d with hω
  have hω0 : ω ≠ -ω := by
    intro h
    have h0 : ω = 0 := by linear_combination h / 2
    have h2 := HodgeBlocks.WeilAction.omegaC_sq hd
    rw [← hω, h0] at h2
    have h3 : (d : ℂ) = 0 := by linear_combination h2
    exact hd.ne' (by exact_mod_cast h3)
  have hex : ∀ τ : L →ₐ[ℚ] ℂ, ∃ g : Module.End ℂ (cmEigenspace ι τ),
      (∀ h : τ u = ω, g = Y ⟨τ, h⟩) ∧
      ∀ σ : cmPlusEmb L u d, cmConjEmbedding σ.1 = τ →
        ∀ (x : cmEigenspace ι σ.1) (y : cmEigenspace ι τ),
          E.baseChange ℂ x (g y) = -E.baseChange ℂ (Y σ x) y := by
    intro τ
    by_cases h : τ u = ω
    · refine ⟨Y ⟨τ, h⟩, fun _ => rfl, fun σ hσ => ?_⟩
      exfalso
      have h' : τ u = -ω := by
        rw [← hσ]
        change starRingEnd ℂ (σ.1 u) = _
        rw [σ.2, a2b_conj_omegaC]
      exact hω0 (h.symm.trans h')
    · have h' : τ u = -ω := (a2b_apply_u_eq u hd hu τ).resolve_left h
      let σ₀ : cmPlusEmb L u d := ⟨cmConjEmbedding τ, a2b_cmConjEmbedding_apply_u u τ h'⟩
      obtain ⟨g, hg⟩ := a2b_exists_contragredient ι E hE hRos σ₀.1 τ
        (a2b_cmConjEmbedding_cmConjEmbedding τ) (Y σ₀)
      refine ⟨g, fun h'' => absurd h'' h, fun σ hσ => ?_⟩
      obtain rfl : σ = σ₀ := Subtype.ext (by
        change σ.1 = cmConjEmbedding τ
        rw [← hσ, a2b_cmConjEmbedding_cmConjEmbedding])
      exact hg
  choose B hB1 hB2 using hex
  let X : Module.End ℂ (ℂ ⊗[ℚ] V) :=
    ∑ τ : L →ₐ[ℚ] ℂ, (cmEigenspace ι τ).subtype ∘ₗ B τ ∘ₗ cmProjection ι τ
  have hXapp : ∀ σ x (hx : x ∈ cmEigenspace ι σ), X x = B σ ⟨x, hx⟩ := by
    intro σ x hx
    simp only [X, LinearMap.sum_apply, LinearMap.comp_apply,
      Submodule.subtype_apply]
    rw [Finset.sum_eq_single σ]
    · rw [a2b_cmProjection_of_mem_b ι hx]
    · intro τ _ hτ
      rw [a2b_cmProjection_of_mem_ne ι (Ne.symm hτ) hx, map_zero, Submodule.coe_zero]
    · intro h
      exact absurd (Finset.mem_univ σ) h
  have hXc : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X := by
    intro a
    refine a2b_linearMap_ext ι fun σ x hx => ?_
    have hax := (a2b_mem_cmEigenspace_iff ι σ x).mp hx a
    have hBx := (a2b_mem_cmEigenspace_iff ι σ _).mp (B σ ⟨x, hx⟩).2 a
    rw [Module.End.mul_apply, Module.End.mul_apply, hax, map_smul, hXapp σ x hx, hBx]
  have hblock : ∀ τ, cmBlock ι τ X = B τ := by
    intro τ
    ext x
    change (cmProjection ι τ (X x) : ℂ ⊗[ℚ] V) = _
    rw [hXapp τ x x.2, a2b_cmProjection_of_mem_b ι (B τ x).2]
  have key : ∀ σ ρ : L →ₐ[ℚ] ℂ, ∀ x ∈ cmEigenspace ι σ, ∀ y ∈ cmEigenspace ι ρ,
      E.baseChange ℂ (X x) y + E.baseChange ℂ x (X y) = 0 := by
    intro σ ρ x hx y hy
    rw [hXapp σ x hx, hXapp ρ y hy]
    by_cases hρ : ρ = cmConjEmbedding σ
    · subst hρ
      rcases a2b_apply_u_eq u hd hu σ with hσ | hσ
      · have h1 : E.baseChange ℂ x (B (cmConjEmbedding σ) ⟨y, hy⟩) =
            -E.baseChange ℂ (Y ⟨σ, hσ⟩ ⟨x, hx⟩) y :=
          hB2 _ ⟨σ, hσ⟩ rfl ⟨x, hx⟩ ⟨y, hy⟩
        rw [h1, hB1 σ hσ]
        ring
      · have hρ' := a2b_cmConjEmbedding_apply_u u σ hσ
        have h1 : E.baseChange ℂ y (B σ ⟨x, hx⟩) =
            -E.baseChange ℂ (Y ⟨cmConjEmbedding σ, hρ'⟩ ⟨y, hy⟩) x :=
          hB2 σ ⟨cmConjEmbedding σ, hρ'⟩ (a2b_cmConjEmbedding_cmConjEmbedding σ) ⟨y, hy⟩ ⟨x, hx⟩
        rw [WeilPower.alternating_baseChange_skew (E := E) hAlt _ y,
          WeilPower.alternating_baseChange_skew (E := E) hAlt x, h1, hB1 _ hρ']
        ring
    · rw [spec_a2a_orthogonal ι E hRos σ ρ hρ _ (B σ ⟨x, hx⟩).2 y hy,
        spec_a2a_orthogonal ι E hRos σ ρ hρ x hx _ (B ρ ⟨y, hy⟩).2, add_zero]
  have hXs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y) := by
    have hF : (E.baseChange ℂ).compl₁₂ X LinearMap.id +
        (E.baseChange ℂ).compl₁₂ LinearMap.id X = 0 := by
      refine a2b_linearMap_ext ι fun σ x hx => a2b_linearMap_ext ι fun ρ y hy => ?_
      simpa using key σ ρ x hx y hy
    intro x y
    have := LinearMap.congr_fun₂ hF x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  refine ⟨X, (spec_a2b_mem_complexSpan_gkLie_iff_aux ι E u X).mpr
    ⟨hXc, hXs, a2b_trace_eq_zero ι E hE hRos X hXc hXs, ?_⟩,
    fun v => by rw [hblock, hB1 v.1 v.2]⟩
  have hY' : ∑ v, LinearMap.trace ℂ _ (Y v) = 0 := by simpa [cmBlockTraceZero] using hY
  rw [spec_a2b_trace_J_aux ι E hE hRos u hd hu X hXc hXs,
    Finset.sum_congr rfl fun v _ => by rw [hblock, hB1 v.1 v.2], hY', mul_zero]

omit [FiniteDimensional ℚ V] [IsCMField L] in
/-- The trace functional of `cmBlockTraceZero` on a tuple with one nonzero entry. -/
theorem a2b_sum_trace_single (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ)
    [DecidableEq (cmPlusEmb L u d)] (w : cmPlusEmb L u d)
    (g : Module.End ℂ (cmEigenspace ι w.1)) :
    ∑ v : cmPlusEmb L u d, LinearMap.trace ℂ _
        ((Pi.single (M := fun v : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι v.1)) w g) v) =
      LinearMap.trace ℂ _ g := by
  rw [Finset.sum_eq_single w (fun v _ hv => by rw [Pi.single_eq_of_ne hv, map_zero])
    (fun h => absurd (Finset.mem_univ w) h), Pi.single_eq_same]

theorem spec_a2b_finrank_complexSpan_gkLie_aux [Nontrivial V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    (Module.finrank ℂ (complexSpan (gkLie E ι.range (ι u)).toSubmodule) + 1) *
        (2 * Module.finrank ℚ L) =
      Module.finrank ℚ V ^ 2 := by
  classical
  set S := complexSpan (gkLie E ι.range (ι u)).toSubmodule
  -- the block map is an isomorphism onto the trace-zero tuples
  let Φ : S →ₗ[ℂ] cmBlockTraceZero ι u d :=
    ((LinearMap.pi fun v : cmPlusEmb L u d => cmBlock ι v.1) ∘ₗ S.subtype).codRestrict _
      fun X => spec_a2b_cmBlock_mem_traceZero_aux ι E hE hRos u hd hu X.1 X.2
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro X Y hXY
      apply Subtype.ext
      refine spec_a2b_eq_of_cmBlock_eq_aux ι E hE hRos u hd hu _ _ X.2 Y.2 fun v => ?_
      exact congrFun (congrArg Subtype.val hXY) v
    · rintro ⟨Y, hY⟩
      obtain ⟨X, hX, hXY⟩ := spec_a2b_exists_of_mem_traceZero_aux ι E hE hAlt hRos u hd hu Y hY
      exact ⟨⟨X, hX⟩, Subtype.ext (funext hXY)⟩
  have hS : Module.finrank ℂ S = Module.finrank ℂ (cmBlockTraceZero ι u d) :=
    (LinearEquiv.ofBijective Φ hΦ).finrank_eq
  -- the trace functional is surjective
  set f : (∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1)) →ₗ[ℂ] ℂ :=
    ∑ v : cmPlusEmb L u d, (LinearMap.trace ℂ (cmEigenspace ι v.1)).comp
      (LinearMap.proj (R := ℂ) (φ := fun w : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι w.1))
        v) with hf
  have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hcard : Nat.card (cmPlusEmb L u d) * 2 = Module.finrank ℚ L := spec_a2a_card_plus u hd hu
  have hm : ∀ v : cmPlusEmb L u d, Module.finrank ℂ (cmEigenspace ι v.1) * Module.finrank ℚ L =
      Module.finrank ℚ V := fun v => spec_a2a_finrank ι v.1
  have hne : Nonempty (cmPlusEmb L u d) := by
    have h0 : 0 < Nat.card (cmPlusEmb L u d) := by omega
    exact (Nat.card_pos_iff.mp h0).1
  obtain ⟨v₀⟩ := hne
  have hV : 0 < Module.finrank ℚ V := Module.finrank_pos
  have hm₀ : (Module.finrank ℂ (cmEigenspace ι v₀.1) : ℂ) ≠ 0 := by
    have := hm v₀
    norm_cast
    rintro h
    rw [h, zero_mul] at this
    omega
  have hfapply : ∀ Y, f Y = ∑ v, LinearMap.trace ℂ _ (Y v) := fun Y => by
    simp [hf]
  have hY₀ : f (Pi.single v₀ 1) = Module.finrank ℂ (cmEigenspace ι v₀.1) := by
    rw [hfapply, a2b_sum_trace_single, LinearMap.trace_one]
  have hrange : LinearMap.range f = ⊤ := by
    rw [eq_top_iff]
    intro c _
    refine ⟨(c / Module.finrank ℂ (cmEigenspace ι v₀.1)) • Pi.single v₀ 1, ?_⟩
    rw [map_smul, hY₀, smul_eq_mul, div_mul_cancel₀ _ hm₀]
  have hrank := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (V := ∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1)) f
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_pi_fintype] at hrank
  have hker : Module.finrank ℂ (LinearMap.ker f) = Module.finrank ℂ (cmBlockTraceZero ι u d) := rfl
  rw [hker, ← hS] at hrank
  simp only [Module.finrank_linearMap] at hrank
  rw [add_comm _ 1, hrank]
  apply Nat.eq_of_mul_eq_mul_right hn
  rw [Finset.sum_mul, Finset.sum_mul]
  have hterm : ∀ v : cmPlusEmb L u d,
      Module.finrank ℂ (cmEigenspace ι v.1) * Module.finrank ℂ (cmEigenspace ι v.1) *
        (2 * Module.finrank ℚ L) * Module.finrank ℚ L = 2 * Module.finrank ℚ V ^ 2 := by
    intro v
    rw [← hm v]
    ring
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul, ← hcard]
  ring

theorem spec_a2b_exists_trace_cmBlock_ne_zero_aux [Nontrivial V]
    (hL : 4 ≤ Module.finrank ℚ L) (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    ∃ X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule,
      ∃ v : cmPlusEmb L u d, LinearMap.trace ℂ _ (cmBlock ι v.1 X) ≠ 0 := by
  classical
  have hcard : Nat.card (cmPlusEmb L u d) * 2 = Module.finrank ℚ L := spec_a2a_card_plus u hd hu
  have hm : ∀ v : cmPlusEmb L u d, Module.finrank ℂ (cmEigenspace ι v.1) * Module.finrank ℚ L =
      Module.finrank ℚ V := fun v => spec_a2a_finrank ι v.1
  have h1 : 1 < Fintype.card (cmPlusEmb L u d) := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨v, w, hvw⟩ := Fintype.one_lt_card_iff.mp h1
  have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hV : 0 < Module.finrank ℚ V := Module.finrank_pos
  have hvw' : Module.finrank ℂ (cmEigenspace ι v.1) = Module.finrank ℂ (cmEigenspace ι w.1) :=
    Nat.eq_of_mul_eq_mul_right hn ((hm v).trans (hm w).symm)
  let Y : ∀ x : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι x.1) :=
    Pi.single v 1 - Pi.single w 1
  have hY : Y ∈ cmBlockTraceZero ι u d := by
    have h : ∑ x, LinearMap.trace ℂ _ (Y x) = 0 := by
      have hx : ∀ x, LinearMap.trace ℂ _ (Y x) = LinearMap.trace ℂ _
          ((Pi.single (M := fun v : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι v.1)) v 1) x) -
          LinearMap.trace ℂ _
          ((Pi.single (M := fun v : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι v.1)) w 1) x) :=
        fun x => map_sub (LinearMap.trace ℂ (cmEigenspace ι x.1)) _ _
      rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_sub_distrib, a2b_sum_trace_single,
        a2b_sum_trace_single, LinearMap.trace_one, LinearMap.trace_one, hvw', sub_self]
    simpa [cmBlockTraceZero] using h
  obtain ⟨X, hX, hXY⟩ := spec_a2b_exists_of_mem_traceZero_aux ι E hE hAlt hRos u hd hu Y hY
  refine ⟨X, hX, v, ?_⟩
  have hYv : Y v = 1 := by
    change Pi.single (M := fun v : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι v.1)) v 1 v -
      Pi.single (M := fun v : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι v.1)) w 1 v = 1
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hvw]
    exact sub_zero (1 : Module.End ℂ (cmEigenspace ι v.1))
  rw [hXY v, hYv, LinearMap.trace_one]
  have := hm v
  norm_cast
  rintro h
  rw [h, zero_mul] at this
  omega

omit [IsCMField L] in
/-- `π_τ` is the identity on `W_τ`. -/
theorem a2b_cmProjection_of_mem_c (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ cmEigenspace ι τ) :
    ((cmProjection ι τ x : cmEigenspace ι τ) : ℂ ⊗[ℚ] V) = x := by
  classical
  have := DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩) hx
  exact congrArg Subtype.val this

omit [IsCMField L] in
/-- A vector with every component zero is zero. -/
theorem a2b_eq_zero_of_cmProjection (ι : L →ₐ[ℚ] Module.End ℚ V) (z : ℂ ⊗[ℚ] V)
    (h : ∀ τ, cmProjection ι τ z = 0) : z = 0 := by
  classical
  have hI := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
    (cmEigenspace ι)).mpr ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap (cmEigenspace ι)) hI
  have h0 : e.symm z = 0 := DirectSum.ext_component ℂ fun τ => by
    rw [map_zero]; exact h τ
  simpa using congrArg e h0

omit [IsCMField L] in
/-- Taking the `τ`-component commutes with an endomorphism commuting with `ι(L)_ℂ`. -/
theorem a2b_cmProjection_comm (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) (z : ℂ ⊗[ℚ] V) :
    cmProjection ι τ (X z) = cmBlock ι τ X (cmProjection ι τ z) := by
  have hz : z ∈ ⨆ σ : L →ₐ[ℚ] ℂ, cmEigenspace ι σ := by
    rw [spec_a2a_iSup_eq_top ι]; trivial
  refine Submodule.iSup_induction _
    (motive := fun z => cmProjection ι τ (X z) = cmBlock ι τ X (cmProjection ι τ z)) hz
    (fun σ x hx => ?_) (by simp) (fun x y hx hy => by simp only [map_add, hx, hy])
  have hXx : X x ∈ cmEigenspace ι σ := by
    simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro a
    rw [← Module.End.mul_apply, ← hX a, Module.End.mul_apply, hx a, map_smul]
  by_cases hστ : σ = τ
  · subst hστ
    apply Subtype.ext
    rw [a2b_cmProjection_of_mem_c ι σ hXx, spec_a2b_cmBlock_apply_aux ι σ X hX,
      a2b_cmProjection_of_mem_c ι σ hx]
  · rw [a2b_cmProjection_of_mem_ne ι hστ hx, a2b_cmProjection_of_mem_ne ι hστ hXx, map_zero]

omit [IsCMField L] in
theorem a2b_cmConjEmbedding_ne {u : L} {d : ℚ} (hd : 0 < d) (v w : cmPlusEmb L u d) :
    cmConjEmbedding w.1 ≠ v.1 := by
  intro h
  have h1 := congrArg (fun f : L →ₐ[ℚ] ℂ => f u) h
  simp only [cmConjEmbedding, AlgHom.coe_comp, Function.comp_apply] at h1
  change starRingEnd ℂ (w.1 u) = v.1 u at h1
  rw [w.2, v.2, a2b_conj_omegaC] at h1
  exact HodgeBlocks.WeilAction.omegaC_ne_zero hd (by linear_combination -h1 / 2)

omit [IsCMField L] in
/-- Every embedding is some `v` or some `v̄`. -/
theorem a2b_exists_cmPlusEmb {u : L} {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (τ : L →ₐ[ℚ] ℂ) : ∃ v : cmPlusEmb L u d, τ = v.1 ∨ τ = cmConjEmbedding v.1 := by
  have hsq : (τ u - HodgeBlocks.WeilAction.omegaC d) * (τ u + HodgeBlocks.WeilAction.omegaC d)
      = 0 := by
    have h1 : τ u ^ 2 = -(d : ℂ) := by rw [← map_pow, hu, AlgHom.commutes]; simp
    linear_combination h1 - HodgeBlocks.WeilAction.omegaC_sq hd
  rcases mul_eq_zero.mp hsq with h | h
  · exact ⟨⟨τ, sub_eq_zero.mp h⟩, Or.inl rfl⟩
  · refine ⟨⟨cmConjEmbedding τ, ?_⟩, Or.inr (a2b_cmConjEmbedding_cmConjEmbedding τ).symm⟩
    change starRingEnd ℂ (τ u) = _
    rw [eq_neg_of_add_eq_zero_left h, map_neg, a2b_conj_omegaC, neg_neg]

open Classical in
/-- The block decomposition `ℂ ⊗ V → Π_v (W_v × W_v^∨)`, `z ↦ (π_v z, E_ℂ(·, π_v̄ z))`.
Source: PW v0.3, Subsection 2.3 (`V_ℂ = ⊕_v (W_v ⊕ W̄_v)`, `W̄_v ≅ W_v^∨`). -/
def a2b_blockMap (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L) (d : ℚ) :
    (ℂ ⊗[ℚ] V) →ₗ[ℂ] ∀ v : cmPlusEmb L u d,
      cmEigenspace ι v.1 × Module.Dual ℂ (cmEigenspace ι v.1) :=
  LinearMap.pi fun v => (cmProjection ι v.1).prod
    (WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι v.1)
      (cmEigenspace ι (cmConjEmbedding v.1)) ∘ₗ cmProjection ι (cmConjEmbedding v.1))

omit [IsCMField L] in
theorem a2b_blockMap_fst (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L)
    (d : ℚ) (z : ℂ ⊗[ℚ] V) (v : cmPlusEmb L u d) :
    (a2b_blockMap ι E u d z v).1 = cmProjection ι v.1 z := rfl

example (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L) (d : ℚ)
    (v : cmPlusEmb L u d) : (a2b_blockMap ι E u d 0 v).1 = 0 := by
  rw [a2b_blockMap_fst, map_zero]

omit [IsCMField L] in
theorem a2b_blockMap_snd (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L)
    (d : ℚ) (z : ℂ ⊗[ℚ] V) (v : cmPlusEmb L u d) :
    (a2b_blockMap ι E u d z v).2 = WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι v.1)
      (cmEigenspace ι (cmConjEmbedding v.1)) (cmProjection ι (cmConjEmbedding v.1) z) := rfl

omit [IsCMField L] in
open Classical in
theorem a2b_blockMap_of_mem (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    {u : L} {d : ℚ} (hd : 0 < d) (v : cmPlusEmb L u d) (x : cmEigenspace ι v.1) :
    a2b_blockMap ι E u d (x : ℂ ⊗[ℚ] V) = Pi.single v (x, 0) := by
  funext w
  by_cases hw : w = v
  · subst hw
    refine Prod.ext ?_ ?_
    · rw [a2b_blockMap_fst, Pi.single_eq_same]
      exact Subtype.ext (a2b_cmProjection_of_mem_c ι w.1 x.2)
    rw [a2b_blockMap_snd, Pi.single_eq_same]
    rw [a2b_cmProjection_of_mem_ne ι (a2b_cmConjEmbedding_ne hd w w).symm x.2, map_zero]
  · rw [Pi.single_eq_of_ne hw]
    refine Prod.ext ?_ ?_
    · rw [a2b_blockMap_fst]
      exact a2b_cmProjection_of_mem_ne ι (fun h => hw (Subtype.ext h).symm) x.2
    · rw [a2b_blockMap_snd]
      rw [a2b_cmProjection_of_mem_ne ι (a2b_cmConjEmbedding_ne hd v w).symm x.2, map_zero]
      rfl

omit [IsCMField L] in
open Classical in
theorem a2b_blockMap_of_mem_conj (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    {u : L} {d : ℚ} (hd : 0 < d) (v : cmPlusEmb L u d)
    (y : cmEigenspace ι (cmConjEmbedding v.1)) :
    a2b_blockMap ι E u d (y : ℂ ⊗[ℚ] V) =
      Pi.single v (0, WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι v.1)
        (cmEigenspace ι (cmConjEmbedding v.1)) y) := by
  funext w
  by_cases hw : w = v
  · subst hw
    refine Prod.ext ?_ ?_
    · rw [a2b_blockMap_fst, Pi.single_eq_same]
      exact a2b_cmProjection_of_mem_ne ι (a2b_cmConjEmbedding_ne hd w w) y.2
    · rw [a2b_blockMap_snd, Pi.single_eq_same]
      congr 1
      exact Subtype.ext (a2b_cmProjection_of_mem_c ι _ y.2)
  · rw [Pi.single_eq_of_ne hw]
    refine Prod.ext ?_ ?_
    · rw [a2b_blockMap_fst]
      exact a2b_cmProjection_of_mem_ne ι (a2b_cmConjEmbedding_ne hd w v) y.2
    · rw [a2b_blockMap_snd]
      have hne : cmConjEmbedding v.1 ≠ cmConjEmbedding w.1 := fun h => hw (Subtype.ext (by
        simpa [a2b_cmConjEmbedding_cmConjEmbedding] using congrArg cmConjEmbedding h.symm))
      rw [a2b_cmProjection_of_mem_ne ι hne y.2, map_zero]
      rfl

theorem a2b_blockMap_bijective (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    {u : L} {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    Function.Bijective (a2b_blockMap ι E u d) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    rw [Submodule.mem_bot]
    refine a2b_eq_zero_of_cmProjection ι z fun τ => ?_
    obtain ⟨v, rfl | rfl⟩ := a2b_exists_cmPlusEmb hd hu τ
    · exact congrArg Prod.fst (congrFun hz v)
    · apply (spec_a2a_duality_bijective ι E hE hRos v.1).1
      rw [map_zero]
      exact congrArg Prod.snd (congrFun hz v)
  · intro g
    have hg : g = ∑ v : cmPlusEmb L u d,
        (Pi.single v ((g v).1, 0) + Pi.single v (0, (g v).2)) := by
      conv_lhs => rw [← Finset.univ_sum_single g]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Pi.single_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [hg]
    refine ⟨∑ v : cmPlusEmb L u d, (((g v).1 : ℂ ⊗[ℚ] V) +
      (((spec_a2a_duality_bijective ι E hE hRos v.1).2 (g v).2).choose : ℂ ⊗[ℚ] V)), ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_add, a2b_blockMap_of_mem ι E hd, a2b_blockMap_of_mem_conj ι E hd,
      ((spec_a2a_duality_bijective ι E hE hRos v.1).2 (g v).2).choose_spec]

theorem a2b_piLeft_tmul {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] {N : Type*} [AddCommGroup N] [Module ℂ N]
    (g : ∀ i, M i) (n : N) (i : ι) :
    TensorProduct.piLeft ℂ N M (g ⊗ₜ[ℂ] n) i = g i ⊗ₜ[ℂ] n := by
  simp

open Classical in
theorem spec_a2b_powerModel_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) (r : ℕ) :
    ∃ e : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        (∀ v : cmPlusEmb L u d,
          InvariantsExterior.Space ℂ (cmEigenspace ι v.1) (Fin r → ℂ) (Fin r → ℂ)),
      (∀ (v : cmPlusEmb L u d) (x : cmEigenspace ι v.1) (w : Fin r → ℂ),
        e ((WeilPower.powerBaseChange (V := V) r).symm ((x : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
          Pi.single v (x ⊗ₜ[ℂ] w, 0)) ∧
      (∀ (v : cmPlusEmb L u d) (y : cmEigenspace ι (cmConjEmbedding v.1)) (w : Fin r → ℂ),
        e ((WeilPower.powerBaseChange (V := V) r).symm ((y : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
          Pi.single v (0, WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι v.1)
            (cmEigenspace ι (cmConjEmbedding v.1)) y ⊗ₜ[ℂ] w)) ∧
      (∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
        (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) →
        (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) →
        ∀ z (v : cmPlusEmb L u d), e (WeilPower.powerAction r X z) v =
          InvariantsExterior.multiplicityLie ℂ (cmEigenspace ι v.1) (Fin r → ℂ) (Fin r → ℂ)
            (cmBlock ι v.1 X) (e z v)) := by
  set F := LinearEquiv.ofBijective (a2b_blockMap ι E u d) (a2b_blockMap_bijective ι E hE hRos hd hu)
  let e := (WeilPower.powerBaseChange (V := V) r).trans
    ((TensorProduct.congr F (LinearEquiv.refl ℂ (Fin r → ℂ))).trans
      ((TensorProduct.piLeft ℂ (Fin r → ℂ)
        (fun v : cmPlusEmb L u d => cmEigenspace ι v.1 × Module.Dual ℂ (cmEigenspace ι v.1))).trans
        (LinearEquiv.piCongrRight fun v => TensorProduct.prodLeft ℂ ℂ (cmEigenspace ι v.1)
          (Module.Dual ℂ (cmEigenspace ι v.1)) (Fin r → ℂ))))
  have he : ∀ (x : ℂ ⊗[ℚ] V) (w : Fin r → ℂ) (v : cmPlusEmb L u d),
      e ((WeilPower.powerBaseChange (V := V) r).symm (x ⊗ₜ[ℂ] w)) v =
        ((a2b_blockMap ι E u d x v).1 ⊗ₜ[ℂ] w, (a2b_blockMap ι E u d x v).2 ⊗ₜ[ℂ] w) := by
    intro x w v
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.piCongrRight_apply,
      a2b_piLeft_tmul]
    exact TensorProduct.prodLeft_tmul ℂ ℂ _ _ _ _ _ _
  refine ⟨e, fun v x w => ?_, fun v y w => ?_, fun X hX hs z v => ?_⟩
  · funext v'
    rw [he, a2b_blockMap_of_mem ι E hd]
    by_cases hv : v' = v
    · subst hv; simp
    · simp [Pi.single_eq_of_ne hv]
  · funext v'
    rw [he, a2b_blockMap_of_mem_conj ι E hd]
    by_cases hv : v' = v
    · subst hv; simp
    · simp [Pi.single_eq_of_ne hv]
  · obtain ⟨z, rfl⟩ := (WeilPower.powerBaseChange (V := V) r).symm.surjective z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | tmul x w =>
      have hpa : WeilPower.powerAction r X ((WeilPower.powerBaseChange (V := V) r).symm
          (x ⊗ₜ[ℂ] w)) = (WeilPower.powerBaseChange (V := V) r).symm (X x ⊗ₜ[ℂ] w) := by
        simp [WeilPower.powerAction]
      have hc := LinearMap.congr_fun (spec_a2b_contragredient_aux ι E v.1 X hX hs)
        (cmProjection ι (cmConjEmbedding v.1) x)
      simp only [LinearMap.comp_apply] at hc
      rw [hpa, he, he, a2b_blockMap_fst, a2b_blockMap_snd, a2b_blockMap_fst, a2b_blockMap_snd,
        a2b_cmProjection_comm ι _ X hX, a2b_cmProjection_comm ι _ X hX, hc]
      rfl

/-- Complex conjugation preserves the trace `L → ℚ`. -/
theorem a2b_trace_complexConj (x : L) :
    Algebra.trace ℚ L (IsCMField.complexConj L x) = Algebra.trace ℚ L x :=
  Algebra.trace_eq_of_algEquiv
    ((IsCMField.complexConj L : L ≃ₐ[_] L).toRingEquiv.toRatAlgEquiv) x

theorem spec_a2b_cmSymplectic_binders_aux :
    (a2b_cmSymplectic L).Nondegenerate ∧ (a2b_cmSymplectic L).IsAlt ∧
      ∀ (a : L) (x y : L × L),
        a2b_cmSymplectic L (a2a_diagAction L a x) y =
          a2b_cmSymplectic L x (a2a_diagAction L (IsCMField.complexConj L a) y) := by
  have hT := (traceForm_nondegenerate ℚ L).1
  have hTr : ∀ a : L, (∀ z : L, Algebra.trace ℚ L (a * z) = 0) → a = 0 := fun a ha =>
    hT a (fun z => by rw [Algebra.traceForm_apply]; exact ha z)
  set c := IsCMField.complexConj L
  have hcc : ∀ z : L, c (c z) = z := IsCMField.complexConj_apply_apply L
  have happ : ∀ x y : L × L, a2b_cmSymplectic L x y =
      Algebra.trace ℚ L (x.1 * c y.2) - Algebra.trace ℚ L (x.2 * c y.1) := fun _ _ => rfl
  have hTrc : ∀ a : L, (∀ z : L, Algebra.trace ℚ L (a * c z) = 0) → a = 0 := fun a ha =>
    hTr a fun z => by simpa [hcc] using ha (c z)
  have hTrc' : ∀ a : L, (∀ z : L, Algebra.trace ℚ L (z * c a) = 0) → a = 0 := by
    intro a ha
    have : c a = 0 := hTr _ fun z => by simpa [mul_comm] using ha z
    simpa [hcc] using congrArg c this
  refine ⟨⟨fun x hx => ?_, fun y hy => ?_⟩, fun x => ?_, fun a x y => ?_⟩
  · have h1 : x.1 = 0 := hTrc _ fun z => by simpa [happ] using hx (0, z)
    have h2 : x.2 = 0 := hTrc _ fun z => by simpa [happ] using hx (z, 0)
    exact Prod.ext h1 h2
  · have h1 : y.1 = 0 := hTrc' _ fun z => by simpa [happ] using hy (0, z)
    have h2 : y.2 = 0 := hTrc' _ fun z => by simpa [happ] using hy (z, 0)
    exact Prod.ext h1 h2
  · have h := a2b_trace_complexConj (x.2 * c x.1)
    rw [show IsCMField.complexConj L (x.2 * c x.1) = c x.2 * x.1 by
      rw [map_mul]; exact congrArg (c x.2 * ·) (hcc x.1)] at h
    rw [happ, ← h, mul_comm, sub_self]
  · have hd : ∀ (b : L) (z : L × L), a2a_diagAction L b z = (b * z.1, b * z.2) := fun b z => by
      simp [a2a_diagAction]; rfl
    rw [happ, happ, hd, hd]
    simp only [map_mul, hcc, mul_assoc, mul_left_comm a]

end NumberField

section QuadraticSpecialization

variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ V]

/-- A quadratic field containing a root of `X² + 3` is generated by it. -/
theorem a2b_adjoin_eq_top_of_finrank_two (hL : Module.finrank ℚ L = 2) (u : L)
    (hu : u ^ 2 = algebraMap ℚ L (-3)) : Algebra.adjoin ℚ {u} = ⊤ := by
  have hfin : FiniteDimensional ℚ L := Module.finite_of_finrank_eq_succ hL
  have := Subalgebra.isSimpleOrder_of_finrank_prime ℚ L (hL ▸ Nat.prime_two)
  rcases eq_bot_or_eq_top (Algebra.adjoin ℚ {u}) with h | h
  · exfalso
    have hmem : u ∈ (⊥ : Subalgebra ℚ L) := h ▸ Algebra.self_mem_adjoin_singleton ℚ u
    obtain ⟨q, rfl⟩ := Algebra.mem_bot.mp hmem
    rw [← map_pow] at hu
    have hq := (algebraMap ℚ L).injective hu
    nlinarith [sq_nonneg q]
  · exact h

theorem spec_a2b_complexSpan_gkLie_eq_complexSU_aux (hL : Module.finrank ℚ L = 2)
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt) (u : L) (hu : u ^ 2 = algebraMap ℚ L (-3))
    (hJ : (ι u).comp (ι u) = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (ι u x) y = -E x (ι u y)) :
    complexSpan (gkLie E ι.range (ι u)).toSubmodule =
      (WeilPower.complexSU E hE (ι u) hJ hskew).toSubmodule := by
  have hR : ι.range = Algebra.adjoin ℚ {ι u} := by
    rw [← Algebra.map_top, ← a2b_adjoin_eq_top_of_finrank_two hL u hu,
      AlgHom.map_adjoin_singleton]
  rw [hR, HodgeLean.Adapters.spec_pw0_gkLie_adjoin_eq, spec_eqw_complexSpan_weilSU_eq_complexSU E hE hAlt]

end QuadraticSpecialization

end HodgeLean.Foundations
