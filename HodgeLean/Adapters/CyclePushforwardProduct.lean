import HodgeLean.Adapters.CyclePushforwardDefs
import HodgeLean.Foundations.GeometricIntegralitySchemes

/-! # External products of prime cycles over `ℂ`

Helper results for the external product statements of `HodgeLean.Adapters.CyclePushforward`:
tensor products of fields over an algebraically closed field, the degree of a tensor product of
field extensions, and the irreducibility of `pr₁⁻¹(closure {z}) ∩ pr₂⁻¹(closure {w})`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits Module
open scoped MonoidalCategory TensorProduct

namespace HodgeLean.Adapters

universe u

/-- Over an algebraically closed field, the tensor product of two domains is a domain, with no
finiteness hypothesis on either factor: a product of two elements lies in the image of
`A₀ ⊗ B` for a finitely generated subalgebra `A₀`, which injects.
Source: Stacks Project, Tag 05P3 (`isDomain_tensorProduct_of_isAlgClosed` for `A₀`), and
flatness over a field. -/
theorem a1x_isDomain_tensorProduct (k A B : Type*) [Field k] [IsAlgClosed k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [IsDomain A] [IsDomain B] :
    IsDomain (A ⊗[k] B) := by
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨M, hM, hs⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
    ({x, y} : Set (A ⊗[k] B)) (Set.toFinite _)
  obtain ⟨s, hsM⟩ := Submodule.fg_def.mp ((Module.Finite.iff_fg (N := M)).mp hM)
  obtain ⟨t, rfl⟩ := hsM.1.exists_finset_coe
  let A0 : Subalgebra k A := Algebra.adjoin k (t : Set A)
  have : Algebra.FiniteType k A0 :=
    (Subalgebra.fg_iff_finiteType A0).mp (Subalgebra.fg_adjoin_finset t)
  have := HodgeLean.Foundations.isDomain_tensorProduct_of_isAlgClosed k A0 B
  let ι : A0 ⊗[k] B →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.map A0.val (AlgHom.id k B)
  have hι : Function.Injective ι :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := B) A0.val.toLinearMap
      Subtype.val_injective
  have hMA : M ≤ Subalgebra.toSubmodule A0 := by
    rw [← hsM.2]
    exact Submodule.span_le.mpr Algebra.subset_adjoin
  have hr : LinearMap.range (M.subtype.rTensor B) ≤ LinearMap.range ι.toLinearMap := by
    have : M.subtype = A0.val.toLinearMap ∘ₗ Submodule.inclusion hMA := rfl
    rw [this, LinearMap.rTensor_comp]
    refine (LinearMap.range_comp_le_range _ _).trans (le_of_eq ?_)
    rfl
  obtain ⟨x0, hx0⟩ := hr (hs (Set.mem_insert x {y}))
  obtain ⟨y0, hy0⟩ := hr (hs (Set.mem_insert_of_mem x rfl))
  change ι x0 = x at hx0
  change ι y0 = y at hy0
  subst hx0 hy0
  change ι x0 * ι y0 = 0 at hxy
  rw [← map_mul, ← map_zero ι] at hxy
  rcases mul_eq_zero.mp (hι hxy) with h | h
  · left; change ι x0 = 0; rw [h, map_zero]
  · right; change ι y0 = 0; rw [h, map_zero]

/-- Base change of a field extension `K / K'` along `K' ⊗ E`: the rank is unchanged and the
module is free.
Source: Mathlib, `Algebra.IsPushout.tensorProduct_tensorProduct` and `IsBaseChange.finrank_eq`. -/
theorem a1x_finrank_tensor_left (k K' K E : Type*) [Field k] [Field K'] [Field K] [CommRing E]
    [Algebra k K'] [Algebra k K] [Algebra k E] [Algebra K' K] [IsScalarTower k K' K]
    [IsDomain (K' ⊗[k] E)] :
    letI := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K' K)
      (AlgHom.id k E)).toRingHom.toAlgebra
    finrank (K' ⊗[k] E) (K ⊗[k] E) = finrank K' K ∧ Module.Free (K' ⊗[k] E) (K ⊗[k] E) := by
  let _ : Algebra (K' ⊗[k] E) (K ⊗[k] E) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K' K) (AlgHom.id k E)).toRingHom.toAlgebra
  have ht : IsScalarTower K' (K' ⊗[k] E) (K ⊗[k] E) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have h := @Algebra.IsPushout.tensorProduct_tensorProduct k E K' K _ _ _ _ _ _ _ _ _ _ ht
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  exact ⟨h.symm.out.finrank_eq, .of_basis (h.symm.out.basis (Module.Free.chooseBasis K' K))⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The right-hand version of `a1x_finrank_tensor_left`.
Source: Mathlib, `Algebra.IsPushout.comp_iff` and `IsBaseChange.finrank_eq`. -/
theorem a1x_finrank_tensor_right (k E K' K : Type*) [Field k] [Field K'] [Field K] [CommRing E]
    [Algebra k K'] [Algebra k K] [Algebra k E] [Algebra K' K] [IsScalarTower k K' K]
    [IsDomain (E ⊗[k] K')] :
    letI := (Algebra.TensorProduct.map (AlgHom.id k E)
      (IsScalarTower.toAlgHom k K' K)).toRingHom.toAlgebra
    finrank (E ⊗[k] K') (E ⊗[k] K) = finrank K' K ∧ Module.Free (E ⊗[k] K') (E ⊗[k] K) := by
  let _ : Algebra (E ⊗[k] K') (E ⊗[k] K) :=
    (Algebra.TensorProduct.map (AlgHom.id k E) (IsScalarTower.toAlgHom k K' K)).toRingHom.toAlgebra
  let _ : Algebra K' (E ⊗[k] K) :=
    ((algebraMap K (E ⊗[k] K)).comp (algebraMap K' K)).toAlgebra
  have : IsScalarTower k K (E ⊗[k] K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have : IsScalarTower K' K (E ⊗[k] K) := .of_algebraMap_eq fun x => rfl
  have : IsScalarTower K' (E ⊗[k] K') (E ⊗[k] K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower k E (E ⊗[k] K) := inferInstance
  have : IsScalarTower k (E ⊗[k] K') (E ⊗[k] K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower E (E ⊗[k] K') (E ⊗[k] K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower k K' (E ⊗[k] K) := .of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul, ← IsScalarTower.algebraMap_apply]
  have h : Algebra.IsPushout K' K (E ⊗[k] K') (E ⊗[k] K) :=
    (Algebra.IsPushout.comp_iff (R := k) (S := K') (R' := E) (S' := E ⊗[k] K') (T := K)
      (T' := E ⊗[k] K)).mp inferInstance
  exact ⟨h.symm.out.finrank_eq, .of_basis (h.symm.out.basis (Module.Free.chooseBasis K' K))⟩

/-- The degree of `K₁ ⊗ K₂` over `K₁' ⊗ K₂'` is the product of the two degrees (both sides `0`
when either extension is infinite).
Source: Fulton, *Intersection Theory*, second edition, §1.10, proof of Proposition 1.10. -/
theorem a1x_finrank_tensor_map (k K₁' K₁ K₂' K₂ : Type*) [Field k] [Field K₁'] [Field K₁]
    [Field K₂'] [Field K₂] [Algebra k K₁'] [Algebra k K₁] [Algebra k K₂'] [Algebra k K₂]
    [Algebra K₁' K₁] [IsScalarTower k K₁' K₁] [Algebra K₂' K₂] [IsScalarTower k K₂' K₂]
    [IsDomain (K₁' ⊗[k] K₂')] [IsDomain (K₁ ⊗[k] K₂')] :
    letI := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K₁' K₁)
      (IsScalarTower.toAlgHom k K₂' K₂)).toRingHom.toAlgebra
    finrank (K₁' ⊗[k] K₂') (K₁ ⊗[k] K₂) = finrank K₁' K₁ * finrank K₂' K₂ := by
  obtain ⟨h₁, f₁⟩ := a1x_finrank_tensor_left k K₁' K₁ K₂'
  obtain ⟨h₂, f₂⟩ := a1x_finrank_tensor_right k K₁ K₂' K₂
  let _ : Algebra (K₁' ⊗[k] K₂') (K₁ ⊗[k] K₂') := (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k K₁' K₁) (AlgHom.id k K₂')).toRingHom.toAlgebra
  let _ : Algebra (K₁ ⊗[k] K₂') (K₁ ⊗[k] K₂) := (Algebra.TensorProduct.map
    (AlgHom.id k K₁) (IsScalarTower.toAlgHom k K₂' K₂)).toRingHom.toAlgebra
  let _ : Algebra (K₁' ⊗[k] K₂') (K₁ ⊗[k] K₂) := (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k K₁' K₁) (IsScalarTower.toAlgHom k K₂' K₂)).toRingHom.toAlgebra
  have : IsScalarTower (K₁' ⊗[k] K₂') (K₁ ⊗[k] K₂') (K₁ ⊗[k] K₂) := .of_algebraMap_eq fun x => by
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
    rfl
  rw [← h₁, ← h₂]
  exact (Module.finrank_mul_finrank _ _ _).symm

/-- Near a point `x` of `closure {z}`, the set `closure {z}` is the image of an integral scheme of
finite type over `ℂ`: `Spec (Γ(U) ⧸ 𝔭_z)` for an affine open `U ∋ x`.
Source: Hartshorne, *Algebraic Geometry*, II, Example 3.2.6 (reduced induced structure). -/
theorem a1x_chart (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (z x : X.left)
    (hx : x ∈ closure {z}) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ X.left) (U : Set X.left), IsOpen U ∧ x ∈ U ∧ z ∈ U ∧
      IsIntegral Z ∧ LocallyOfFiniteType (i ≫ X.hom) ∧ Set.range i = closure {z} ∩ U := by
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.left.isBasis_affineOpens) (show x ∈ (⊤ : X.left.Opens) from trivial)
  have hU : IsAffineOpen U := hU
  have hzU : z ∈ U := by
    obtain ⟨y, hyU, hy⟩ := mem_closure_iff.mp hx U U.isOpen hxU
    rw [Set.mem_singleton_iff.mp hy] at hyU
    exact hyU
  let p := hU.primeIdealOf ⟨z, hzU⟩
  let q : Spec (.of (Γ(X.left, U) ⧸ p.asIdeal)) ⟶ Spec Γ(X.left, U) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨_, q ≫ hU.fromSpec, U, U.isOpen, hxU, hzU, inferInstance, inferInstance, ?_⟩
  let p' : Spec Γ(X.left, U) := p
  have hq : Set.range q = closure ({p'} : Set (Spec Γ(X.left, U))) := by
    have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal)) = closure {p} := by
      rw [PrimeSpectrum.closure_singleton,
        range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact this
  have he := hU.fromSpec.isOpenEmbedding
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hq,
    he.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
    hU.fromSpec_primeIdealOf, Set.image_preimage_eq_inter_range, hU.range_fromSpec]

/-- Every point of `a1p_productSet X Y z w` has an open neighbourhood meeting the set in an
irreducible piece, the image of `Spec (A ⧸ 𝔭_z) ×_ℂ Spec (B ⧸ 𝔭_w)`; the neighbourhood contains
every point over `(z, w)`.
Source: Stacks Project, Tag 05P3; Mathlib, `Scheme.Pullback.range_map`. -/
theorem a1x_productSet_piece (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (z : X.left) (w : Y.left) (p : (gagam_product X Y).left)
    (hp : p ∈ a1p_productSet X Y z w) :
    ∃ N : Set (gagam_product X Y).left, IsOpen N ∧ p ∈ N ∧
      IsIrreducible (a1p_productSet X Y z w ∩ N) ∧
      ∀ t : (gagam_product X Y).left, pullback.fst X.hom Y.hom t = z →
        pullback.snd X.hom Y.hom t = w → t ∈ N := by
  obtain ⟨Z, i, U, hUo, hpU, hzU, hZ, hi, hiU⟩ := a1x_chart X z _ hp.1
  obtain ⟨W, j, V, hVo, hpV, hwV, hW, hj, hjV⟩ := a1x_chart Y w _ hp.2
  refine ⟨pullback.fst X.hom Y.hom ⁻¹' U ∩ pullback.snd X.hom Y.hom ⁻¹' V,
    (hUo.preimage (pullback.fst X.hom Y.hom).continuous).inter
      (hVo.preimage (pullback.snd X.hom Y.hom).continuous),
    ⟨hpU, hpV⟩, ?_, fun t ht hs => ⟨Set.mem_preimage.mpr (ht ▸ hzU),
      Set.mem_preimage.mpr (hs ▸ hwV)⟩⟩
  have := HodgeLean.Foundations.isIntegral_pullback_of_isAlgClosed ℂ Z W (i ≫ X.hom) (j ≫ Y.hom)
  have hr := Scheme.Pullback.range_map (f := i ≫ X.hom) (g := j ≫ Y.hom) X.hom Y.hom i j (𝟙 _)
    (by simp) (by simp)
  have hset : a1p_productSet X Y z w ∩
      (pullback.fst X.hom Y.hom ⁻¹' U ∩ pullback.snd X.hom Y.hom ⁻¹' V) =
      Set.range (pullback.map (i ≫ X.hom) (j ≫ Y.hom) X.hom Y.hom i j (𝟙 _)
        (by simp) (by simp)) := by
    rw [hr, hiU, hjV]
    ext t
    simp only [a1p_productSet, Set.mem_inter_iff]
    change (_ ∧ _) ∧ (_ ∧ _) ↔ (_ ∧ _) ∧ (_ ∧ _)
    tauto
  rw [hset, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn

/-- `pr₁⁻¹(closure {z}) ∩ pr₂⁻¹(closure {w})` is irreducible, for `X`, `Y` locally of finite type
over `ℂ`.
Source: Stacks Project, Tag 05P3; Fulton, *Intersection Theory*, second edition, §1.10. -/
theorem a1x_productSet_isIrreducible (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (z : X.left) (w : Y.left) :
    IsIrreducible (a1p_productSet X Y z w) := by
  obtain ⟨t₀, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := Y.hom) z w
    (Subsingleton.elim _ _)
  have ht₀ : t₀ ∈ a1p_productSet X Y z w := by
    refine ⟨Set.mem_preimage.mpr ?_, Set.mem_preimage.mpr ?_⟩
    · change pullback.fst X.hom Y.hom t₀ ∈ closure {z}
      rw [ht₁]; exact subset_closure rfl
    · change pullback.snd X.hom Y.hom t₀ ∈ closure {w}
      rw [ht₂]; exact subset_closure rfl
  obtain ⟨N, hNo, hN, hNi, -⟩ := a1x_productSet_piece X Y z w t₀ ht₀
  have hclosed : IsClosed (a1p_productSet X Y z w) :=
    (isClosed_closure.preimage (Scheme.Hom.continuous _)).inter
      (isClosed_closure.preimage (Scheme.Hom.continuous _))
  suffices h : a1p_productSet X Y z w = closure (a1p_productSet X Y z w ∩ N) by
    rw [h]; exact hNi.closure
  refine subset_antisymm (fun p hp => ?_)
    ((closure_mono Set.inter_subset_left).trans hclosed.closure_subset)
  obtain ⟨M, hMo, hpM, hMi, hM⟩ := a1x_productSet_piece X Y z w p hp
  have h1 := subset_closure_inter_of_isPreirreducible_of_isOpen hMi.isPreirreducible hNo
    ⟨t₀, ⟨ht₀, hM t₀ ht₁ ht₂⟩, hN⟩
  refine closure_mono ?_ (h1 ⟨hp, hpM⟩)
  exact fun t ht => ⟨ht.1.1, ht.2⟩


open Scheme.Pullback in
/-- The pushout `κ(x) ⊗[κ(s)] κ(y)` of a triplet is the tensor product of the residue fields,
compatibly with the two inclusions.
Source: Mathlib, `CommRingCat.isPushout_tensorProduct`. -/
theorem a1x_tensorIso {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triplet f g) :
    letI := ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
    letI := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
    ∃ e : T.tensor ≃+* (X.residueField T.x ⊗[S.residueField T.s] Y.residueField T.y),
      (∀ a, e (T.tensorInl a) = a ⊗ₜ 1) ∧ ∀ b, e (T.tensorInr b) = 1 ⊗ₜ b := by
  let _ := ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
  let _ := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
  let h := (IsPushout.of_hasPushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)).isoIsPushout _ _
    (CommRingCat.isPushout_tensorProduct (S.residueField T.s) (X.residueField T.x)
      (Y.residueField T.y))
  refine ⟨h.commRingCatIsoToRingEquiv, fun a => ?_, fun b => ?_⟩
  · have := IsPushout.inl_isoIsPushout_hom (h := IsPushout.of_hasPushout _ _) (h' :=
      (CommRingCat.isPushout_tensorProduct (S.residueField T.s) (X.residueField T.x)
        (Y.residueField T.y)))
    exact congr($(this).hom a)
  · have := IsPushout.inr_isoIsPushout_hom (h := IsPushout.of_hasPushout _ _) (h' :=
      (CommRingCat.isPushout_tensorProduct (S.residueField T.s) (X.residueField T.x)
        (Y.residueField T.y)))
    exact congr($(this).hom b)


/-- At the generic point of the spectrum of a domain `R`, the residue field is a fraction field
of `R`.
Source: Mathlib, `Scheme.Spec.residueFieldIso` and `Ideal.ResidueField` of `⊥`. -/
theorem a1x_isFractionRing_residueField_bot (R : CommRingCat.{u}) [IsDomain R] (x : Spec R)
    (hx : x.asIdeal = ⊥) :
    letI := ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation x).hom.toAlgebra
    IsFractionRing R ((Spec R).residueField x) := by
  let _ := ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation x).hom.toAlgebra
  have := x.isPrime
  have key : ∀ (I : Ideal R) [I.IsPrime], I = ⊥ → IsFractionRing R I.ResidueField := by
    rintro I _ rfl
    exact (inferInstance : IsFractionRing R (⊥ : Ideal R).ResidueField)
  have h0 : IsFractionRing R x.asIdeal.ResidueField := key _ hx
  let e : x.asIdeal.ResidueField ≃ₐ[R] (Spec R).residueField x :=
    { (Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        have := congr($(Scheme.Spec.algebraMap_residueFieldIso_inv R x).hom r)
        exact this }
  exact IsLocalization.isLocalization_of_algEquiv _ e


/-- The degree of `Spec.map φ` at generic points is the rank of `B` over `A`.
Source: Mathlib, `IsFractionRing.finrank_eq`. -/
theorem a1x_degree_specMap_bot {A B : CommRingCat.{u}} [IsDomain A] [IsDomain B] (φ : A ⟶ B)
    (x : Spec B) (hx : x.asIdeal = ⊥) (hφx : (Spec.map φ x).asIdeal = ⊥) :
    letI := φ.hom.toAlgebra
    a1p_degree (Spec.map φ) x = finrank A B := by
  let _ := φ.hom.toAlgebra
  let K := (Spec A).residueField (Spec.map φ x)
  let L := (Spec B).residueField x
  let _ : Algebra A K := ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation _).hom.toAlgebra
  let _ : Algebra B L := ((Scheme.ΓSpecIso B).inv ≫ (Spec B).Γevaluation x).hom.toAlgebra
  let _ : Algebra K L := ((Spec.map φ).residueFieldMap x).hom.toAlgebra
  let _ : Algebra A L := (φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).Γevaluation x).hom.toAlgebra
  have : IsScalarTower A B L := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K L := .of_algebraMap_eq fun a => by
    change (φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).Γevaluation x) a =
      ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation _ ≫ (Spec.map φ).residueFieldMap x) a
    rw [Scheme.Γevaluation_naturality, Scheme.ΓSpecIso_inv_naturality_assoc]
  have := a1x_isFractionRing_residueField_bot A _ hφx
  have := a1x_isFractionRing_residueField_bot B x hx
  exact IsFractionRing.finrank_eq A K B L


/-- A morphism whose residue-field map at `x` is surjective has degree `1` at `x`.
Source: Mathlib, `Module.finrank_self`. -/
theorem a1x_degree_eq_one_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : Function.Surjective (f.residueFieldMap x)) : a1p_degree f x = 1 := by
  let _ := (f.residueFieldMap x).hom.toAlgebra
  have hb : Function.Bijective (f.residueFieldMap x) := ⟨(f.residueFieldMap x).hom.injective, h⟩
  change finrank (Y.residueField (f x)) (X.residueField x) = 1
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective _ hb) (RingEquiv.refl _)
    (S₁ := X.residueField x) (by ext; rfl)]
  exact Module.finrank_self _

open Scheme.Pullback in
/-- The map `Spec (κ(x) ⊗[κ(s)] κ(y)) → X ×_S Y` has degree `1` at the generic point when the
tensor product is a domain: the residue field of the image point contains the image of the
tensor product, whose fraction field is the residue field upstairs.
Source: Mathlib, `Scheme.Pullback.Triplet.Spec_ofPointTensor_SpecTensorTo`. -/
theorem a1x_degree_specTensorTo_bot {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Triplet f g) [IsDomain T.tensor] (q : Spec T.tensor) (hq : q.asIdeal = ⊥) :
    a1p_degree T.SpecTensorTo q = 1 := by
  apply a1x_degree_eq_one_of_surjective
  have h1 := T.Spec_ofPointTensor_SpecTensorTo q
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h1
  have := q.isPrime
  have key : ∀ (I : Ideal T.tensor) [I.IsPrime], I = ⊥ →
      IsFractionRing T.tensor I.ResidueField := by
    rintro I _ rfl
    exact (inferInstance : IsFractionRing T.tensor (⊥ : Ideal T.tensor).ResidueField)
  have h0 : IsFractionRing T.tensor q.asIdeal.ResidueField := key _ hq
  intro c
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := T.tensor)
    ((Scheme.Spec.residueFieldIso T.tensor q).hom c)
  have hc : c = (Scheme.Spec.residueFieldIso T.tensor q).inv
      (algebraMap T.tensor q.asIdeal.ResidueField a / algebraMap _ _ b) := by
    rw [hab]; exact (congr($((Scheme.Spec.residueFieldIso T.tensor q).hom_inv_id).hom c)).symm
  have hr (r : T.tensor) : (Scheme.Spec.residueFieldIso T.tensor q).inv
      (algebraMap T.tensor q.asIdeal.ResidueField r) =
      T.SpecTensorTo.residueFieldMap q (ofPointTensor (T.SpecTensorTo q)
        ((Triplet.tensorCongr (T.ofPoint_SpecTensorTo q).symm).hom r)) :=
    (congr($(h1).hom r)).symm
  refine ⟨ofPointTensor (T.SpecTensorTo q)
      ((Triplet.tensorCongr (T.ofPoint_SpecTensorTo q).symm).hom a) /
    ofPointTensor (T.SpecTensorTo q)
      ((Triplet.tensorCongr (T.ofPoint_SpecTensorTo q).symm).hom b), ?_⟩
  rw [hc, map_div₀, map_div₀, hr, hr]


section Triplet

open Scheme.Pullback

variable {X Y X' Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S}

/-- The image of a triplet `(x, y, s)` of `f`, `g` under maps `a`, `b` over `S`: the triplet
`(a x, b y, s)` of `f'`, `g'`.
Source: Mathlib, `AlgebraicGeometry.Scheme.Pullback.Triplet`. -/
def a1x_imageTriplet (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g)
    (T : Triplet f g) : Triplet f' g' where
  x := a T.x
  y := b T.y
  s := T.s
  hx := by rw [← Scheme.Hom.comp_apply, ha, T.hx]
  hy := by rw [← Scheme.Hom.comp_apply, hb, T.hy]

/-- The residue-field maps of `a` and `f'` compose to the residue-field map of `f = a ≫ f'`.
Source: Mathlib, `Scheme.residueFieldMap_comp`. -/
example (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g) (T : Triplet f g) :
    (a1x_imageTriplet a b ha hb T).x = a T.x := rfl

theorem a1x_residue_comp (a : X ⟶ X') (ha : a ≫ f' = f) (x : X) (s : S) (h' : f' (a x) = s)
    (h : f x = s) :
    (S.residueFieldCongr h').inv ≫ f'.residueFieldMap (a x) ≫ a.residueFieldMap x =
      (S.residueFieldCongr h).inv ≫ f.residueFieldMap x := by
  subst ha
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- The map `κ(a x) ⊗[κ(s)] κ(b y) → κ(x) ⊗[κ(s)] κ(y)` of the pushouts of residue fields.
Source: Mathlib, `CategoryTheory.Limits.pushout.desc`. -/
def a1x_tensorMap (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g)
    (T : Triplet f g) : (a1x_imageTriplet a b ha hb T).tensor ⟶ T.tensor :=
  pushout.desc (a.residueFieldMap T.x ≫ T.tensorInl) (b.residueFieldMap T.y ≫ T.tensorInr) (by
    have h1 := a1x_residue_comp a ha T.x T.s (a1x_imageTriplet a b ha hb T).hx T.hx
    have h2 := a1x_residue_comp b hb T.y T.s (a1x_imageTriplet a b ha hb T).hy T.hy
    have h3 := pushout.condition (f := (S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      (g := (S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
    simp only [Category.assoc] at h1 h2 h3 ⊢
    dsimp only [a1x_imageTriplet]
    rw [reassoc_of% h1, reassoc_of% h2]
    exact h3)

example (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g) (T : Triplet f g) :
    (a1x_imageTriplet a b ha hb T).tensor ⟶ T.tensor := a1x_tensorMap a b ha hb T

/-- `a1x_tensorMap` on the left factor.
Source: Mathlib, `pushout.inl_desc`. -/
theorem a1x_tensorMap_inl (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g)
    (T : Triplet f g) :
    (a1x_imageTriplet a b ha hb T).tensorInl ≫ a1x_tensorMap a b ha hb T =
      a.residueFieldMap T.x ≫ T.tensorInl :=
  pushout.inl_desc _ _ _

/-- `a1x_tensorMap` on the right factor.
Source: Mathlib, `pushout.inr_desc`. -/
theorem a1x_tensorMap_inr (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g)
    (T : Triplet f g) :
    (a1x_imageTriplet a b ha hb T).tensorInr ≫ a1x_tensorMap a b ha hb T =
      b.residueFieldMap T.y ≫ T.tensorInr :=
  pushout.inr_desc _ _ _

/-- The square `Spec (κ(x) ⊗ κ(y)) → X ×_S Y → X' ×_S Y'` equals
`Spec (κ(x) ⊗ κ(y)) → Spec (κ(a x) ⊗ κ(b y)) → X' ×_S Y'`.
Source: Mathlib, `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`. -/
theorem a1x_specTensorTo_map (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g)
    (T : Triplet f g) :
    T.SpecTensorTo ≫ pullback.map f g f' g' a b (𝟙 S) (by simp [ha]) (by simp [hb]) =
      Spec.map (a1x_tensorMap a b ha hb T) ≫ (a1x_imageTriplet a b ha hb T).SpecTensorTo := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Triplet.specTensorTo_fst,
      Triplet.specTensorTo_fst_assoc]
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    exact (pushout.inl_desc _ _ _).symm
  · simp only [Category.assoc, pullback.lift_snd, Triplet.specTensorTo_snd,
      Triplet.specTensorTo_snd_assoc]
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    exact (pushout.inr_desc _ _ _).symm

/-- Over an algebraically closed residue field `κ(s)`, both tensor products of residue fields are
domains, the map between them is injective, and its rank is the product of the degrees of `a` at
`x` and `b` at `y`.
Source: Fulton, *Intersection Theory*, second edition, §1.10, proof of Proposition 1.10. -/
theorem a1x_tensorMap_spec (a : X ⟶ X') (b : Y ⟶ Y') (ha : a ≫ f' = f) (hb : b ≫ g' = g)
    (T : Triplet f g) [IsAlgClosed (S.residueField T.s)] :
    IsDomain T.tensor ∧ IsDomain (a1x_imageTriplet a b ha hb T).tensor ∧
      Function.Injective (a1x_tensorMap a b ha hb T) ∧
      (letI := (a1x_tensorMap a b ha hb T).hom.toAlgebra;
        finrank (a1x_imageTriplet a b ha hb T).tensor T.tensor =
          a1p_degree a T.x * a1p_degree b T.y) := by
  let T' := a1x_imageTriplet a b ha hb T
  let k := S.residueField T.s
  let _ : Algebra k (X.residueField T.x) :=
    ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
  let _ : Algebra k (Y.residueField T.y) :=
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
  let _ : Algebra k (X'.residueField T'.x) :=
    ((S.residueFieldCongr T'.hx).inv ≫ f'.residueFieldMap T'.x).hom.toAlgebra
  let _ : Algebra k (Y'.residueField T'.y) :=
    ((S.residueFieldCongr T'.hy).inv ≫ g'.residueFieldMap T'.y).hom.toAlgebra
  let _ : Algebra (X'.residueField T'.x) (X.residueField T.x) := (a.residueFieldMap T.x).hom.toAlgebra
  let _ : Algebra (Y'.residueField T'.y) (Y.residueField T.y) := (b.residueFieldMap T.y).hom.toAlgebra
  have : IsScalarTower k (X'.residueField T'.x) (X.residueField T.x) := .of_algebraMap_eq fun c =>
    (congr($(a1x_residue_comp a ha T.x T.s T'.hx T.hx).hom c)).symm
  have : IsScalarTower k (Y'.residueField T'.y) (Y.residueField T.y) := .of_algebraMap_eq fun c =>
    (congr($(a1x_residue_comp b hb T.y T.s T'.hy T.hy).hom c)).symm
  obtain ⟨e, he1, he2⟩ := a1x_tensorIso T
  obtain ⟨e', he1', he2'⟩ : ∃ e' : T'.tensor ≃+*
      (X'.residueField T'.x ⊗[k] Y'.residueField T'.y),
      (∀ c, e' (T'.tensorInl c) = c ⊗ₜ 1) ∧ ∀ c, e' (T'.tensorInr c) = 1 ⊗ₜ c :=
    a1x_tensorIso T'
  have := a1x_isDomain_tensorProduct k (X.residueField T.x) (Y.residueField T.y)
  have := a1x_isDomain_tensorProduct k (X'.residueField T'.x) (Y'.residueField T'.y)
  have := a1x_isDomain_tensorProduct k (X.residueField T.x) (Y'.residueField T'.y)
  let m := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k (X'.residueField T'.x)
    (X.residueField T.x)) (IsScalarTower.toAlgHom k (Y'.residueField T'.y) (Y.residueField T.y))
  have hsq : ∀ c, e (a1x_tensorMap a b ha hb T c) = m (e' c) := by
    have : a1x_tensorMap a b ha hb T ≫ CommRingCat.ofHom e.toRingHom =
        CommRingCat.ofHom e'.toRingHom ≫ CommRingCat.ofHom m.toRingHom := by
      apply pushout.hom_ext
      · ext c
        change e (a1x_tensorMap a b ha hb T (T'.tensorInl c)) = m (e' (T'.tensorInl c))
        rw [he1']
        have : a1x_tensorMap a b ha hb T (T'.tensorInl c) = T.tensorInl (a.residueFieldMap T.x c) :=
          congr($(a1x_tensorMap_inl a b ha hb T).hom c)
        rw [this, he1]
        erw [Algebra.TensorProduct.map_tmul, map_one]
        rfl
      · ext c
        change e (a1x_tensorMap a b ha hb T (T'.tensorInr c)) = m (e' (T'.tensorInr c))
        rw [he2']
        have : a1x_tensorMap a b ha hb T (T'.tensorInr c) = T.tensorInr (b.residueFieldMap T.y c) :=
          congr($(a1x_tensorMap_inr a b ha hb T).hom c)
        rw [this, he2]
        erw [Algebra.TensorProduct.map_tmul, map_one]
        rfl
    exact fun c => congr($(this).hom c)
  have hm : Function.Injective m :=
    TensorProduct.map_injective_of_flat_flat _ _ (a.residueFieldMap T.x).hom.injective
      (b.residueFieldMap T.y).hom.injective
  refine ⟨Function.Injective.isDomain e.toRingHom e.injective,
    Function.Injective.isDomain e'.toRingHom e'.injective, fun c d hcd => ?_, ?_⟩
  · apply e'.injective
    apply hm
    rw [← hsq, ← hsq, hcd]
  · let _ := (a1x_tensorMap a b ha hb T).hom.toAlgebra
    let _ := m.toRingHom.toAlgebra
    rw [Algebra.finrank_eq_of_equiv_equiv e' e (by ext c; exact (hsq c).symm)]
    exact a1x_finrank_tensor_map k _ _ _ _

end Triplet

/-- The residue field of `Spec ℂ` is algebraically closed.
Source: Mathlib, `Scheme.Spec.residueFieldIsoOfField` and `IsAlgClosed.of_ringEquiv`. -/
theorem a1x_isAlgClosed_residueField (s : Spec ↧ℂ) :
    IsAlgClosed ((Spec ↧ℂ).residueField s) :=
  IsAlgClosed.of_ringEquiv ℂ _ (Scheme.Spec.residueFieldIsoOfField s).symm.commRingCatIsoToRingEquiv

open Scheme.Pullback in
/-- The generic point of `a1p_productSet X Y z w` is the image of the generic point of
`Spec (κ(z) ⊗ κ(w))`: it lies over `(z, w)`, and every point over `(z, w)` specializes from that
image.
Source: Mathlib, `Scheme.Pullback.carrierEquiv`; Fulton, *Intersection Theory*, second edition,
§1.10. -/
theorem a1x_genericPoint_eq (X Y : Over (Spec ↧ℂ)) (z : X.left) (w : Y.left)
    (h : IsIrreducible (a1p_productSet X Y z w)) (T : Triplet X.hom Y.hom) (hTx : T.x = z)
    (hTy : T.y = w) (q : Spec T.tensor) (hq : ∀ r : Spec T.tensor, q ⤳ r) :
    h.genericPoint = T.SpecTensorTo q := by
  have hcl : IsClosed (a1p_productSet X Y z w) :=
    (isClosed_closure.preimage (Scheme.Hom.continuous _)).inter
      (isClosed_closure.preimage (Scheme.Hom.continuous _))
  have hp : closure {h.genericPoint} = a1p_productSet X Y z w := by
    rw [h.isGenericPoint_genericPoint_closure.def, hcl.closure_eq]
  generalize h.genericPoint = p at hp ⊢
  have hmem : ∀ t : (gagam_product X Y).left, pullback.fst X.hom Y.hom t = z →
      pullback.snd X.hom Y.hom t = w → t ∈ a1p_productSet X Y z w := fun t h1 h2 =>
    ⟨Set.mem_preimage.mpr (by change pullback.fst X.hom Y.hom t ∈ _; rw [h1]; exact subset_closure rfl),
      Set.mem_preimage.mpr (by change pullback.snd X.hom Y.hom t ∈ _; rw [h2]; exact subset_closure rfl)⟩
  have h0 : T.SpecTensorTo q ∈ a1p_productSet X Y z w := hmem _ (by simp [hTx]) (by simp [hTy])
  have hp0 : p ⤳ T.SpecTensorTo q :=
    specializes_iff_mem_closure.mpr (by rw [hp]; exact h0)
  have hgp := hp ▸ subset_closure (Set.mem_singleton p)
  obtain ⟨t₀, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := Y.hom) z w
    (Subsingleton.elim _ _)
  have ht₀ : p ⤳ t₀ :=
    specializes_iff_mem_closure.mpr (by rw [hp]; exact hmem _ ht₁ ht₂)
  have hfst : pullback.fst X.hom Y.hom p = z := by
    refine (Specializes.antisymm ?_ ?_).eq
    · rw [← ht₁]; exact ht₀.map (Scheme.Hom.continuous _)
    · exact specializes_iff_mem_closure.mpr hgp.1
  have hsnd : pullback.snd X.hom Y.hom p = w := by
    refine (Specializes.antisymm ?_ ?_).eq
    · rw [← ht₂]; exact ht₀.map (Scheme.Hom.continuous _)
    · exact specializes_iff_mem_closure.mpr hgp.2
  have hT : Triplet.ofPoint p = T := Triplet.ext (hfst.trans hTx.symm) (hsnd.trans hTy.symm)
  have key : ∀ (T'' : Triplet X.hom Y.hom), T'' = T → ∀ r : Spec T''.tensor,
      T.SpecTensorTo q ⤳ T''.SpecTensorTo r := by
    rintro _ rfl r
    exact (hq r).map (Scheme.Hom.continuous _)
  have h2 := key _ hT (SpecOfPoint p)
  have h3 : (Triplet.ofPoint p).SpecTensorTo (SpecOfPoint p) = p := SpecTensorTo_SpecOfPoint p
  rw [h3] at h2
  exact (Specializes.antisymm hp0 h2).eq


section Scale

variable {X : Type*} [TopologicalSpace X] {R : Type*} [Semiring R]

/-- Scaling a cycle by `0` gives `0`.
Source: Mathlib, `Function.locallyFinsuppWithin.mapRange_apply`. -/
theorem a1x_mapRange_zero (c : Function.locallyFinsupp X R) :
    c.mapRange ((0 : R) * ·) (mul_zero 0) = 0 := by
  ext x
  simp [Function.locallyFinsuppWithin.mapRange_apply]

/-- Scaling a cycle by `t` and then by `r` is scaling by `r * t`.
Source: Mathlib, `Function.locallyFinsuppWithin.mapRange_apply`. -/
theorem a1x_mapRange_mapRange (r t : R) (c : Function.locallyFinsupp X R) :
    (c.mapRange (t * ·) (mul_zero t)).mapRange (r * ·) (mul_zero r) =
      c.mapRange (r * t * ·) (mul_zero _) := by
  ext x
  simp [Function.locallyFinsuppWithin.mapRange_apply, mul_assoc]

/-- Scaling a cycle is additive in the scalar.
Source: Mathlib, `Function.locallyFinsuppWithin.mapRange_apply`. -/
theorem a1x_mapRange_add (r t : R) (c : Function.locallyFinsupp X R) :
    c.mapRange ((r + t) * ·) (mul_zero _) =
      c.mapRange (r * ·) (mul_zero r) + c.mapRange (t * ·) (mul_zero t) := by
  ext x
  simp [Function.locallyFinsuppWithin.mapRange_apply, add_mul]

/-- Scaling a cycle by a finite sum is the sum of the scalings.
Source: Mathlib, `Finset.induction_on`. -/
theorem a1x_mapRange_sum {ι : Type*} (s : Finset ι) (r : ι → R) (c : Function.locallyFinsupp X R) :
    c.mapRange ((∑ i ∈ s, r i) * ·) (mul_zero _) = ∑ i ∈ s, c.mapRange (r i * ·) (mul_zero _) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using a1x_mapRange_zero c
  | insert i s hi ih => rw [Finset.sum_insert hi, a1x_mapRange_add, ih, Finset.sum_insert hi]

end Scale

/-- When the supports of `α` and `β` lie in finite sets `s` and `t`, the external product is the
finite sum over `s × t`.
Source: Fulton, *Intersection Theory*, second edition, §1.10, exterior product of cycles;
Mathlib, `finsum_eq_sum_of_support_subset`. -/
theorem a1x_externalProductCycle_eq_sum {X Y : Over (Spec ↧ℂ)} {R : Type*} [Semiring R]
    (α : AlgebraicCycle X.left R) (β : AlgebraicCycle Y.left R) (s : Finset X.left)
    (t : Finset Y.left) (hs : α.support ⊆ s) (ht : β.support ⊆ t) :
    a1p_externalProductCycle α β = ∑ z ∈ s, ∑ w ∈ t,
      (a1p_externalProduct X Y z w R).mapRange (α z * β w * ·) (mul_zero _) := by
  unfold a1p_externalProductCycle
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
    intro w hw
    by_contra h
    apply hw
    have : β w = 0 := by
      by_contra h'; exact h (ht h')
    simp only [this, mul_zero]
    exact a1x_mapRange_zero _
  · intro z hz
    by_contra h
    apply hz
    have : α z = 0 := by
      by_contra h'; exact h (hs h')
    have h0 : ∀ w, (a1p_externalProduct X Y z w R).mapRange (α z * β w * ·) (mul_zero _) = 0 :=
      fun w => by ext; simp [Function.locallyFinsuppWithin.mapRange_apply, this]
    simp only [h0, finsum_zero]

/-- When the support of `c` lies in a finite set `s`, the coefficient of `f_* c` at `y` is the
finite sum over the points of `s` above `y`.
Source: Mathlib, `finsum_mem_eq_sum_of_inter_support_eq`. -/
theorem a1x_pushforward_apply_eq_sum {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] {R : Type*}
    [Semiring R] [DecidableEq Y] (c : AlgebraicCycle X R) (s : Finset X) (hs : c.support ⊆ s)
    (y : Y) : a1p_pushforward f c y = ∑ x ∈ s with f x = y, c x * (a1p_degree f x : R) := by
  change ∑ᶠ x ∈ f ⁻¹' {y}, c x * (a1p_degree f x : R) = _
  apply finsum_mem_eq_sum_of_inter_support_eq
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Function.mem_support,
    Finset.coe_filter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hs (left_ne_zero_of_mul h2), h1⟩, h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-- The pushforward of the zero cycle is zero.
Source: Mathlib, `finsum_zero`. -/
theorem a1x_pushforward_zero {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] {R : Type*}
    [Semiring R] : a1p_pushforward f (0 : AlgebraicCycle X R) = 0 := by
  ext y
  change ∑ᶠ x ∈ f ⁻¹' {y}, (0 : AlgebraicCycle X R) x * (a1p_degree f x : R) = 0
  simp

/-- When the support of `c` lies in a finite set `s`, the support of `f_* c` lies in `f(s)`.
Source: Fulton, *Intersection Theory*, second edition, §1.4. -/
theorem a1x_pushforward_support {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] {R : Type*}
    [Semiring R] [DecidableEq Y] (c : AlgebraicCycle X R) (s : Finset X) (hs : c.support ⊆ s) :
    (a1p_pushforward f c).support ⊆ s.image f := by
  classical
  intro y hy
  rw [Function.mem_support, a1x_pushforward_apply_eq_sum f c s hs] at hy
  obtain ⟨x, hx, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  rw [Finset.mem_filter] at hx
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩)

end HodgeLean.Adapters
