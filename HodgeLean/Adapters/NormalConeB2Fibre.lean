import HodgeLean.Adapters.NormalConeB2Chart
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Fibres of a deformation family

Density of the punctured family, and the identification of base changes of a chart along
the parameter line with spectra of tensor products.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData}

/-- The spectrum of an injective ring map is scheme-theoretically dominant.
Source: Mathlib, `AlgebraicGeometry.Scheme.ker_of_isAffine`. -/
theorem a3b2_SpecMap_isSchemeTheoreticallyDominant {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
  have h : RingHom.ker (Spec.map φ).appTop.hom = ⊥ := by
    rw [← RingHom.injective_iff_ker_eq_bot]
    have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
      rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1.comp
      (hφ.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)
  rw [h]
  ext U : 2
  simp

/-- The punctured line is scheme-theoretically dominant in the line.
Source: Mathlib, `Polynomial.toLaurent_injective`. -/
instance a3b2_punctured_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (a3b2_punctured k) :=
  a3b2_SpecMap_isSchemeTheoreticallyDominant _ Polynomial.toLaurent_injective

/-- The punctured family is scheme-theoretically dense in the family: a flat base change of the
dense open immersion of the punctured line.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88; Mathlib,
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst`. -/
theorem a3b2_puncturedDense' (D : A3b2Deformation k X p I) :
    IsSchemeTheoreticallyDominant (pullback.fst D.toLine (a3b2_punctured k)) :=
  haveI := a3b2_flat_toLine D
  inferInstance

/-- Tensoring over the line with the evaluation at `c` is the quotient by `t - c`.
Source: Mathlib, `Polynomial.X_sub_C_dvd_sub_C_eval` and `Algebra.TensorProduct.lift`. -/
def a3b2_tensorEvalEquiv (A : Type u) [CommRing A] [Algebra (Polynomial k) A] (c : k)
    [Algebra (Polynomial k) k] (hc : algebraMap (Polynomial k) k = Polynomial.evalRingHom c) :
    A ⊗[Polynomial k] k ≃+*
      A ⧸ Ideal.span {algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C c)} := by
  set J := Ideal.span {algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C c)}
  have hJ : ∀ q : Polynomial k, algebraMap (Polynomial k) (A ⧸ J) (Polynomial.C (q.eval c)) =
      algebraMap (Polynomial k) (A ⧸ J) q := by
    intro q
    rw [← sub_eq_zero, ← map_sub, IsScalarTower.algebraMap_apply (Polynomial k) A (A ⧸ J),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨r, hr⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := c) (p := q)
    rw [← neg_sub, hr, map_neg, map_mul]
    exact J.neg_mem (J.mul_mem_right _ (Ideal.subset_span rfl))
  let g : k →ₐ[Polynomial k] A ⧸ J :=
    { toRingHom := (algebraMap (Polynomial k) (A ⧸ J)).comp Polynomial.C
      commutes' := fun q => by
        change algebraMap _ _ (Polynomial.C (algebraMap (Polynomial k) k q)) = _
        rw [hc]
        exact hJ q }
  let F : A ⊗[Polynomial k] k →ₐ[Polynomial k] A ⧸ J :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ (Polynomial k) J) g
      (fun _ _ => Commute.all _ _)
  have hone : ∀ q : Polynomial k, (algebraMap (Polynomial k) A q) ⊗ₜ[Polynomial k] (1 : k) =
      (1 : A) ⊗ₜ (algebraMap (Polynomial k) k q) := by
    intro q
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hker : ∀ a ∈ J, (Algebra.TensorProduct.includeLeft : A →ₐ[Polynomial k]
      A ⊗[Polynomial k] k) a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    change _ * ((algebraMap (Polynomial k) A _) ⊗ₜ[Polynomial k] (1 : k)) = 0
    rw [hone, hc]
    simp
  let G : A ⧸ J →ₐ[Polynomial k] A ⊗[Polynomial k] k :=
    Ideal.Quotient.liftₐ J Algebra.TensorProduct.includeLeft hker
  have hGF : G.comp F = AlgHom.id _ _ := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change G (F (a ⊗ₜ b)) = a ⊗ₜ b
    rw [Algebra.TensorProduct.lift_tmul]
    change G (Ideal.Quotient.mk J a * algebraMap (Polynomial k) (A ⧸ J) (Polynomial.C b)) = _
    rw [map_mul, AlgHom.commutes]
    change (a ⊗ₜ[Polynomial k] (1 : k)) * algebraMap (Polynomial k) _ (Polynomial.C b) = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    calc (a ⊗ₜ[Polynomial k] (1 : k)) * ((algebraMap (Polynomial k) A (Polynomial.C b)) ⊗ₜ 1)
        = (a ⊗ₜ[Polynomial k] (1 : k)) * ((1 : A) ⊗ₜ algebraMap (Polynomial k) k
          (Polynomial.C b)) := by rw [hone]
      _ = a ⊗ₜ b := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc]
        simp
  have hFG : F.comp G = AlgHom.id _ _ := by
    apply Ideal.Quotient.algHom_ext
    ext a
    change F (a ⊗ₜ 1) = Ideal.Quotient.mk J a
    rw [Algebra.TensorProduct.lift_tmul]
    simp [g]
  exact RingEquiv.ofRingHom F.toRingHom G.toRingHom (congrArg AlgHom.toRingHom hFG)
    (congrArg AlgHom.toRingHom hGF)

/-- The defining property of `a3b2_tensorEvalEquiv` on the left factor.
Source: definition `a3b2_tensorEvalEquiv`. -/
theorem a3b2_tensorEvalEquiv_tmul (A : Type u) [CommRing A] [Algebra (Polynomial k) A] (c : k)
    [Algebra (Polynomial k) k] (hc : algebraMap (Polynomial k) k = Polynomial.evalRingHom c)
    (a : A) : a3b2_tensorEvalEquiv A c hc (a ⊗ₜ[Polynomial k] (1 : k)) = Ideal.Quotient.mk _ a := by
  simp [a3b2_tensorEvalEquiv, RingEquiv.ofRingHom_apply]

/-- Base change of a chart along an algebra over the line, for any algebra structures whose
structure maps are the line map and the given one: the part over an affine open `U` of the
pullback of the family is the spectrum of the tensor product, compatibly with both projections.
Source: Mathlib, `AlgebraicGeometry.isPullback_SpecMap_of_isPushout` and
`CommRingCat.isPushout_tensorProduct`. -/
theorem a3b2_baseChange_chart_of (D : A3b2Deformation k X p I) (U : X.affineOpens)
    {B : Type u} [CommRing B] [Algebra (Polynomial k) B]
    [Algebra (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U))]
    (hA : algebraMap (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) =
      a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U)) :
    ∃ e : ((pullback.fst D.toLine (Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial k) B)))) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).toScheme ≅
        Spec (CommRingCat.of (a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] B)),
      e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
        (pullback.fst D.toLine (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) B))) ∣_
          (D.toX ⁻¹ᵁ U.1)) ≫ (D.chart U).hom ∧
      e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) =
        ((pullback.fst D.toLine (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) B)))) ⁻¹ᵁ
          (D.toX ⁻¹ᵁ U.1)).ι ≫ pullback.snd _ _ := by
  set ψ := algebraMap (Polynomial k) B
  have h1 := isPullback_morphismRestrict (pullback.fst D.toLine (Spec.map (CommRingCat.ofHom ψ)))
    (D.toX ⁻¹ᵁ U.1)
  have h2 := IsPullback.of_hasPullback D.toLine (Spec.map (CommRingCat.ofHom ψ))
  have h3 := h1.paste_vert h2
  have h4 := h3.of_iso (Iso.refl _) (D.chart U) (Iso.refl _) (Iso.refl _)
    (Category.id_comp _).symm (by simp)
    (by rw [Iso.refl_hom, Category.comp_id, a3b2_ι_toLine, hA])
    (by simp)
    (fst' := (pullback.fst D.toLine (Spec.map (CommRingCat.ofHom ψ)) ∣_ (D.toX ⁻¹ᵁ U.1)) ≫
      (D.chart U).hom)
    (snd' := ((pullback.fst D.toLine (Spec.map (CommRingCat.ofHom ψ))) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).ι ≫
      pullback.snd _ _)
    (f' := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k)
      (a3cc3_deformationAlgebra (I.ideal U)))))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) B)))
  have h5 := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) B)
  refine ⟨h4.isoIsPullback _ _ h5, ?_, ?_⟩
  · rw [IsPullback.isoIsPullback_hom_fst]
  · rw [IsPullback.isoIsPullback_hom_snd]

/-- `a3b2_baseChange_chart_of` for a morphism to the line equal to the spectrum of the
structure map.
Source: theorem `a3b2_baseChange_chart_of`. -/
theorem a3b2_baseChange_chart_of' (D : A3b2Deformation k X p I) (U : X.affineOpens)
    {B : Type u} [CommRing B] [Algebra (Polynomial k) B]
    [Algebra (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U))]
    (hA : algebraMap (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) =
      a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U))
    (g : Spec (CommRingCat.of B) ⟶ a3b2_line k)
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) B))) :
    ∃ e : ((pullback.fst D.toLine g) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).toScheme ≅
        Spec (CommRingCat.of (a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] B)),
      e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
        (pullback.fst D.toLine g ∣_ (D.toX ⁻¹ᵁ U.1)) ≫ (D.chart U).hom ∧
      e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) =
        ((pullback.fst D.toLine g) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).ι ≫ pullback.snd _ _ := by
  subst hg
  exact a3b2_baseChange_chart_of D U hA

/-- Base change of a chart along a ring map to the line: the part over an affine open `U` of the
pullback of the family along `Spec ψ` is the spectrum of the tensor product
`Γ(X, U)[t, I(U)/t] ⊗_{k[t]} B`, compatibly with both projections.
Source: Mathlib, `AlgebraicGeometry.isPullback_SpecMap_of_isPushout` and
`CommRingCat.isPushout_tensorProduct`. -/
theorem a3b2_baseChange_chart (D : A3b2Deformation k X p I) (U : X.affineOpens)
    {B : Type u} [CommRing B] (ψ : Polynomial k →+* B) :
    letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) :=
      (a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U)).toAlgebra
    letI : Algebra (Polynomial k) B := ψ.toAlgebra
    ∃ e : ((pullback.fst D.toLine (Spec.map (CommRingCat.ofHom ψ))) ⁻¹ᵁ
        (D.toX ⁻¹ᵁ U.1)).toScheme ≅
        Spec (CommRingCat.of (a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] B)),
      e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
        (pullback.fst D.toLine (Spec.map (CommRingCat.ofHom ψ)) ∣_ (D.toX ⁻¹ᵁ U.1)) ≫
          (D.chart U).hom ∧
      e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) =
        ((pullback.fst D.toLine (Spec.map (CommRingCat.ofHom ψ))) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).ι ≫
          pullback.snd _ _ := by
  letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) :=
    (a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U)).toAlgebra
  letI : Algebra (Polynomial k) B := ψ.toAlgebra
  exact a3b2_baseChange_chart_of D U rfl

/-- Over each affine open the zero fibre is the spectrum of the normal cone ring, compatibly with
the chart and the normalized quotient.
Source: Fulton, *Intersection Theory*, second edition, §§4.1 and 5.1, p. 88; stage A3-B1,
`a3b1_specialFiberAlgEquiv`. -/
theorem a3b2_zeroFibre_cone' (D : A3b2Deformation k X p I) (U : X.affineOpens) :
    ∃ e : ((pullback.fst D.toLine (a3b2_point k 0)) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).toScheme ≅
        Spec (CommRingCat.of (a3cc3_normalConeRing (I.ideal U))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (a3b2_coneQuotient (I.ideal U))) =
        a3b2_zeroFibreRestrict D U ≫ (D.chart U).hom := by
  unfold a3b2_zeroFibreRestrict a3b2_point
  letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) :=
    (a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U)).toAlgebra
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  obtain ⟨e, he, -⟩ := a3b2_baseChange_chart D U (Polynomial.evalRingHom (0 : k))
  have hgen : Ideal.span {(algebraMap (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U))
      (Polynomial.X - Polynomial.C 0))} = Ideal.span {a3cc3_parameter (I.ideal U)} := by
    congr 2
    simp [RingHom.algebraMap_toAlgebra, a3b2_lineMap]
  let Φ : a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] k ≃+*
      a3cc3_normalConeRing (I.ideal U) :=
    (a3b2_tensorEvalEquiv _ 0 rfl).trans ((Ideal.quotEquivOfEq hgen).trans
      (a3b1_specialFiberAlgEquiv _ (I.ideal U)).toRingEquiv)
  have hΦ : (Φ.symm : a3cc3_normalConeRing (I.ideal U) →+*
      a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] k).comp
      (a3b2_coneQuotient (I.ideal U)) =
      Algebra.TensorProduct.includeLeftRingHom := by
    ext a
    apply Φ.injective
    change Φ (Φ.symm _) = Φ (a ⊗ₜ 1)
    rw [RingEquiv.apply_symm_apply]
    change _ = (a3b1_specialFiberAlgEquiv _ (I.ideal U)) (Ideal.quotEquivOfEq hgen
      (a3b2_tensorEvalEquiv _ 0 rfl (a ⊗ₜ 1)))
    rw [a3b2_tensorEvalEquiv_tmul, Ideal.quotEquivOfEq_mk]
    rfl
  refine ⟨e ≪≫ Scheme.Spec.mapIso Φ.symm.toCommRingCatIso.op, ?_⟩
  refine Eq.trans ?_ he
  rw [Iso.trans_hom, Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom (Φ.symm : a3cc3_normalConeRing (I.ideal U) →+*
      a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] k)) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hΦ]

/-- The fibre over `t = 1` maps isomorphically to `X`.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88; `a3cc3_evalOne_ker` and
`a3cc3_evalOne_surjective`. -/
theorem a3b2_unitFibre' (D : A3b2Deformation k X p I) : IsIso (a3b2_unitFibreMap D) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun U : X.affineOpens => U.1) (iSup_affineOpens_eq_top X) fun U => ?_
  change IsIso (a3b2_unitFibreMap D ∣_ U.1)
  rw [a3b2_unitFibreMap, morphismRestrict_comp]
  unfold a3b2_point
  letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U)) :=
    (a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U)).toAlgebra
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (1 : k)).toAlgebra
  obtain ⟨e, he, -⟩ := a3b2_baseChange_chart D U (Polynomial.evalRingHom (1 : k))
  have h1 : pullback.fst D.toLine (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 1))) ∣_ (D.toX ⁻¹ᵁ U.1) =
      e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (D.chart U).inv := by
    rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 : D.toX ∣_ U.1 = (D.chart U).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (a3cc3_deformationAlgebra (I.ideal U)))) ≫ U.2.isoSpec.inv := by
    rw [← Category.assoc, D.chart_toX, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h1, h2]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hgen : Ideal.span {(algebraMap (Polynomial k) (a3cc3_deformationAlgebra (I.ideal U))
      (Polynomial.X - Polynomial.C 1))} = RingHom.ker (a3cc3_evalOne (I.ideal U)) := by
    rw [a3cc3_evalOne_ker]
    congr 2
    simp [RingHom.algebraMap_toAlgebra, a3b2_lineMap]
  let Ψ : a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] k ≃+* Γ(X, U.1) :=
    (a3b2_tensorEvalEquiv _ 1 rfl).trans ((Ideal.quotEquivOfEq hgen).trans
      (RingHom.quotientKerEquivOfSurjective (a3cc3_evalOne_surjective (I.ideal U))))
  have hΨ : Algebra.TensorProduct.includeLeftRingHom.comp
      (algebraMap Γ(X, U.1) (a3cc3_deformationAlgebra (I.ideal U))) = Ψ.symm.toRingHom := by
    ext r
    apply Ψ.injective
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    change (RingHom.quotientKerEquivOfSurjective (a3cc3_evalOne_surjective (I.ideal U)))
      (Ideal.quotEquivOfEq hgen (a3b2_tensorEvalEquiv _ 1 rfl
        (algebraMap Γ(X, U.1) _ r ⊗ₜ[Polynomial k] (1 : k)))) = r
    rw [a3b2_tensorEvalEquiv_tmul, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp [a3cc3_evalOne]
  have hS : IsIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      a3cc3_deformationAlgebra (I.ideal U) →+*
        a3cc3_deformationAlgebra (I.ideal U) ⊗[Polynomial k] k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1)
        (a3cc3_deformationAlgebra (I.ideal U))))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hΨ]
    change IsIso (Spec.map Ψ.symm.toCommRingCatIso.hom)
    infer_instance
  rw [← Category.assoc (Spec.map _)]
  exact IsIso.comp_isIso' (Iso.isIso_hom e) (IsIso.comp_isIso' hS (Iso.isIso_inv _))

end HodgeLean.Adapters
