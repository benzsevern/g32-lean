import HodgeLean.Foundations.Curves.CurveFunctionField
import HodgeLean.Foundations.Curves.CurveStalkDVR
import HodgeLean.Foundations.Curves.CurveValuation

/-! # Points of a proper curve and valuations of its function field

By the valuative criterion, every valuation subring of the function field containing `ℂ`
dominates the local ring of some point (existence part, from properness); a point is determined by
its local ring as a subring of the function field (uniqueness part, from separatedness). On a
smooth curve, a proper such valuation subring is exactly the local ring of a coheight-one point.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Curves

attribute [local instance] overSpecAlgebra functionFieldAlgebra

/-- Global sections of `Spec 𝒪_{Y,x} → Y` are the germ map. -/
@[reassoc]
theorem fromSpecStalk_appTop_ΓSpecIso_hom (Y : Scheme) (x : Y) :
    (Y.fromSpecStalk x).appTop ≫ (Scheme.ΓSpecIso _).hom = Y.presheaf.germ ⊤ x trivial := by
  rw [Scheme.fromSpecStalk_appTop]
  simp

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left]

/-- The structure map from `ℂ` to a stalk. -/
def stalkC (x : X.left) : ℂ →+* X.left.presheaf.stalk x :=
  (X.left.presheaf.germ ⊤ x (by simp)).hom.comp (algebraMap ℂ Γ(X.left, ⊤))

/-- Constants in a stalk map to constants in the function field. -/
theorem algebraMap_stalkC (x : X.left) (c : ℂ) :
    algebraMap (X.left.presheaf.stalk x) X.left.functionField (stalkC x c) =
      algebraMap ℂ X.left.functionField c := by
  simp only [stalkC, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

omit [IsIntegral X.left] in
/-- A morphism from `Spec` of a stalk to `Spec ℂ` is determined by the constants. -/
theorem fromSpecStalk_comp_hom (x : X.left) {R : CommRingCat} (φ : CommRingCat.of ℂ ⟶ R)
    (ψ : R ⟶ X.left.presheaf.stalk x) (h : ∀ c, ψ (φ c) = stalkC x c) :
    X.left.fromSpecStalk x ≫ X.hom = Spec.map ψ ≫ Spec.map φ := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv,
    ← cancel_mono (Scheme.ΓSpecIso (X.left.presheaf.stalk x)).hom, ← Spec.map_comp,
    Scheme.Hom.comp_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc,
    fromSpecStalk_appTop_ΓSpecIso_hom]
  ext c
  rw [CommRingCat.comp_apply φ ψ, h]
  simp [stalkC, RingHom.algebraMap_toAlgebra, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]

/-- The generic point `Spec K → X → Spec ℂ` is `Spec` of the constants of `K`. -/
theorem fromSpecStalk_generic_comp_hom {R : CommRingCat} (φ : CommRingCat.of ℂ ⟶ R)
    (ψ : R ⟶ X.left.functionField)
    (h : ∀ c, ψ (φ c) = algebraMap ℂ X.left.functionField c) :
    X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom = Spec.map ψ ≫ Spec.map φ := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv,
    ← cancel_mono (Scheme.ΓSpecIso X.left.functionField).hom, ← Spec.map_comp,
    Scheme.Hom.comp_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc,
    fromSpecStalk_appTop_ΓSpecIso_hom]
  ext c
  rw [CommRingCat.comp_apply φ ψ, h]
  simp [RingHom.algebraMap_toAlgebra, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]

omit [IsIntegral X.left] in
/-- The composite `Spec 𝒪_{X,x} → X → Spec ℂ` is `Spec` of the structure map. -/
theorem fromSpecStalk_comp_hom' (x : X.left) :
    X.left.fromSpecStalk x ≫ X.hom = Spec.map (CommRingCat.ofHom (stalkC x)) := by
  rw [fromSpecStalk_comp_hom x (CommRingCat.ofHom (stalkC x)) (𝟙 _) fun _ ↦ rfl, Spec.map_id]
  erw [Category.id_comp]

/-- Existence part of the valuative criterion: a valuation subring of the function field that
contains `ℂ` dominates the local ring of some point.
Source: Hartshorne, *Algebraic Geometry*, II.4.7; Mathlib
`UniversallyClosed.eq_valuativeCriterion`. -/
theorem exists_point_of_valuationSubring [UniversallyClosed X.hom]
    (V : ValuationSubring X.left.functionField)
    (hV : ∀ c, algebraMap ℂ X.left.functionField c ∈ V) :
    ∃ P : X.left, ∃ φ : X.left.presheaf.stalk P ⟶ CommRingCat.of V, IsLocalHom φ.hom ∧
      ∀ s, algebraMap V X.left.functionField (φ s) =
        algebraMap (X.left.presheaf.stalk P) X.left.functionField s := by
  let ι : ℂ →+* V := (algebraMap ℂ X.left.functionField).codRestrict V hV
  let sq : ValuativeCommSq X.hom :=
    { R := V
      K := X.left.functionField
      i₁ := X.left.fromSpecStalk (genericPoint X.left)
      i₂ := Spec.map (CommRingCat.ofHom ι)
      commSq := ⟨fromSpecStalk_generic_comp_hom (CommRingCat.ofHom ι)
        (CommRingCat.ofHom (algebraMap V X.left.functionField)) fun _ ↦ rfl⟩ }
  have hex : (ValuativeCriterion.Existence ⊓ @QuasiCompact) X.hom :=
    UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed X.hom)
  obtain ⟨⟨ℓ, hl, -⟩⟩ := hex.1 sq
  refine ⟨ℓ (IsLocalRing.closedPoint V), Scheme.stalkClosedPointTo ℓ, inferInstance, ?_⟩
  set P := ℓ (IsLocalRing.closedPoint V)
  have hsp : genericPoint X.left ⤳ P := (genericPoint_spec X.left).specializes trivial
  have hℓ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ℓ
  have key : Spec.map (Scheme.stalkClosedPointTo ℓ ≫
      CommRingCat.ofHom (algebraMap V X.left.functionField)) ≫ X.left.fromSpecStalk P =
      Spec.map (X.left.presheaf.stalkSpecializes hsp) ≫ X.left.fromSpecStalk P := by
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Spec.map_comp, Category.assoc, hℓ]
    exact hl
  have := Spec.map_injective ((cancel_mono _).mp key)
  intro s
  exact congr($this s)

/-- Uniqueness part of the valuative criterion: two points with the same local ring inside the
function field coincide.
Source: Hartshorne, *Algebraic Geometry*, II.4.3; Mathlib `IsSeparated.valuativeCriterion`. -/
theorem eq_of_range_eq [IsSeparated X.hom] {P Q : X.left}
    [ValuationRing (X.left.presheaf.stalk P)]
    (h : (algebraMap (X.left.presheaf.stalk P) X.left.functionField).range =
      (algebraMap (X.left.presheaf.stalk Q) X.left.functionField).range) : P = Q := by
  let aP := algebraMap (X.left.presheaf.stalk P) X.left.functionField
  let aQ := algebraMap (X.left.presheaf.stalk Q) X.left.functionField
  let eP : X.left.presheaf.stalk P ≃+* aP.range := RingEquiv.ofBijective aP.rangeRestrict
    ⟨fun a b hab ↦ IsFractionRing.injective _ X.left.functionField (congrArg Subtype.val hab),
      aP.rangeRestrict_surjective⟩
  let eQ : X.left.presheaf.stalk Q ≃+* aQ.range := RingEquiv.ofBijective aQ.rangeRestrict
    ⟨fun a b hab ↦ IsFractionRing.injective _ X.left.functionField (congrArg Subtype.val hab),
      aQ.rangeRestrict_surjective⟩
  let e : X.left.presheaf.stalk Q ≃+* X.left.presheaf.stalk P :=
    eQ.trans ((RingEquiv.subringCongr h.symm).trans eP.symm)
  have he : ∀ t, aP (e t) = aQ t := by
    intro t
    have h1 : eP (e t) = RingEquiv.subringCongr h.symm (eQ t) := by simp [e]
    exact congrArg Subtype.val h1
  let ψ : X.left.presheaf.stalk Q ⟶ X.left.presheaf.stalk P := e.toCommRingCatIso.hom
  have hψ : IsLocalHom ψ.hom := isLocalHom_of_isIso ψ
  have hP : genericPoint X.left ⤳ P := (genericPoint_spec X.left).specializes trivial
  have hQ : genericPoint X.left ⤳ Q := (genericPoint_spec X.left).specializes trivial
  have hfacP : Spec.map (CommRingCat.ofHom aP) ≫ X.left.fromSpecStalk P =
      X.left.fromSpecStalk (genericPoint X.left) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hP
  have hfacQ : Spec.map (CommRingCat.ofHom aP) ≫ Spec.map ψ ≫ X.left.fromSpecStalk Q =
      X.left.fromSpecStalk (genericPoint X.left) := by
    rw [← Category.assoc, ← Spec.map_comp]
    have : ψ ≫ CommRingCat.ofHom aP = X.left.presheaf.stalkSpecializes hQ := by
      ext t; exact he t
    erw [this, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hC : ∀ c, e (stalkC Q c) = stalkC P c := fun c ↦
    IsFractionRing.injective _ X.left.functionField (by
      rw [he, algebraMap_stalkC, algebraMap_stalkC])
  have hfacR : (Spec.map ψ ≫ X.left.fromSpecStalk Q) ≫ X.hom = X.left.fromSpecStalk P ≫ X.hom := by
    rw [Category.assoc, fromSpecStalk_comp_hom', fromSpecStalk_comp_hom', ← Spec.map_comp]
    congr 1
    ext c
    exact hC c
  let sq : ValuativeCommSq X.hom :=
    { R := X.left.presheaf.stalk P
      domain := (inferInstance : IsDomain (X.left.presheaf.stalk P))
      K := X.left.functionField
      i₁ := X.left.fromSpecStalk (genericPoint X.left)
      i₂ := X.left.fromSpecStalk P ≫ X.hom
      commSq := ⟨by rw [← hfacP, Category.assoc]⟩ }
  have huniq := IsSeparated.valuativeCriterion (f := X.hom) sq
  have := congrArg CommSq.LiftStruct.l
    (huniq.elim (⟨X.left.fromSpecStalk P, hfacP, rfl⟩ : sq.commSq.LiftStruct)
      ⟨Spec.map ψ ≫ X.left.fromSpecStalk Q, hfacQ, hfacR⟩)
  have h1 := congrArg (fun f : Spec (X.left.presheaf.stalk P) ⟶ X.left ↦
    f (IsLocalRing.closedPoint _)) this
  simp only [Scheme.fromSpecStalk_closedPoint] at h1
  rw [h1]
  change X.left.fromSpecStalk Q (Spec.map ψ (IsLocalRing.closedPoint (X.left.presheaf.stalk P))) = Q
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- On a complete smooth curve, every proper valuation subring of the function field containing
`ℂ` is the local ring of a coheight-one point.
Source: Hartshorne, *Algebraic Geometry*, I.6.7 and II.4.7. -/
theorem exists_point_range_eq [UniversallyClosed X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsLocallyNoetherian X.left] (V : ValuationSubring X.left.functionField)
    (hV : ∀ c, algebraMap ℂ X.left.functionField c ∈ V) (hVtop : V ≠ ⊤) :
    ∃ P : X.left, Order.coheight P = 1 ∧ ∀ x, x ∈ V ↔
      ∃ s, algebraMap (X.left.presheaf.stalk P) X.left.functionField s = x := by
  obtain ⟨P, φ, -, hφ⟩ := exists_point_of_valuationSubring V hV
  have hsub : ∀ s, algebraMap (X.left.presheaf.stalk P) X.left.functionField s ∈ V :=
    fun s ↦ hφ s ▸ (φ s).2
  have hcoh : Order.coheight P = 1 := by
    have hle : Order.coheight P ≤ 1 :=
      SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := 1) P
    have hne : Order.coheight P ≠ 0 := by
      intro h0
      have : Ring.KrullDimLE 0 (X.left.presheaf.stalk P) := by
        rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight, h0]
        rfl
      have hfield := Ring.KrullDimLE.isField_of_isDomain (R := X.left.presheaf.stalk P)
      apply hVtop
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, b, hb, rfl⟩ :=
        IsFractionRing.div_surjective (A := X.left.presheaf.stalk P) x
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨c, hc⟩ := hfield.mul_inv_cancel hb0
      have : algebraMap (X.left.presheaf.stalk P) X.left.functionField a /
          algebraMap (X.left.presheaf.stalk P) X.left.functionField b =
          algebraMap (X.left.presheaf.stalk P) X.left.functionField (a * c) := by
        rw [div_eq_iff (by simpa using hb0), map_mul, mul_assoc, ← map_mul, mul_comm c, hc,
          map_one, mul_one]
      rw [this]
      exact hsub _
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  have := isDVR_stalk hcoh
  refine ⟨P, hcoh, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · exact exists_algebraMap_eq_of_mem_valuationSubring V hsub hVtop hx
  · rintro ⟨s, rfl⟩
    exact hsub s

end HodgeLean.Foundations.Curves
