import HodgeLean.Foundations.Program.SchoenTowerI2bGenericAction
import HodgeLean.Foundations.Program.SchoenTowerI2bGenericSuppliers

/-! Generic stalks of the retained normalizations in the original field.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant field source sends its unique point to the generic point.
Source: density of its singleton image and uniqueness of a generic point. -/
theorem s2v_i2b_fieldSource_genericPoint
    {K : Type} [Field K] (X : Scheme) [IrreducibleSpace X]
    (f : Spec ↧K ⟶ X) [IsDominant f] :
    f (IsLocalRing.closedPoint K) = genericPoint X := by
  have hr : Set.range f = {f (IsLocalRing.closedPoint K)} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact congrArg f (Subsingleton.elim y (IsLocalRing.closedPoint K))
    · intro hx
      exact ⟨IsLocalRing.closedPoint K, (Set.mem_singleton_iff.mp hx).symm⟩
  apply IsGenericPoint.eq ?_ (genericPoint_spec X)
  rw [isGenericPoint_def, ← hr]
  exact f.denseRange.closure_range

/-- A generic field parametrization is a stalk isomorphism when its composite is one.
Source: injectivity of maps from fields and surjectivity of the composite. -/
theorem s2v_i2b_genericSource_stalk_iso_of_comp
    {K : Type} [Field K] (X Y : Scheme) [IsIntegral X]
    (f : Spec ↧K ⟶ X) [IsDominant f] (w : X ⟶ Y)
    [IsIso (Scheme.stalkClosedPointTo (f ≫ w))] :
    IsIso (Scheme.stalkClosedPointTo f) := by
  have hg := s2v_i2b_fieldSource_genericPoint X f
  haveI : IsSimpleRing (X.presheaf.stalk (f (IsLocalRing.closedPoint K))) := by
    rw [hg]
    exact inferInstanceAs (IsSimpleRing X.functionField)
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo f).hom := by
    intro x
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.stalkClosedPointTo (f ≫ w))).2 x
    refine ⟨(w.stalkMap (f (IsLocalRing.closedPoint K))).hom a, ?_⟩
    change (w.stalkMap (f (IsLocalRing.closedPoint K)) ≫ Scheme.stalkClosedPointTo f).hom a = x
    rw [← Scheme.stalkClosedPointTo_comp]
    exact ha
  let e := (RingEquiv.ofBijective (Scheme.stalkClosedPointTo f).hom
    ⟨(Scheme.stalkClosedPointTo f).hom.injective, hsurj⟩).toCommRingCatIso
  exact inferInstanceAs (IsIso e.hom)

/-- A field source whose point-stalk map is an isomorphism is a monomorphism.
Source: factorization through the spectrum of the image stalk. -/
theorem s2v_i2b_genericSource_mono
    {K : Type} [Field K] (X : Scheme) (f : Spec ↧K ⟶ X)
    [IsIso (Scheme.stalkClosedPointTo f)] : Mono f := by
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk f]
  infer_instance

/-- Every dominant field-valued map factors through the retained generic parametrization.
Source: the stalk factorization of a field-valued scheme morphism. -/
theorem s2v_i2b_factor_through_genericSource
    {K : Type} [Field K] (X : Scheme) [IrreducibleSpace X]
    (q : Spec ↧K ⟶ X) [IsDominant q] [IsIso (Scheme.stalkClosedPointTo q)]
    (f : Spec ↧K ⟶ X) [IsDominant f] :
    ∃ σ : Spec ↧K ⟶ Spec ↧K, σ ≫ q = f := by
  have hp : f (IsLocalRing.closedPoint K) = q (IsLocalRing.closedPoint K) :=
    (s2v_i2b_fieldSource_genericPoint X f).trans (s2v_i2b_fieldSource_genericPoint X q).symm
  let a : X.presheaf.stalk (q (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K :=
    eqToHom (congrArg (fun x => X.presheaf.stalk x) hp.symm) ≫ Scheme.stalkClosedPointTo f
  have hfa : Spec.map a ≫ X.fromSpecStalk (q (IsLocalRing.closedPoint K)) = f := by
    dsimp only [a]
    rw [Spec.map_comp, Category.assoc, s2v_i2b_fromSpecStalk_transport X hp,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  let t : Spec ↧K ⟶ Spec (X.presheaf.stalk (q (IsLocalRing.closedPoint K))) :=
    Spec.map (Scheme.stalkClosedPointTo q)
  haveI : IsIso t := inferInstanceAs (IsIso (Spec.map (Scheme.stalkClosedPointTo q)))
  have ht : t ≫ X.fromSpecStalk (q (IsLocalRing.closedPoint K)) = q :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk q
  have htinv : inv t ≫ q = X.fromSpecStalk (q (IsLocalRing.closedPoint K)) := by
    calc
      inv t ≫ q = inv t ≫ (t ≫ X.fromSpecStalk (q (IsLocalRing.closedPoint K))) :=
        congrArg (fun g : Spec ↧K ⟶ X => inv t ≫ g) ht.symm
      _ = X.fromSpecStalk (q (IsLocalRing.closedPoint K)) := by
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  refine ⟨Spec.map a ≫ inv t, ?_⟩
  rw [Category.assoc, htinv, hfa]

/-- Equality after a retained transition detects equality of dominant field-valued lifts.
Source: factorization through generic parametrizations and monomorphy of the preceding source. -/
theorem s2v_i2b_genericSource_lifts_unique
    {K : Type} [Field K] (X Y : Scheme) [IrreducibleSpace X]
    (q : Spec ↧K ⟶ X) [IsDominant q] [IsIso (Scheme.stalkClosedPointTo q)]
    (q' : Spec ↧K ⟶ Y) [Mono q'] (w : X ⟶ Y) (hw : q ≫ w = q')
    (f g : Spec ↧K ⟶ X) [IsDominant f] [IsDominant g]
    (hfg : f ≫ w = g ≫ w) : f = g := by
  obtain ⟨a, ha⟩ := s2v_i2b_factor_through_genericSource X q f
  obtain ⟨b, hb⟩ := s2v_i2b_factor_through_genericSource X q g
  have hab : a = b := by
    apply (cancel_mono q').mp
    calc
      a ≫ q' = (a ≫ q) ≫ w := by rw [Category.assoc, hw]
      _ = f ≫ w := congrArg (fun t : Spec ↧K ⟶ X => t ≫ w) ha
      _ = g ≫ w := hfg
      _ = (b ≫ q) ≫ w := congrArg (fun t : Spec ↧K ⟶ X => t ≫ w) hb.symm
      _ = b ≫ q' := by rw [Category.assoc, hw]
  exact ha.symm.trans ((congrArg (fun t : Spec ↧K ⟶ Spec ↧K => t ≫ q) hab).trans hb)

end HodgeLean.Foundations.Program
