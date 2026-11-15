import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! # Holomorphic transport through algebraic open inclusions

Route: extend each regular coordinate section from the open subscheme to
its ambient image using the open-immersion section isomorphism. F4 makes
these evaluations holomorphic, and the coordinate criterion identifies the
inverse map on the analytic open as holomorphic.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of an algebraic open inclusion is holomorphic on its analytic
image, for the frozen F4 analytifications. -/
theorem a3b4a_classOpenInverse_isHolomorphic
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (U : X.left.Opens)
    [LocallyOfFiniteType (ComplexPoint.openScheme X U).hom]
    [QuasiCompact (ComplexPoint.openScheme X U).hom]
    [IsSeparated (ComplexPoint.openScheme X U).hom] :
    an_IsHom
      (anrem_openSpace (f4_analytification X) (Point.isOpen_overOpen (X := X) U))
      (f4_analytification (ComplexPoint.openScheme X U))
      (ComplexPoint.openHomeomorph X U).symm := by
  let Y := ComplexPoint.openScheme X U
  let O : Set (ComplexPoint X) := Point.overOpen U
  let e := ComplexPoint.openHomeomorph X U
  let S := anrem_openSpace (f4_analytification X) (Point.isOpen_overOpen (X := X) U)
  apply a3b4a_class_isHom_of_coordinate_functions S (f4_analytification Y) e.symm e.symm.continuous
  intro j k
  let V := j.1.U.1
  let s := j.1.coord k
  let W := U.ι ''ᵁ V
  let t := (U.ι.appIso V).inv s
  have he (w : O) : Point.map (ComplexPoint.openInclusion X U) (e.symm w) = w.1 :=
    congrArg Subtype.val (e.apply_symm_apply w)
  let D : Set O := e.symm ⁻¹' (Point.overOpen V : Set (ComplexPoint Y))
  have hsub : D ⊆ (Subtype.val ⁻¹' (Point.overOpen W : Set (ComplexPoint X))) := by
    intro w hw
    change w.1.underlying ∈ W
    rw [← he w, Point.underlying_map]
    exact ⟨(e.symm w).underlying, hw, rfl⟩
  have hh := anrem_isHolFun_openSpace (f4_analytification X)
    (Point.isOpen_overOpen (X := X) U) (f4_isHolFun_evaluate X W t)
  have hh' := anrem_isHolFun_restrict S hsub hh
  change S.IsHolFun (fun w : D => Point.evaluate V s (e.symm w))
  convert hh' using 1
  funext w
  have hv := ComplexPoint.evaluate_openEquiv X U s (e.symm w.1)
  rw [he w.1] at hv
  exact hv.symm

/-- A function on an ambient open contained in an algebraic open is
holomorphic whenever its pullback to that open subscheme is holomorphic. -/
theorem a3b4a_classHolomorphic_of_openInclusion
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (U : X.left.Opens)
    [LocallyOfFiniteType (ComplexPoint.openScheme X U).hom]
    [QuasiCompact (ComplexPoint.openScheme X U).hom]
    [IsSeparated (ComplexPoint.openScheme X U).hom]
    {V : Set (ComplexPoint X)} (hV : IsOpen V) (hVU : V ⊆ Point.overOpen U) (g : V → ℂ)
    (hg : (f4_analytification (ComplexPoint.openScheme X U)).IsHolFun
      (fun y : Point.map (ComplexPoint.openInclusion X U) ⁻¹' V =>
        g ⟨Point.map (ComplexPoint.openInclusion X U) y, y.2⟩)) :
    (f4_analytification X).IsHolFun g := by
  let Y := ComplexPoint.openScheme X U
  let O : Set (ComplexPoint X) := Point.overOpen U
  let e := ComplexPoint.openHomeomorph X U
  let f := Point.map (ComplexPoint.openInclusion X U)
  let S := anrem_openSpace (f4_analytification X) (Point.isOpen_overOpen (X := X) U)
  have he (w : O) : f (e.symm w) = w.1 :=
    congrArg Subtype.val (e.apply_symm_apply w)
  have hsub : (Subtype.val ⁻¹' V : Set O) ⊆ e.symm ⁻¹' (f ⁻¹' V) := by
    intro w hw
    change f (e.symm w) ∈ V
    rw [he w]
    exact hw
  have hh := (a3b4a_classOpenInverse_isHolomorphic X U).2
    (f ⁻¹' V) (hV.preimage (Point.continuous_map (ComplexPoint.openInclusion X U)))
    (fun y : f ⁻¹' V => g ⟨f y, y.2⟩) hg
  have hh' := anrem_isHolFun_restrict S hsub hh
  apply a3b4a_classHolomorphic_of_openSpace (f4_analytification X)
    (Point.isOpen_overOpen (X := X) U) hVU g
  convert hh' using 1
  funext y
  congr 1
  exact Subtype.ext (he y.1).symm

end HodgeLean.Adapters
