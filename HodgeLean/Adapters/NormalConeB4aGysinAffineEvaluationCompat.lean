import HodgeLean.Adapters.NormalConeB4aGysinOpenEvaluation

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- The affine point homeomorphism evaluates the original affine sections. -/
theorem a3b4a_gysin_affine_point_homeomorph_apply
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of ℂ))
    (U : X.Opens) (hU : IsAffineOpen U)
    (w : {w : ComplexPoint (Over.mk q) // w.underlying ∈ U}) (s : Γ(X, U)) :
    letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
    a3b4a_gysin_affine_point_homeomorph q U hU w s = Point.evaluate U s w.val := by
  letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
  let z := (ComplexPoint.openHomeomorph (Over.mk q) U).symm w
  have hz : Point.map (ComplexPoint.openInclusion (Over.mk q) U) z = w.val :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph (Over.mk q) U).apply_symm_apply w)
  have he : hU.isoSpec.hom ≫ ComplexPoint.affineSpecStructureMap Γ(X, U) = U.ι ≫ q := by
    apply (cancel_epi hU.isoSpec.inv).mp
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, hU.isoSpec_inv_ι,
      a3b4a_gysin_affine_fromSpec_over q U hU]
  let f : ComplexPoint.openScheme (Over.mk q) U ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap Γ(X, U)) := Over.homMk hU.isoSpec.hom he
  change ComplexPoint.affineSpecEquiv Γ(X, U) (Point.map f z) s = _
  rw [ComplexPoint.affineSpecEquiv_apply, Point.evaluate_map]
  change Point.evaluate ⊤ (hU.isoSpec.hom.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv s)) z = _
  rw [hU.isoSpec_hom_appTop]
  change Point.evaluate ⊤ (U.topIso.inv
    ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv s))) z = _
  have hc := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv_hom_id) s
  change (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv s) = s at hc
  rw [hc]
  exact (a3b4a_gysin_open_top_evaluation q U s z).symm.trans
    (congrArg (Point.evaluate U s) hz)

end HodgeLean.Adapters
