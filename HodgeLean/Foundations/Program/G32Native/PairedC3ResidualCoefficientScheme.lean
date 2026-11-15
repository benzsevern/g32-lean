import HodgeLean.Foundations.Program.G32Native.PairedC3AffineResidualRestriction

/-! # The residual coefficient map over the original scheme -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The quotient coefficient map retains the original ambient morphism. -/
theorem pairedC3_residual_coefficient_scheme
    {X Y : Scheme} (p : Y ⟶ X) (M : X.IdealSheafData)
    (U : X.affineOpens) (V : Y.affineOpens) (hV : V.1 ≤ p ⁻¹ᵁ U.1) :
    Spec.map (CommRingCat.ofHom (pairedC3AffineResidualCoefficient p M U V hV)) ≫
      M.subschemeCover.f U ≫ M.subschemeι =
      (M.comap p).subschemeCover.f V ≫ (M.comap p).subschemeι ≫ p := by
  rw [M.subschemeCover_map_subschemeι,
    ← Category.assoc ((M.comap p).subschemeCover.f V),
    (M.comap p).subschemeCover_map_subschemeι,
    M.glueDataObjι_ι, (M.comap p).glueDataObjι_ι, Category.assoc]
  rw [← Spec.map_comp_assoc]
  have hq : CommRingCat.ofHom (Ideal.Quotient.mk (M.ideal U)) ≫
      CommRingCat.ofHom (pairedC3AffineResidualCoefficient p M U V hV) =
      p.appLE U.1 V.1 hV ≫
        CommRingCat.ofHom (Ideal.Quotient.mk ((M.comap p).ideal V)) := by
    ext a
    rfl
  rw [hq, Spec.map_comp, Category.assoc, U.2.SpecMap_appLE_fromSpec p V.2 hV]

#print axioms pairedC3_residual_coefficient_scheme
end HodgeLean.Foundations.Program.G32Native
