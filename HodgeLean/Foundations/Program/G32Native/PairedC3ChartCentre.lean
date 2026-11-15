import HodgeLean.Foundations.Program.SchoenCycleC1AffineComapSections

/-! # The exceptional centre ideal in either supplied Rees chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The ratio equation makes the actual pulled-back paired centre ideal
principal on the chart, with its original branch generator.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_chart_centre
    {X Y : Scheme} (σ : X ⟶ Y) (D E : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ σ ⁻¹ᵁ U.1)
    (u v : Γ(Y, U)) (t : Γ(X, V))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v})
    (hrel : (σ.appLE U.1 V.1 hVU).hom v = t * (σ.appLE U.1 V.1 hVU).hom u) :
    ((D ⊔ E).comap σ).ideal V = Ideal.span {(σ.appLE U.1 V.1 hVU).hom u} := by
  rw [s2e_c1_affine_comap_appLE σ (D ⊔ E) U V hVU]
  change Ideal.map _ (D.ideal U ⊔ E.ideal U) = _
  rw [hu, hv, Ideal.map_sup, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton]
  apply sup_eq_left.mpr
  apply Ideal.span_le.mpr
  intro b hb
  obtain rfl := Set.mem_singleton_iff.mp hb
  rw [hrel]
  exact Ideal.mul_mem_left _ t (Ideal.subset_span (Set.mem_singleton _))

#print axioms paired_c3_chart_centre
end HodgeLean.Foundations.Program.G32Native
