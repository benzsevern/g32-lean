import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualCoordinateRestriction

/-! # Actual affine restriction maps on residual quotient rings -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction on the original residual quotient rings. -/
def pairedC3AffineResidualRestriction {X : Scheme} (I : X.IdealSheafData)
    (V W : X.affineOpens) (hWV : W.1 ≤ V.1) :
    (Γ(X, V) ⧸ I.ideal V) →+* (Γ(X, W) ⧸ I.ideal W) :=
  Ideal.Quotient.lift (I.ideal V)
    ((Ideal.Quotient.mk (I.ideal W)).comp
      (X.presheaf.map (homOfLE hWV).op).hom)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (I.ideal_le_comap_ideal hWV ha))

/-- The base coefficient map on an actual residual affine open. -/
def pairedC3AffineResidualCoefficient {X Y : Scheme} (p : Y ⟶ X)
    (M : X.IdealSheafData) (U : X.affineOpens) (V : Y.affineOpens)
    (hV : V.1 ≤ p ⁻¹ᵁ U.1) :
    (Γ(X, U) ⧸ M.ideal U) →+* (Γ(Y, V) ⧸ (M.comap p).ideal V) :=
  Ideal.Quotient.lift (M.ideal U)
    ((Ideal.Quotient.mk ((M.comap p).ideal V)).comp (p.appLE U.1 V.1 hV).hom)
    (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [HodgeLean.Adapters.IntersectionProductScaf_comap_ideal_affine_charts p M U V hV]
      exact Ideal.mem_map_of_mem _ ha)

/-- Actual restriction of coefficient sections commutes with the quotient
maps. This retains the original morphism's section restriction identity. -/
theorem pairedC3_affine_residual_restriction_coefficients
    {X Y : Scheme} (p : Y ⟶ X) (M : X.IdealSheafData)
    (U : X.affineOpens) (V W : Y.affineOpens)
    (hV : V.1 ≤ p ⁻¹ᵁ U.1) (hWV : W.1 ≤ V.1) (a : Γ(X, U)) :
    pairedC3AffineResidualRestriction (M.comap p) V W hWV
      (Ideal.Quotient.mk ((M.comap p).ideal V) ((p.appLE U.1 V.1 hV).hom a)) =
      pairedC3AffineResidualCoefficient p M U W (hWV.trans hV)
        (Ideal.Quotient.mk (M.ideal U) a) := by
  change Ideal.Quotient.mk ((M.comap p).ideal W)
      ((Y.presheaf.map (homOfLE hWV).op).hom ((p.appLE U.1 V.1 hV).hom a)) =
    Ideal.Quotient.mk ((M.comap p).ideal W)
      ((p.appLE U.1 W.1 (hWV.trans hV)).hom a)
  exact congrArg (Ideal.Quotient.mk ((M.comap p).ideal W))
    (congrArg (fun F => F.hom a) (p.appLE_map hV (homOfLE hWV).op))

/-- In supplied polynomial coordinates, the actual affine restriction map
is evaluation at the restricted original ratio with the actual coefficient map. -/
theorem pairedC3_affine_residual_coordinate_restriction
    {X Y : Scheme} (p : Y ⟶ X) (M : X.IdealSheafData)
    (U : X.affineOpens) (V W : Y.affineOpens)
    (hV : V.1 ≤ p ⁻¹ᵁ U.1) (hWV : W.1 ≤ V.1) (t : Γ(Y, V))
    (E : (Γ(Y, V) ⧸ (M.comap p).ideal V) ≃+* (Γ(X, U) ⧸ M.ideal U)[X])
    (hc : ∀ a, E (Ideal.Quotient.mk ((M.comap p).ideal V)
      ((p.appLE U.1 V.1 hV).hom a)) = C (Ideal.Quotient.mk (M.ideal U) a))
    (ht : E (Ideal.Quotient.mk ((M.comap p).ideal V) t) = Polynomial.X) :
    (pairedC3AffineResidualRestriction (M.comap p) V W hWV).comp E.symm.toRingHom =
      eval₂RingHom (pairedC3AffineResidualCoefficient p M U W (hWV.trans hV))
        (Ideal.Quotient.mk ((M.comap p).ideal W)
          ((Y.presheaf.map (homOfLE hWV).op).hom t)) := by
  apply pairedC3_residual_coordinate_restriction (M.ideal U) ((M.comap p).ideal V)
    (p.appLE U.1 V.1 hV).hom t E hc ht
  exact pairedC3_affine_residual_restriction_coefficients p M U V W hV hWV

#print axioms pairedC3AffineResidualRestriction
#print axioms pairedC3AffineResidualCoefficient
#print axioms pairedC3_affine_residual_restriction_coefficients
#print axioms pairedC3_affine_residual_coordinate_restriction
end HodgeLean.Foundations.Program.G32Native
