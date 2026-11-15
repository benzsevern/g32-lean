import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedResidualChart
import HodgeLean.Foundations.Program.G32Native.PairedC3ReesEquationIso

/-! # Residual coordinates directly from the supplied Rees equations -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native

/-- The equations exported by a supplied chart determine its residual
coordinates on every polynomial representative, retaining the original
coefficient map and ratio.
Source: Hartshorne, Algebraic Geometry, II.7.13; Fulton, Intersection Theory, B.6. -/
theorem pairedC3_supplied_residual_equations
    {X Y : Scheme} (p : Y ⟶ X) (M : X.IdealSheafData)
    (U : X.affineOpens) (V : Y.affineOpens) (hV : V.1 ≤ p ⁻¹ᵁ U.1)
    (u v : Γ(X, U)) (hu : u ∈ M.ideal U) (hv : v ∈ M.ideal U)
    (s : Γ(Y, V))
    (hsurj : Function.Surjective (eval₂RingHom (p.appLE U.1 V.1 hV).hom s))
    (hker : RingHom.ker (eval₂RingHom (p.appLE U.1 V.1 hV).hom s) =
      Ideal.span {C u - Polynomial.X * C v}) :
    ∃ E : (Γ(Y, V) ⧸ (M.comap p).ideal V) ≃+* (Γ(X, U) ⧸ M.ideal U)[X],
      (∀ a : Γ(X, U)[X],
        E (Ideal.Quotient.mk ((M.comap p).ideal V)
          (eval₂ (p.appLE U.1 V.1 hV).hom s a)) =
            a.map (Ideal.Quotient.mk (M.ideal U))) ∧
      (∀ a : Γ(X, U), E (Ideal.Quotient.mk ((M.comap p).ideal V)
        ((p.appLE U.1 V.1 hV).hom a)) = C (Ideal.Quotient.mk (M.ideal U) a)) ∧
      E (Ideal.Quotient.mk ((M.comap p).ideal V) s) = Polynomial.X := by
  let f := (p.appLE U.1 V.1 hV).hom
  let e := pairedC3ReesEquationEquiv f u v s hsurj hker
  have he : e.toRingHom.comp (coeff u v) = f := by
    ext a
    exact paired_c3_rees_equation_constants f u v s hsurj hker a
  obtain ⟨E, hE, _⟩ := pairedC3_supplied_residual_chart p M U V hV u v hu hv e he
  have hpoly (a : Γ(X, U)[X]) :
      E (Ideal.Quotient.mk ((M.comap p).ideal V) (eval₂ f s a)) =
        a.map (Ideal.Quotient.mk (M.ideal U)) := by
    exact (hE (Ideal.Quotient.mk _ a)).trans
      (pairedC3_residual_chart_polynomial u v (M.ideal U) hu hv a)
  refine ⟨E, hpoly, ?_, ?_⟩
  · intro a
    simpa only [eval₂_C, Polynomial.map_C] using hpoly (C a)
  · simpa only [eval₂_X, Polynomial.map_X] using hpoly Polynomial.X

#print axioms pairedC3_supplied_residual_equations
end HodgeLean.Foundations.Program.G32Native
