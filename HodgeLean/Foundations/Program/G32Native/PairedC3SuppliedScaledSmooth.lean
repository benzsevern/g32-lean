import HodgeLean.Foundations.Program.G32Native.PairedC3ScaledProjectionSmooth
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualCoefficientAlgebra
import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedResidualEquations

/-! # Smoothness of the specified residual ratio over the original base -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- Supplied binomial equations and a smooth residual base make every unit
multiple of the original ratio a smooth affine-line morphism. -/
theorem pairedC3_supplied_scaled_smooth
    (X Y : Over (Spec ↧ℂ)) (p : Y ⟶ X) (M : X.left.IdealSheafData)
    (U : X.left.affineOpens) (V : Y.left.affineOpens)
    (hV : V.1 ≤ p.left ⁻¹ᵁ U.1)
    (u v : Γ(X.left, U)) (hu : u ∈ M.ideal U) (hv : v ∈ M.ideal U)
    (s : Γ(Y.left, V))
    (hsurj : Function.Surjective (eval₂RingHom (p.left.appLE U.1 V.1 hV).hom s))
    (hker : RingHom.ker (eval₂RingHom (p.left.appLE U.1 V.1 hV).hom s) =
      Ideal.span {C u - Polynomial.X * C v})
    (α : (Γ(X.left, U) ⧸ M.ideal U)ˣ)
    (hs : Smooth (M.subschemeι ≫ X.hom)) :
    let pB := (M.comap p.left).subschemeCover.f V ≫
      (M.comap p.left).subschemeι ≫ Y.hom
    letI := pairedC3SpecAlgebra pB
    let b := pairedC3AffineResidualCoefficient p.left M U V hV
    Smooth (Spec.map (CommRingCat.ofHom (eval₂RingHom
      (algebraMap ℂ (Γ(Y.left, V) ⧸ (M.comap p.left).ideal V))
      (b (α : Γ(X.left, U) ⧸ M.ideal U) *
        Ideal.Quotient.mk ((M.comap p.left).ideal V) s)))) := by
  let pA := M.subschemeCover.f U ≫ M.subschemeι ≫ X.hom
  let pB := (M.comap p.left).subschemeCover.f V ≫
    (M.comap p.left).subschemeι ≫ Y.hom
  letI := pairedC3SpecAlgebra pA
  letI := pairedC3SpecAlgebra pB
  let b := pairedC3ResidualCoefficientAlgHom X Y p M U V hV
  obtain ⟨E, _, hcoeff, hratio⟩ := pairedC3_supplied_residual_equations
    p.left M U V hV u v hu hv s hsurj hker
  have hb (a : Γ(X.left, U) ⧸ M.ideal U) : E (b a) = C a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hcoeff a
  have hc (r : ℂ) :
      E (algebraMap ℂ (Γ(Y.left, V) ⧸ (M.comap p.left).ideal V) r) =
        C (algebraMap ℂ (Γ(X.left, U) ⧸ M.ideal U) r) := by
    rw [← b.commutes r]
    exact hb _
  have hz : E (b (α : Γ(X.left, U) ⧸ M.ideal U) *
      Ideal.Quotient.mk ((M.comap p.left).ideal V) s) =
        C (α : Γ(X.left, U) ⧸ M.ideal U) * Polynomial.X := by
    rw [map_mul, hratio, hb]
  exact pairedC3_scaled_projection_smooth ℂ _ _ E
    (algebraMap ℂ (Γ(Y.left, V) ⧸ (M.comap p.left).ideal V))
    hc α _ hz (pairedC3_residual_coefficient_base_smooth X M U hs)

#print axioms pairedC3_supplied_scaled_smooth
end HodgeLean.Foundations.Program.G32Native
