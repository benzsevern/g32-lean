import HodgeLean.Foundations.Program.G32Native.WeilMarkedTorus

/-! Nondegeneracy of the original polarization under marked theta algebraization. -/
noncomputable section
set_option maxRecDepth 8000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

/-- The original integral Riemann form gives a nondegenerate rational degree-two class.
Source: Birkenhake–Lange, §§1.3, 2.2 and Theorem 4.5.1. -/
theorem weil_marked_torus_nondegenerate
    (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (E : LinearMap.BilinForm ℤ Λ) (hE : b2_IsRiemannForm Λ F E)
    (J : Λ →+ Λ) (hJ : ∀ x, J (J x) = (-3 : ℤ) • x)
    (hJF : F ≤ F.comap (b2_cplxMap J)) :
    IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf (weil_marked_torus Λ F hF E hE J hJ hJF).X)
        (weil_marked_torus Λ F hF E hE J hJ hJF).pol) := by
  let P := weil_marked_torus Λ F hF E hE J hJ hJF
  let e : Λ ≃+ b2_abelianLattice P.X := b5_periodEquiv Λ F hF E hE
  let Q := b4b_transportForm Λ P.X e E
  have hQ : b2_IsRiemannForm (b2_abelianLattice P.X) (b2_abelianF P.X) Q := by
    apply b4b_transportForm_riemann_aux Λ P.X e F
    · exact b5_period_filtration Λ F hF E hE
    · exact hE
  exact b2_abelian_nondegenerate P.X Q hQ

#print axioms weil_marked_torus_nondegenerate
end HodgeLean.Foundations.Program
