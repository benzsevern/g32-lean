import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs

/-! # Continuous coefficient identifications of the original normal bundle -/
noncomputable section
open CategoryTheory AlgebraicGeometry Bundle
namespace HodgeLean.Foundations.Program.G32Native

/-- The fibre and continuity fields supplied by U10, without its differential construction.
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, §7.1,
complex normal bundles and their continuous linear identifications. -/
structure CoefficientNormalIdentification (G : CanonicalAbelGeometry) where
  fibre : ∀ x : ComplexPoint G.Q, canonicalNormalFibre G x ≃ₗ[ℂ]
    (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator
  continuous_forward : @Continuous
    (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
    (TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
    (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k) (coefficientTotalTopology G)
    (fun z => ⟨z.proj, fibre z.proj z.2⟩)
  continuous_inverse : @Continuous
    (TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
    (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
    (coefficientTotalTopology G) (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k)
    (fun z => ⟨z.proj, (fibre z.proj).symm z.2⟩)

end HodgeLean.Foundations.Program.G32Native
