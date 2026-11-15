import HodgeLean.Foundations.Program.SchoenGluedProjQuotientProjective
import HodgeLean.Foundations.Program.SchoenGluedQuotientBaseIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual invariant Proj quotient is projective over an identified coefficient field. -/
theorem s2_gluedProjQuotient_projective_coefficientField {K A G : Type}
    [Field K] [Infinite K] [CommRing A] [IsDomain A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsNoetherianRing (𝒜 0)]
    [Algebra.FiniteType (𝒜 0) A] [IsIntegral (Proj 𝒜)]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj 𝒜)))]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a)
    (e : 𝒜 0 ≃+* K)
    (hs : ∀ g : G, (s2_projAction 𝒜 hgrade g).asIso.hom ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map e.symm.toCommRingCatIso.hom) =
        Proj.toSpecZero 𝒜 ≫ Spec.map e.symm.toCommRingCatIso.hom) :
    IsProjective (s2_gluedQuotientStructure
      (Proj.toSpecZero 𝒜 ≫ Spec.map e.symm.toCommRingCatIso.hom) G
      (s2_projAction 𝒜 hgrade) hs (s2_proj_invariantAffineCover 𝒜 hgrade hK)) := by
  haveI := s2_gluedProjQuotient_projective 𝒜 hgrade hK hzero
  exact s2_gluedQuotientStructure_projective_baseIso G (s2_projAction 𝒜 hgrade)
    (s2_proj_invariantAffineCover 𝒜 hgrade hK) (Proj.toSpecZero 𝒜)
    (s2_projAction_toSpecZero 𝒜 hgrade hK hzero)
    (Spec.map e.symm.toCommRingCatIso.hom) hs

end HodgeLean.Foundations.Program
