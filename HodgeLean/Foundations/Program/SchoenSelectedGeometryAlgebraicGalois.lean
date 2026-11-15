import HodgeLean.Foundations.Program.SchoenSelectedGeometryQuotientBetti
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAlgebraicSquare
import HodgeLean.Foundations.Program.SchoenSelectedGeometryBettiSquare

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Algebraized quotient pullback has the invariant image under the analytic deck action. -/
theorem s0_algebraic_galois_range
    {C Y G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f)
    (X Z : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (eC : C ≃ₜ ComplexPoint X) (eY : Y ≃ₜ ComplexPoint Z)
    (q : X ⟶ Z) (hq : ∀ z, Point.map q (eC z) = eY (f z)) (a : HQ X 1) :
    let B := (cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩)).comp
      (cupComparison X 1).toLinearMap
    a ∈ LinearMap.range (homPullback q 1) ↔
      ∀ g : G, cohomologyMap ℚ 1
        (TopCat.ofHom ⟨fun x : C ↦ g • x, (hG g).continuous⟩) (B a) = B a := by
  let B := (cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩)).comp
    (cupComparison X 1).toLinearMap
  have hB : Function.Injective B :=
    (cohomologyHomeomorphEquiv eC 1).symm.injective.comp (cupComparison X 1).injective
  have hs := s0_algebraic_pullback_square ⟨eC, eC.continuous⟩ ⟨eY, eY.continuous⟩
    ⟨f, hf.continuous⟩ q hq 1
  change a ∈ LinearMap.range (homPullback q 1) ↔ _
  rw [← s0_galois_pullback_range hG f hf hgal (B a)]
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨cohomologyMap ℚ 1 (TopCat.ofHom ⟨eY, eY.continuous⟩)
      (cupComparison Z 1 b), (hs b).symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨z, hz⟩ := ((cohomologyHomeomorphEquiv eY 1).symm.surjective.comp
      (cupComparison Z 1).surjective) b
    change cohomologyMap ℚ 1 (TopCat.ofHom ⟨eY, eY.continuous⟩)
      (cupComparison Z 1 z) = b at hz
    refine ⟨z, hB ?_⟩
    change cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩)
      (cupComparison X 1 (homPullback q 1 z)) = B a
    rw [hs, hz]
    exact hb

#print axioms s0_algebraic_galois_range
end HodgeLean.Foundations.Program
