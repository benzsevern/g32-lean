import HodgeLean.Foundations.Program.SchoenSelectedGeometryModelAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- A holomorphic tower of compact curves with a faithful residual action has compatible algebraic models. -/
theorem s0_curve_model_tower
    (C Y Z G : Type) [Group G]
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]
    [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
    [MulAction G Y] [FaithfulSMul G Y]
    (qₐ : C → Y) (pₐ : Y → Z)
    (hq : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω qₐ)
    (hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω pₐ)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : Y ↦ g • y))
    (hinv : ∀ (g : G) (y : Y), pₐ (g • y) = pₐ y) :
    ∃ (C₀ Y₀ Z₀ : Over (Spec ↧ℂ)),
      ∃ (_ : IsIntegral C₀.left) (_ : Smooth C₀.hom) (_ : IsProjective C₀.hom),
      ∃ (_ : IsIntegral Y₀.left) (_ : Smooth Y₀.hom) (_ : IsProjective Y₀.hom),
      ∃ (_ : IsIntegral Z₀.left) (_ : Smooth Z₀.hom) (_ : IsProjective Z₀.hom),
      TopologicalSpace.dim C₀.left = 1 ∧ TopologicalSpace.dim Y₀.left = 1 ∧
      TopologicalSpace.dim Z₀.left = 1 ∧
      ∃ (eC : C ≃ₜ ComplexPoint C₀) (eY : Y ≃ₜ ComplexPoint Y₀)
        (eZ : Z ≃ₜ ComplexPoint Z₀),
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) ω eC ∧
      ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eC.symm ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) ω eY ∧
      ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eY.symm ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) ω eZ ∧
      ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eZ.symm ∧
      ∃ (q : C₀ ⟶ Y₀) (p : Y₀ ⟶ Z₀) (a : G → (Y₀ ⟶ Y₀)),
      (∀ x, Point.map q (eC x) = eY (qₐ x)) ∧
      (∀ y, Point.map p (eY y) = eZ (pₐ y)) ∧
      (∀ g y, Point.map (a g) (eY y) = eY (g • y)) ∧
      a 1 = 𝟙 Y₀ ∧ (∀ u v, a (u * v) = a v ≫ a u) ∧
      Function.Injective a ∧ (∀ g, a g ≫ p = p) := by
  obtain ⟨C₀, hCi, hCs, hCp, hCd, eC, hC, hCi'⟩ := s0_curve_model_exists C
  obtain ⟨Y₀, hYi, hYs, hYp, hYd, eY, hY, hYi'⟩ := s0_curve_model_exists Y
  obtain ⟨Z₀, hZi, hZs, hZp, hZd, eZ, hZ, hZi'⟩ := s0_curve_model_exists Z
  obtain ⟨q, hq'⟩ := s0_curve_model_map C₀ Y₀ eC eY hCi' hY qₐ hq
  obtain ⟨p, hp'⟩ := s0_curve_model_map Y₀ Z₀ eY eZ hYi' hZ pₐ hp
  obtain ⟨a, ha, ha1, ham, hai⟩ := s0_curve_model_action Y₀ eY hY hYi' hG
  exact ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, eC, eY, eZ, hC, hCi', hY, hYi', hZ, hZi',
    q, p, a, hq', hp', ha, ha1, ham, hai,
    s0_curve_model_action_invariant Y₀ Z₀ eY eZ a p pₐ ha hp' hinv⟩

#print axioms s0_curve_model_tower
end HodgeLean.Foundations.Program
