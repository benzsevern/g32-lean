import HodgeLean.Foundations.Program.G32Native.CanonicalAbelGeometry

/-! # Point equations for descent along the retained quotient -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native

/-- An algebraic point map that factors through the retained quotient descends with that equation. -/
theorem canonical_quotient_descend_pointMap (G : CanonicalAbelGeometry)
    (T : Over (Spec ↧ℂ)) [LocallyOfFiniteType T.hom] [IsSeparated T.hom] (f : ComplexPoint G.B → ComplexPoint T)
    (v : g3_power G.Z (2 * G.k) ⟶ T)
    (hv : Point.map v = fun u => f (Point.map G.γ u)) :
    ∃ vB : G.B ⟶ T, Point.map vB = f := by
  have hinv : ∀ σ, s2_permute G.Z (2 * G.k) σ ≫ v = v := by
    intro σ
    apply b55_hom_ext
    funext u
    have he : Point.map G.γ (Point.map (s2_permute G.Z (2 * G.k) σ) u) =
        Point.map G.γ u :=
      (Point.map_comp_apply (s2_permute G.Z (2 * G.k) σ) G.γ u).symm.trans
        (congrArg (fun w => Point.map w u) (G.invariantγ σ))
    exact (Point.map_comp_apply _ _ u).trans
      ((congrFun hv _).trans ((congrArg f he).trans (congrFun hv u).symm))
  obtain ⟨vB, hvB, _⟩ := G.quotientγ T v hinv
  refine ⟨vB, funext fun b => ?_⟩
  obtain ⟨u, rfl⟩ := G.surjectiveγ b
  exact (Point.map_comp_apply G.γ vB u).symm.trans
    ((congrArg (fun w => Point.map w u) hvB).trans (congrFun hv u))

#print axioms canonical_quotient_descend_pointMap
end HodgeLean.Foundations.Program.G32Native
