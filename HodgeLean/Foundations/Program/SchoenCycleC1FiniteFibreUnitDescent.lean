import HodgeLean.Foundations.Program.SchoenCycleC1FiniteFibreRationalUnitNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleC1FiniteSchemeComplexUnitDescent

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Pullback units at the complex points of one actual finite fibre give
a base unit on an arbitrarily small affine neighbourhood of that fibre. -/
theorem s2e_c1_finite_fibre_unit_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [IsDominant f.left]
    (y : ComplexPoint Y) (U : Y.left.Opens) (hy : y.underlying ∈ U)
    (t : Y.left.functionField) (ht : t ≠ 0) :
    let hg := s2e_c1_dominant_generic_point f.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      f.left.stalkMap (genericPoint X.left)).hom
    (∀ z : ComplexPoint X, Point.map f z = y →
      ∃ u : (X.left.presheaf.stalk z.underlying)ˣ,
        algebraMap (X.left.presheaf.stalk z.underlying) X.left.functionField (u : _) = φ t) →
    ∃ (V : Y.left.affineOpens) (hyV : y.underlying ∈ V.1), V.1 ≤ U ∧
      letI : Nonempty V.1 := ⟨⟨y.underlying, hyV⟩⟩
      ∃ v : Γ(Y.left, V.1)ˣ, Y.left.germToFunctionField V.1 (v : Γ(Y.left, V.1)) = t := by
  dsimp only
  let hg := s2e_c1_dominant_generic_point f.left
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    f.left.stalkMap (genericPoint X.left)).hom
  intro hlocal
  have hscheme (p : X.left) (hp : f.left p = y.underlying) :
      ∃ u : (X.left.presheaf.stalk p)ˣ,
        algebraMap (X.left.presheaf.stalk p) X.left.functionField (u : _) = φ t := by
    obtain ⟨z, hz, hfz⟩ := s2e_c1_finite_fibre_complex_representative X Y f y p hp
    exact (congrArg (fun q : X.left => ∃ u : (X.left.presheaf.stalk q)ˣ,
      algebraMap (X.left.presheaf.stalk q) X.left.functionField (u : _) = φ t) hz) ▸ hlocal z hfz
  obtain ⟨V, hyV, hVU, hV⟩ := s2e_c1_finite_fibre_rational_unit_neighbourhood
    f.left y.underlying U hy (φ t) hscheme
  letI : Nonempty V.1 := ⟨⟨y.underlying, hyV⟩⟩
  refine ⟨V, hyV, hVU, ?_⟩
  exact s2e_c1_finite_scheme_complex_unit_descent X Y f V.1 V.2 t ht
    (fun z hz => hV z.underlying hz)

end HodgeLean.Foundations.Program
