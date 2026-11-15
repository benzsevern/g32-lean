import HodgeLean.Foundations.Program.SchoenCycleC1AffineRationalUnitComplexStalks
import HodgeLean.Foundations.Program.SchoenCycleC1FiniteSchemeUnitDescent

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Actual pullback units at all complex inverse-image points descend to
one unit on the original smooth base affine chart. -/
theorem s2e_c1_finite_scheme_complex_unit_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [IsDominant f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (t : Y.left.functionField) (ht : t ≠ 0) :
    let hg := s2e_c1_dominant_generic_point f.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      f.left.stalkMap (genericPoint X.left)).hom
    (∀ x : ComplexPoint X, x.underlying ∈ f.left ⁻¹ᵁ U →
      ∃ u : (X.left.presheaf.stalk x.underlying)ˣ,
        algebraMap (X.left.presheaf.stalk x.underlying) X.left.functionField (u : _) = φ t) →
    ∃ v : Γ(Y.left, U)ˣ, Y.left.germToFunctionField U (v : Γ(Y.left, U)) = t := by
  dsimp only
  let hg := s2e_c1_dominant_generic_point f.left
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    f.left.stalkMap (genericPoint X.left)).hom
  letI : Nonempty (f.left ⁻¹ᵁ U) := ⟨⟨genericPoint X.left, by
    change f.left (genericPoint X.left) ∈ U
    rw [hg]
    exact ((genericPoint_spec Y.left).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)⟩⟩
  intro hlocal
  have hφt : φ t ≠ 0 := fun he => ht (φ.injective (he.trans (map_zero φ).symm))
  obtain ⟨u, hu⟩ := s2e_c1_affine_rational_unit_of_complex_stalks X
    (f.left ⁻¹ᵁ U) (hU.preimage f.left) (φ t) hφt hlocal
  exact s2e_c1_finite_scheme_unit_descent X Y f U hU t u hu.symm

end HodgeLean.Foundations.Program
