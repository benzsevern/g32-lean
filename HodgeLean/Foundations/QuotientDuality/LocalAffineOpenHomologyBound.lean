import HodgeLean.Foundations.QuotientDuality.LocalPolynomialOpenHomologyBound
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis

/-! Uniform bounds on homology of open subsets of affine complex schemes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

theorem affine_complex_open_homology_bound (X : Over (Spec ↧ℂ))
    [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    ∃ N : ℕ, ∀ (U : TopCat.{0}) (j : U ⟶ TopCat.of (ComplexPoint X)),
      IsOpenEmbedding j → ∀ i : ℕ, N < i → Subsingleton (Homology ℚ U i) := by
  obtain ⟨n, m, p, a, h, ha⟩ := affine_coordinates X
  obtain ⟨aR, bR, ⟨hR⟩⟩ := zeroSet_real_model p
  let E : ComplexPoint X ≃ₜ realPolynomialCarrier aR bR := h.trans hR
  refine ⟨n + n, ?_⟩
  intro U j hj i hi
  exact polynomial_carrier_open_homology_bound aR bR U
    (j ≫ TopCat.ofHom ⟨E, E.continuous⟩) (E.isOpenEmbedding.comp hj) i hi

#print axioms affine_complex_open_homology_bound
end HodgeLean.Foundations.QuotientDuality
