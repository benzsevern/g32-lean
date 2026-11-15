import HodgeLean.Foundations.Singular.RationalProductCohomology
import HodgeLean.Foundations.Singular.RationalTensorCohomologyClass
import HodgeLean.Foundations.Singular.ProductTensorCupClass

/-! The actual rational product-cohomology equivalence is the specified projection-cup map. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct DirectSum
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The actual rational product-cohomology equivalence evaluates a pure summand by the specified projection cup.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient cohomology Künneth theorem. -/
theorem rationalProductCohomologyEquiv_tmul (X Y : TopCat.{0})
    (hX : ∀ r : ℕ, Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ X r)) (p q : ℕ)
    (α : AlgebraicTopology.Singular.Cohomology ℚ X p) (β : AlgebraicTopology.Singular.Cohomology ℚ Y q) :
    rationalProductCohomologyEquiv X Y hX (p + q)
      (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
        (fun a => AlgebraicTopology.Singular.Cohomology ℚ X a.1.1 ⊗[ℚ]
          AlgebraicTopology.Singular.Cohomology ℚ Y a.1.2)
        ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩ (α ⊗ₜ[ℚ] β)) =
      cup (TopCat.of (X × Y)) rfl
        (AlgebraicTopology.Singular.cohomologyMap ℚ p (productFirst X Y) α)
        (AlgebraicTopology.Singular.cohomologyMap ℚ q (productSecond X Y) β) := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective (R := ℚ) X p α
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective (R := ℚ) Y q β
  letI (r : ℕ) : Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ X r) := hX r
  have hK (r : ℕ) : Module.Finite ℚ ((rationalChains X).sc r).linearDual.homology :=
    Module.Finite.of_surjective
      (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X r).symm.toLinearMap
      (AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ X r).symm.surjective
  change AlgebraicTopology.Singular.cochainCohomologyEquiv ℚ (TopCat.of (X × Y)) (p + q)
    ((rationalProductTensorCohomologyEquiv X Y (p + q)).symm
      (rationalTensorCohomologyEquiv (rationalChains X) (rationalChains Y) hK (p + q)
        (singularShortDegreeSumEquiv X Y (p + q)
          (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
            (fun a => AlgebraicTopology.Singular.Cohomology ℚ X a.1.1 ⊗[ℚ]
              AlgebraicTopology.Singular.Cohomology ℚ Y a.1.2)
            ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
            (cohomologyClass X p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ))))) = _
  have hx := singularShortDegreeSumEquiv_classes X Y p q φ ψ
  rw [hx]
  have ht := rationalTensorCohomologyEquiv_class (rationalChains X) (rationalChains Y) hK p q
    (singularDualCycle X p φ) (singularDualCycle Y q ψ)
  rw [ht]
  exact tensorScalarCycle_AW_class X Y p q φ ψ

#print axioms rationalProductCohomologyEquiv_tmul
end HodgeLean.Foundations.Singular
