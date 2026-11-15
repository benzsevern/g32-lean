import HodgeLean.Foundations.Singular.SingularShortTensor
import HodgeLean.Foundations.Singular.TensorDegreeSum

/-! Direct-sum conversion of actual singular tensor classes to their short-complex models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct DirectSum
namespace HodgeLean.Foundations.Singular

/-- The actual degreewise direct-sum conversion from singular factor cohomologies to short-complex cohomologies.
Source: Hatcher, Algebraic Topology, §3.2, the graded cohomology tensor product. -/
def singularShortDegreeSumEquiv (X Y : TopCat.{0}) (n : ℕ) :
    (⨁ a : tensorDegreeIndex n,
      AlgebraicTopology.Singular.Cohomology ℚ X a.1.1 ⊗[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y a.1.2) ≃ₗ[ℚ]
    (⨁ a : tensorDegreeIndex n,
      ((rationalChains X).sc a.1.1).linearDual.homology ⊗[ℚ]
        ((rationalChains Y).sc a.1.2).linearDual.homology) :=
  DirectSum.congrLinearEquiv (fun a => singularShortTensorEquiv X Y a.1.1 a.1.2)

set_option backward.isDefEq.respectTransparency false in
/-- The actual direct-sum conversion sends a represented singular tensor summand to its specified short-complex summand.
Source: Hatcher, Algebraic Topology, §3.2, the graded cohomology tensor product. -/
theorem singularShortDegreeSumEquiv_classes (X Y : TopCat.{0}) (p q : ℕ)
    (φ : Cocycle ℚ (TopCat.toSSet.obj X) p) (ψ : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    singularShortDegreeSumEquiv X Y (p + q)
      (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
        (fun a => AlgebraicTopology.Singular.Cohomology ℚ X a.1.1 ⊗[ℚ]
          AlgebraicTopology.Singular.Cohomology ℚ Y a.1.2)
        ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
        (cohomologyClass X p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ)) =
      DirectSum.lof ℚ (tensorDegreeIndex (p + q))
        (fun a => ((rationalChains X).sc a.1.1).linearDual.homology ⊗[ℚ]
          ((rationalChains Y).sc a.1.2).linearDual.homology)
        ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
        (((rationalChains X).sc p).linearDual.moduleCatHomologyClass (singularDualCycle X p φ) ⊗ₜ[ℚ]
          ((rationalChains Y).sc q).linearDual.moduleCatHomologyClass (singularDualCycle Y q ψ)) := by
  let a : tensorDegreeIndex (p + q) := ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
  have h := DirectSum.lmap_lof
    (fun b : tensorDegreeIndex (p + q) => (singularShortTensorEquiv X Y b.1.1 b.1.2).toLinearMap) a
    (cohomologyClass X p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ)
  exact h.trans (congrArg (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
    (fun b => ((rationalChains X).sc b.1.1).linearDual.homology ⊗[ℚ]
      ((rationalChains Y).sc b.1.2).linearDual.homology) a) (singularShortTensorEquiv_classes X Y p q φ ψ))

#print axioms singularShortDegreeSumEquiv
#print axioms singularShortDegreeSumEquiv_classes
end HodgeLean.Foundations.Singular
