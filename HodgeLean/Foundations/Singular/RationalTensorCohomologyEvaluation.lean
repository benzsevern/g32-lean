import HodgeLean.Foundations.Singular.RationalTensorCohomology

/-! Bidegree evaluation of the actual algebraic rational tensor-cohomology equivalence. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor-cohomology equivalence evaluates in each bidegree through its factorwise pairing.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient cohomology tensor pairing. -/
theorem rationalTensorCohomologyEquiv_evaluate (K L : ChainComplex (ModuleCat ℚ) ℕ)
    (hK : ∀ p : ℕ, Module.Finite ℚ (K.sc p).linearDual.homology) (n : ℕ)
    (x : ⨁ a : tensorDegreeIndex n,
      (K.sc a.1.1).linearDual.homology ⊗[ℚ] (L.sc a.1.2).linearDual.homology)
    (a : tensorDegreeIndex n)
    (z : tensorDegreeFactor (rationalHomologyComplex K) (rationalHomologyComplex L) n a) :
    rationalTensorDualHomologyEquiv K L n (rationalTensorCohomologyEquiv K L hK n x)
      ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
        a.1.1 a.1.2 n (Finset.mem_antidiagonal.mp a.2)).hom z) =
    (DirectSum.congrLinearEquiv (fun b : tensorDegreeIndex n =>
      rationalTensorCohomologyFactorEquiv (h := hK b.1.1) K L n b) x) a z := by
  letI (p : ℕ) : Module.Finite ℚ (K.sc p).linearDual.homology := hK p
  let F := DirectSum.congrLinearEquiv (fun b : tensorDegreeIndex n =>
    rationalTensorCohomologyFactorEquiv K L n b)
  let V := tensorDegreeFactor (rationalHomologyComplex K) (rationalHomologyComplex L) n
  have he : rationalTensorDualHomologyEquiv K L n (rationalTensorCohomologyEquiv K L hK n x) =
      (tensorDegreeSumEquiv (rationalHomologyComplex K) (rationalHomologyComplex L) n).dualMap
        ((rationalFiniteDirectSumDualEquiv V).symm (F x)) := by
    simp only [rationalTensorCohomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [he]
  change (rationalFiniteDirectSumDualEquiv V).symm (F x)
      (tensorDegreeSumEquiv (rationalHomologyComplex K) (rationalHomologyComplex L) n
        ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
          a.1.1 a.1.2 n (Finset.mem_antidiagonal.mp a.2)).hom z)) = (F x) a z
  have hi := LinearMap.congr_fun (tensorDegreeToSum_inclusion
    (rationalHomologyComplex K) (rationalHomologyComplex L) a.1.1 a.1.2 n
      (Finset.mem_antidiagonal.mp a.2)) z
  change tensorDegreeSumEquiv (rationalHomologyComplex K) (rationalHomologyComplex L) n
    ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
      a.1.1 a.1.2 n (Finset.mem_antidiagonal.mp a.2)).hom z) = _ at hi
  rw [hi]
  exact rationalFiniteDirectSumDualEquiv_symm_lof V (F x) a z

#print axioms rationalTensorCohomologyEquiv_evaluate
end HodgeLean.Foundations.Singular
