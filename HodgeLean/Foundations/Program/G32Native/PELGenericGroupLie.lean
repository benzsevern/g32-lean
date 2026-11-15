import HodgeLean.Foundations.HodgeGroupAlgebraic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations

/-- Equality of complexified endomorphism spaces descends to rational spaces.
Source: Bourbaki, Algebra, Chapter II, §5 (faithful extension of scalars). -/
theorem complexSpan_injective {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {L M : Submodule ℚ (Module.End ℚ V)}
    (h : complexSpan L = complexSpan M) : L = M := by
  apply Submodule.baseChange_injective (A := ℂ)
  rw [complexSpan_eq_map, complexSpan_eq_map] at h
  exact Submodule.map_injective_of_injective (endBaseChangeEquiv V).injective h

/-- A fibre with the generic algebraic Hodge group has its rational Lie algebra.
The group is given by its complex points and its computed tangent space; neither
connectedness nor invariant-generation is an additional hypothesis here.
Source: Borel, Linear Algebraic Groups, second edition, §3.5;
Abdulali, Annals 155 (2002), Proposition 2.3.1 (generic Hodge group);
Abdulali, International Journal of Mathematics 10 (1999), §2.5 (PEL families).
The Hodge-group tangent comparison is `g2_lie_hodgeGroup`. -/
theorem hodgeLie_of_generic_group {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V]
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    {n : ℕ} (basis : Module.Basis (Fin n) ℚ V)
    (G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (L : Submodule ℚ (Module.End ℚ V))
    (hGroup : g2_hodgeGroup H hH basis = G)
    (hTangent : g1_lieOfSet G = (complexSpan L).map
      (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ basis)
        (Algebra.TensorProduct.basis ℂ basis)).toLinearMap) :
    (hodgeLieAlgebra H hH).toSubmodule = L := by
  apply complexSpan_injective
  apply Submodule.map_injective_of_injective
    (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ basis)
      (Algebra.TensorProduct.basis ℂ basis)).injective
  rw [← g2_lie_hodgeGroup H hH basis, hGroup, hTangent]

#print axioms complexSpan_injective
#print axioms hodgeLie_of_generic_group
end HodgeLean.Foundations.Program.GeneralTypeIII
