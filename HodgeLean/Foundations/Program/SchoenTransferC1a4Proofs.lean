import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! Implication from the explicit inputs to a supporting construction piece.
Finite normalized integral chains prepare the cellular comparison.
Comparison with a triangulated space and finite singular homology remain later pieces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped Simplicial
namespace HodgeLean.Foundations.Program
/-- Finite normalized integral chains prepare the cellular comparison.
Source: Hatcher, Algebraic Topology, §2.1–2.2, simplicial chains; SSet.isColimitCofanNormalizedChainComplex and SSet.homotopyEquivNormalizedChainComplex. -/
theorem s4_c1a4_finite_normalized_chains_aux (K : SSet.{0})
    [K.Finite] :
    let R := ModuleCat.of ℤ ℤ
    ∃ b : ∀ n : ℕ, Module.Basis (K.nonDegenerate n) ℤ
        ((K.normalizedChainComplex R).X n),
      (∀ n σ, b n σ = (K.ιNormalizedChainComplex (R := R) σ.val).hom 1) ∧
      (∀ n, Module.Finite ℤ ((K.normalizedChainComplex R).X n)) ∧
      (∃ d : ℕ, ∀ n : ℕ, d ≤ n → CategoryTheory.Limits.IsZero
        ((K.normalizedChainComplex R).X n)) ∧
      ∃ e : HomotopyEquiv (K.chainComplex R) (K.normalizedChainComplex R),
        e.hom = K.toNormalizedChainComplex R ∧
        e.inv = K.fromNormalizedChainComplex R := by
  classical
  let R := ModuleCat.of ℤ ℤ
  let e (n : ℕ) := (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (K.nonDegenerate n)).coconePointUniqueUpToIso
    (K.isColimitCofanNormalizedChainComplex R n)
  let b (n : ℕ) := (Finsupp.basisSingleOne (R := ℤ) (ι := K.nonDegenerate n)).map
    (e n).toLinearEquiv
  refine ⟨b, ?_, ?_, ?_, K.homotopyEquivNormalizedChainComplex R, rfl, rfl⟩
  · intro n σ
    change (e n).hom.hom (Finsupp.single σ 1) = _
    have h := CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (K.nonDegenerate n))
      (K.isColimitCofanNormalizedChainComplex R n) (Discrete.mk σ)
    exact congrArg (fun f : R ⟶ (K.normalizedChainComplex R).X n => f.hom 1) h
  · intro n
    exact Module.Finite.of_basis (b n)
  · obtain ⟨d, hd⟩ := K.hasDimensionLT_of_finite
    haveI := hd
    exact ⟨d, fun n hn => K.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d hn⟩

end HodgeLean.Foundations.Program
