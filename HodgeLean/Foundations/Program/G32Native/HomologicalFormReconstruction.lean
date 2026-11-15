import HodgeLean.RealDefs.Compare.MarkmanTransport
import Mathlib.LinearAlgebra.Basis.Bilinear

noncomputable section
open Module HodgeLean.Foundations.Symplectic
open HodgeLean.RealDefs.Compare.Markman
namespace HodgeLean.Foundations.Program.G32Native

/-- Every rational alternating form on the dual is the Riemann form of a unique 2-vector.
Source: Bourbaki, Algebra, III §7, the perfect exterior pairing in finite dimension.
The sum has coefficient `1/2`, retaining the order of the two dual coordinates. -/
theorem homological_form_reconstruction
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E : LinearMap.BilinForm ℚ (Dual ℚ V)) (hE : E.IsAlt) :
    ∃! ω : ⋀[ℚ]^2 V, riemannForm ω = E := by
  classical
  let b := Module.finBasis ℚ V
  let ω : ⋀[ℚ]^2 V := (1 / 2 : ℚ) • ∑ i, ∑ j,
    E (b.dualBasis i) (b.dualBasis j) • exteriorPower.ιMulti ℚ 2 ![b i, b j]
  have hω : riemannForm ω = E := by
    apply LinearMap.ext_basis b.dualBasis b.dualBasis
    intro i j
    change (b.dualBasis j) (contract ω (b.dualBasis i)) = _
    simp only [ω, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
      contract_ιMulti, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub,
      Basis.dualBasis_apply, map_smul, smul_eq_mul]
    simp only [Basis.repr_self, Finsupp.single_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_mul,
      mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hs := hE.neg_eq (b.dualBasis i) (b.dualBasis j)
    linarith
  refine ⟨ω, hω, ?_⟩
  intro ω' hω'
  apply contract_injective
  apply LinearMap.ext
  intro φ
  apply (Module.evalEquiv ℚ V).injective
  ext ψ
  exact congrArg (fun B : LinearMap.BilinForm ℚ (Dual ℚ V) => B φ ψ)
    (hω'.trans hω.symm)

#print axioms homological_form_reconstruction
end HodgeLean.Foundations.Program.G32Native
