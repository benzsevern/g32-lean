import HodgeLean.Foundations.Singular.RationalTensorDual
import HodgeLean.Foundations.Singular.RationalSplitDualClass
import HodgeLean.Foundations.Singular.TensorDegreeMaps

/-! Evaluation of tensor dual cohomology on actual pure homology representatives. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor dual-cohomology comparison evaluates a cocycle on pure chosen homology representatives.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient tensor evaluation pairing. -/
theorem rationalTensorDualHomologyEquiv_class
    (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q n : ℕ) (hpq : p + q = n)
    (φ : LinearMap.ker ((HomologicalComplex.tensorObj K L).sc n).f.hom.dualMap)
    (u : rationalHomologyQuotient K p) (v : rationalHomologyQuotient L q) :
    rationalTensorDualHomologyEquiv K L n
      (((HomologicalComplex.tensorObj K L).sc n).linearDual.moduleCatHomologyClass φ)
      ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
        p q n hpq).hom (u ⊗ₜ[ℚ] v)) =
    φ.1 ((HomologicalComplex.ιTensorObj K L p q n hpq).hom
      (rationalHomologyInclusion K p u ⊗ₜ[ℚ] rationalHomologyInclusion L q v)) := by
  have hn := rationalSplitDualEquiv_class (rationalTensorHomologyHomotopyEquiv K L)
    (rationalTensorHomology_d_eq_zero K L) n φ
    ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
      p q n hpq).hom (u ⊗ₜ[ℚ] v))
  have hm := congrArg (fun k => ModuleCat.Hom.hom k (u ⊗ₜ[ℚ] v))
    (tensorDegreeInclusion_naturality (rationalHomologyChainInclusion K)
      (rationalHomologyChainInclusion L) p q n hpq)
  change ((HomologicalComplex.tensorHom (rationalHomologyChainInclusion K)
      (rationalHomologyChainInclusion L)).f n).hom
      ((HomologicalComplex.ιTensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)
        p q n hpq).hom (u ⊗ₜ[ℚ] v)) =
    (HomologicalComplex.ιTensorObj K L p q n hpq).hom
      (((rationalHomologyChainInclusion K).f p ⊗ₘ (rationalHomologyChainInclusion L).f q).hom
        (u ⊗ₜ[ℚ] v)) at hm
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul] at hm
  exact hn.trans (congrArg φ.1 hm)

#print axioms rationalTensorDualHomologyEquiv_class
end HodgeLean.Foundations.Singular
