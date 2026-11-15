import HodgeLean.Foundations.Program.SchoenSelectedGeometryProofs
import HodgeLean.Foundations.Program.SchoenSelectedGeometryQuotientFormRank
import HodgeLean.Foundations.Program.SchoenSelectedGeometryModelHolomorphic
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySupplierPrimitive
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartRetraction

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Retain the stored part while transporting its Jacobian and action to the curve models. -/
theorem selectedPrimitiveNativePrefix
    {A : g32t_Sixfold} (X : g32p_Cover A)
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (hJ : X.J = J) (hAut : HEq X.aut aut)
    (hGrp : HEq X.grp (inferInstance : GrpObj J))
    (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    (C₀ Y Z : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (qC : C₀ ⟶ Y) (p₀ : Y ⟶ Z) (j : C₀ ⟶ J)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (eC : C ≃ₜ ComplexPoint C₀)
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    [ChartedSpace ℂ (rsq_Quot S.H C)] [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hj : Function.Bijective (homPullback j 1))
    (hPrefix : ∀ P : g32p_Part J aut S,
      ∃ primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
        (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
          (Polynomial.cyclotomic S.m ℚ)),
        (∀ v, homPullback qC 1 (primitive v) =
          homPullback j 1 (homPullback P.proj 1 v)) ∧
        (∀ (u : S.H) v,
          homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
            (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1)) ∧
        Module.finrank ℚ (LinearMap.ker
          (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
            (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m ∧
        2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
          (g32p_exponents S).length) :
    let P := X.part S hS
    ∃ (jC : C₀ ⟶ X.J), HEq jC j ∧
      (∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x)) ∧
      (∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z)) ∧
      (∀ u : S.H, e (QuotientGroup.mk u) = S.χ u) ∧
      Function.Bijective (homPullback jC 1) ∧
      ∃ primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
        (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
          (Polynomial.cyclotomic S.m ℚ)),
        (∀ v, homPullback qC 1 (primitive v) =
          homPullback jC 1 (homPullback P.proj 1 v)) ∧
        (∀ (u : S.H) v,
          homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
            (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1)) ∧
        Module.finrank ℚ (LinearMap.ker
          (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
            (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m ∧
        2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
          (g32p_exponents S).length := by
  subst J
  cases eq_of_heq hGrp
  have hAut' : X.aut = aut := eq_of_heq hAut
  subst aut
  exact ⟨j, HEq.rfl, hqC, hpC, hχ, hj, hPrefix (X.part S hS)⟩

#print axioms selectedPrimitiveNativePrefix
end HodgeLean.Foundations.Program
