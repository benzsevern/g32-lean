import HodgeLean.Adapters.NormalConeB4aClassUniqueBoundary

/-! Detection of the lowest supported degree on arbitrary boundary complements. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- Lower support purity detects degree-2k relative classes by all their germs
on any specified open set. -/
theorem s4_q3_cycle_germs_injective
    {Z : Scheme.{0}} (q : Z ⟶ Spec ↧ℂ) [Smooth q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (k : ℕ)
    (hc : ∀ p ∈ γ.support, (k : ℕ∞) ≤ Order.coheight p)
    (O : Opens (a3b4_an q)) :
    let C : Closeds (a3b4_an q) :=
      ⟨a3b4_cycleSupport q γ, a3b4a_classSupport_isClosed q γ⟩
    Function.Injective (fun v => fun x : O =>
      supportRelativeCohomologyGerm (a3b4_an q) C (2 * k) O x.1 x.2 v) := by
  letI : LocallyOfFiniteType (Over.mk q).hom := inferInstanceAs (LocallyOfFiniteType q)
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI (V : Opens (ComplexPoint (Over.mk q))) : ParacompactSpace V :=
    a3b4a_class_openParacompact q V
  let C : Closeds (a3b4_an q) :=
    ⟨a3b4_cycleSupport q γ, a3b4a_classSupport_isClosed q γ⟩
  exact ccm5_relativeGerms_injective_of_lowerVanishing (a3b4_an q) C O (2 * k)
    (fun j hj => (O.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero
      (a3b4a_classSheaf_purity_vanishing q (a3b4a_classAlgebraicSupport q γ) k
        (a3b4a_classAlgebraicSupport_coheight q γ k hc) j hj))

end HodgeLean.Foundations.Program
