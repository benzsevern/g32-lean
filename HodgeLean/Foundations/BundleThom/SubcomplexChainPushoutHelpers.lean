import HodgeLean.Foundations.BundleThom.Defs
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Abelian.CommSq

/-! # Rational chains on actual intersections and unions of singular subcomplexes

The intersection–union square is retained before passing to relative chains or cohomology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- In each degree, rational chains carry an actual subcomplex intersection–union square to a pushout.
Source: Hatcher, Algebraic Topology, §2.2, small-chain Mayer–Vietoris construction. -/
theorem i1_subcomplexChainDegree_isPushout (X : SSet) (U V : X.Subcomplex) (n : ℕ) :
    IsPushout
      ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U))
        (ModuleCat.of ℚ ℚ)).f n)
      ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V))
        (ModuleCat.of ℚ ℚ)).f n)
      ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : U ≤ U ⊔ V))
        (ModuleCat.of ℚ ℚ)).f n)
      ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V))
        (ModuleCat.of ℚ ℚ)).f n) := by
  let sq : SSet.Subcomplex.BicartSq (U ⊓ V) U V (U ⊔ V) := ⟨rfl, rfl⟩
  let F : SSet ⥤ ModuleCat ℚ :=
    (evaluation SimplexCategoryᵒᵖ (Type)).obj (Opposite.op ⦋n⦌) ⋙
      sigmaConst.obj (ModuleCat.of ℚ ℚ)
  exact F.map_isPushout sq.isPushout

/-- Rational chain complexes carry the actual intersection–union square to a pushout of complexes.
Source: Hatcher, Algebraic Topology, §2.2, small-chain Mayer–Vietoris construction. -/
theorem i1_subcomplexChains_isPushout (X : SSet) (U V : X.Subcomplex) :
    IsPushout
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : U ≤ U ⊔ V)) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V)) (ModuleCat.of ℚ ℚ)) := by
  have hw :
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : U ≤ U ⊔ V)) (ModuleCat.of ℚ ℚ) =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V)) (ModuleCat.of ℚ ℚ) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  refine { w := hw, isColimit' := ⟨?_⟩ }
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2
    (i1_subcomplexChainDegree_isPushout X U V n).isColimit

/-- An actual bicartesian subcomplex square gives a pushout of rational chain complexes.
Source: Hatcher, Algebraic Topology, §2.2, intersection–union chain construction. -/
theorem i1_subcomplexChains_bicart_isPushout (X : SSet) (A₁ A₂ A₃ A₄ : X.Subcomplex)
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    IsPushout
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₂) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₃) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₂₄) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₃₄) (ModuleCat.of ℚ ℚ)) := by
  obtain ⟨hsup, hinf⟩ := sq
  subst A₁
  subst A₄
  exact i1_subcomplexChains_isPushout X A₂ A₃

end HodgeLean.Foundations.BundleThom
