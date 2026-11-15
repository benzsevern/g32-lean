import HodgeLean.Foundations.RationalHomologyManifold.ScalarCycleSheafSections
import HodgeLean.Foundations.RationalHomologyManifold.ScalarCycleForgetClass

/-! Actual relative classes underlying scalar supported homology sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Evaluation of the original scalar homology presheaf section is the actual relative class of its projected cycle.
Source: Bredon, Sheaf Theory, second edition, VI.12; actual relative homology on each open support.
HC no distance; AV milestone no distance.
-/
theorem scalarCycleHomologyPresheafMap_relative_class (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) (U : Opens X)
    (v : LinearMap.ker ((((relativeChainFunctor ℚ).obj
      (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).sc (n + 1)).g.hom))
    (hv : v.val = (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f (n + 1) z) :
    (scalarCycleHomologyPresheafMap X n z hz).app (op U) (1 : ℚ) =
      (relativeHomologyPresheafSectionIso ℚ X U (n + 1)).hom
        ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).sc
          (n + 1)).moduleCatHomologyClass v) := by
  let K := singularChainPresheafComplex ℚ X
  let P := K.sc (n + 1)
  let R := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).sc (n + 1)
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let E := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)
  letI : E.Additive := inferInstanceAs
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)).Additive)
  letI : PreservesFiniteLimits E := inferInstanceAs
    (PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))
  letI : PreservesFiniteColimits E := inferInstanceAs
    (PreservesFiniteColimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)))
  let e := singularChainPresheafComplexEvaluationIso ℚ X U
  let ψ : R.map F ⟶ P.map E :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} (.down ℕ) (n + 1)).map e.inv
  let k := scalarChainPresheafMap X (n + 1) z
  have hk : k ≫ P.g = 0 := by
    change k ≫ K.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) = 0
    rw [ChainComplex.next_nat_succ]
    exact scalarChainPresheafMap_cycle X n z hz
  have hE := exactFunctor_cycle_class P E k hk
  have hF := scalarCycle_forget_class R v
  let a := ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ v.val)
  let l := (R.map F).liftCycles (F.map a)
    (by change F.map a ≫ F.map R.g = 0; rw [← F.map_comp, scalarModuleCycle_zero, F.map_zero]) ≫
      (R.map F).homologyπ
  have hl : l (1 : ℚ) = (R.mapHomologyIso F).inv (R.moduleCatHomologyClass v) := hF
  have ha : F.map a ≫ ψ.τ₂ = E.map k := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro r
    change r • v.val = (relativeChainProjection ℚ
      (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f (n + 1) (r • z)
    rw [map_smul, hv]
  have hc : l ≫ ShortComplex.homologyMap ψ =
      (P.map E).liftCycles (E.map k)
        (by change E.map k ≫ E.map P.g = 0; rw [← E.map_comp, hk, E.map_zero]) ≫
          (P.map E).homologyπ := by
    apply (cancel_mono (P.map E).homologyι).mp
    dsimp only [l]
    simp only [Category.assoc, ShortComplex.π_homologyMap_ι,
      ShortComplex.homology_π_ι]
    simp only [← Category.assoc, ShortComplex.liftCycles_i]
    rw [ha]
  have heq := congrArg (fun f => f (1 : ℚ))
    (congrArg (fun f => f ≫ (P.mapHomologyIso E).hom) hc)
  change ((P.mapHomologyIso E).hom)
      ((ShortComplex.homologyMap ψ) (l (1 : ℚ))) = _ at heq
  rw [hl] at heq
  have hEval := ConcreteCategory.congr_hom hE (1 : ℚ)
  simp only [ConcreteCategory.comp_apply] at hEval
  exact hEval.symm.trans heq.symm

#print axioms scalarCycleHomologyPresheafMap_relative_class
end HodgeLean.Foundations.RationalHomologyManifold
