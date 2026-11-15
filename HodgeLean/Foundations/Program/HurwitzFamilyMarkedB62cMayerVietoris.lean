import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.MayerVietoris
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientExcision

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular

instance b6m_simplicialChains_preservesColimitsOfShape
    (R : Type) [CommRing R] {J : Type} [Category J] :
    PreservesColimitsOfShape J ((SSet.chainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)) := by
  let : PreservesColimitsOfShape J (sigmaConst.obj (ModuleCat.of R R)) :=
    (sigmaConstAdj (ModuleCat.of R R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    (((evaluation _ _).obj (Opposite.op (SimplexCategory.mk n))) ⋙
      sigmaConst.obj (ModuleCat.of R R))
  infer_instance

theorem b6m_subsetSmallChainSquare_isPushout
    (R : Type) [CommRing R] (X : TopCat) (U V : Set X) :
    IsPushout
      (SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft X U V))
        (ModuleCat.of R R))
      (SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight X U V))
        (ModuleCat.of R R))
      (SSet.chainComplexMap (subsetLeftToSmallSingularSet X U V) (ModuleCat.of R R))
      (SSet.chainComplexMap (subsetRightToSmallSingularSet X U V) (ModuleCat.of R R)) :=
  (subsetSmallSingularSquare_isPushout X U V).map
    ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))

def b6m_singularMayerVietorisShortComplex
    (R : Type) [CommRing R] (X : TopCat) (U V : Set X) : ShortComplex (ChainCategory R) :=
  (b6m_subsetSmallChainSquare_isPushout R X U V).shortComplex

set_option backward.isDefEq.respectTransparency false in
theorem b6m_singularMayerVietorisShortComplex_shortExact
    (R : Type) [CommRing R] (X : TopCat) (U V : Set X) :
    (b6m_singularMayerVietorisShortComplex R X U V).ShortExact where
  exact := (b6m_subsetSmallChainSquare_isPushout R X U V).exact_shortComplex
  epi_g := (b6m_subsetSmallChainSquare_isPushout R X U V).epi_shortComplex_g
  mono_f := by
    let f := TopCat.toSSet.map (subsetIntersectionToLeft X U V)
    have : Mono f := by
      rw [NatTrans.mono_iff_mono_app]
      intro n
      rw [CategoryTheory.mono_iff_injective]
      intro a b hab
      apply ((TopCat.of ↥(U ∩ V)).toSSetObjEquiv n).injective
      ext t
      exact congrArg (fun s ↦ ((TopCat.of U).toSSetObjEquiv n s t).1) hab
    have : Mono (SSet.chainComplexMap f (ModuleCat.of R R)) := by
      dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
      apply +allowSynthFailures Functor.map_mono
    exact mono_of_mono_fac (biprod.lift_fst _ _)

def b6m_twoSubsetSmallChainInclusion
    (R : Type) [CommRing R] (X : TopCat) (U V : Set X) :
    (b6m_singularMayerVietorisShortComplex R X U V).X₃ ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R) :=
  SSet.chainComplexMap
    (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι (ModuleCat.of R R)

theorem b6m_twoSubsetSmallChainInclusion_quasiIso
    (R : Type) [CommRing R] (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    QuasiIso (b6m_twoSubsetSmallChainInclusion R X U V) := by
  have hopen : ∀ b : Bool, IsOpen (if b then U else V) := by
    intro b
    cases b <;> assumption
  have hcover : ⋃ b : Bool, (if b then U else V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases (hUV.symm ▸ Set.mem_univ x : x ∈ U ∪ V) with hx | hx
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  change QuasiIso (SSet.chainComplexMap
    (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι (ModuleCat.of R R))
  rw [subsetSingularSubcomplex_sup]
  change QuasiIso (coverSmallCoefficientSingularChainInclusion R X
    (fun b : Bool => if b then U else V))
  rw [← coverSmallCoefficientChainHomotopyEquiv_of_openCover_hom R X
    (fun b : Bool => if b then U else V) hopen hcover]
  exact HomotopyEquiv.quasiIso_hom _

end HodgeLean.Foundations.Program
