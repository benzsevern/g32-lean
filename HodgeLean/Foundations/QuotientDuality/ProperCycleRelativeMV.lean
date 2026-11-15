import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.MayerVietoris
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! # Relative Mayer–Vietoris quotient models for the tangential homology shift

Source: Hatcher, Algebraic Topology, section 2.2;
Other/AlgebraicTopology/Singular/RelativeMayerVietoris.lean at 2ead713,
quotient diagram and endpoint constructions adapted to the existing chain port.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeMV

section Abelian

variable {C : Type*} [Category C] [Abelian C]
  {S T : ShortComplex C} (f : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)


def shortExactMapSnakeInput : ShortComplex.SnakeInput C where
  L₀ := kernel f
  L₁ := S
  L₂ := T
  L₃ := cokernel f
  v₀₁ := kernel.ι f
  v₁₂ := f
  v₂₃ := cokernel.π f
  w₀₂ := kernel.condition f
  w₁₃ := cokernel.condition f
  h₀ := kernelIsKernel f
  h₃ := cokernelIsCokernel f
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hT.exact
  mono_L₂_f := hT.mono_f

set_option backward.isDefEq.respectTransparency false in
include hS hT in

theorem cokernel_shortExact_of_shortExact_of_mono_third [Mono f.τ₃] :
    (cokernel f).ShortExact := by
  let D := shortExactMapSnakeInput f hS hT
  have hzero : IsZero D.L₀.X₃ := by
    apply IsZero.of_mono_eq_zero D.v₀₁.τ₃
    apply (cancel_mono f.τ₃).mp
    rw [zero_comp]
    exact D.w₀₂_τ₃
  refine { exact := D.L₃_exact, mono_f := ?_, epi_g := ?_ }
  · exact (D.L₂'.exact_iff_mono (hzero.eq_of_src _ _)).mp D.L₂'_exact
  · let : Epi D.L₂.g := hT.epi_g
    exact D.epi_L₃_g

variable {P₁ P₂ Q₁ Q₂ : C} (a : P₁ ⟶ Q₁) (b : P₂ ⟶ Q₂)


def cokernelBiprodMapCofork : CokernelCofork (biprod.map a b) :=
  CokernelCofork.ofπ (biprod.map (cokernel.π a) (cokernel.π b)) (by
    ext <;> simp)

set_option backward.isDefEq.respectTransparency false in

def cokernelBiprodMapCofork_isColimit : IsColimit (cokernelBiprodMapCofork a b) :=
  Cofork.IsColimit.mk _
    (fun s ↦ biprod.desc
      (cokernel.desc a (biprod.inl ≫ s.π) (by
        have h := biprod.inl ≫= s.condition
        simpa only [Category.assoc, biprod.inl_map_assoc, zero_comp, comp_zero] using h))
      (cokernel.desc b (biprod.inr ≫ s.π) (by
        have h := biprod.inr ≫= s.condition
        simpa only [Category.assoc, biprod.inr_map_assoc, zero_comp, comp_zero] using h)))
    (fun _ ↦ by apply biprod.hom_ext' <;> simp [cokernelBiprodMapCofork])
    (fun _ m hm ↦ by
      apply biprod.hom_ext'
      · apply (cancel_epi (cokernel.π a)).mp
        simpa [cokernelBiprodMapCofork] using biprod.inl ≫= hm
      · apply (cancel_epi (cokernel.π b)).mp
        simpa [cokernelBiprodMapCofork] using biprod.inr ≫= hm)


def cokernelBiprodMapIso : cokernel (biprod.map a b) ≅ cokernel a ⊞ cokernel b :=
  (cokernelIsCokernel (biprod.map a b)).coconePointUniqueUpToIso
    (cokernelBiprodMapCofork_isColimit a b)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem cokernelBiprodMapIso_projection :
    cokernel.π (biprod.map a b) ≫ (cokernelBiprodMapIso a b).hom =
      biprod.map (cokernel.π a) (cokernel.π b) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (biprod.map a b))
    (cokernelBiprodMapCofork_isColimit a b) WalkingParallelPair.one

end Abelian

section Subsets

variable (X : TopCat) (U V : Set X)


def ambientDiagonalShortComplex : ShortComplex (ChainCategory ℚ) :=
  (IsPushout.of_id_fst
    (f := 𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)))).shortComplex

set_option backward.isDefEq.respectTransparency false in

theorem ambientDiagonalShortComplex_shortExact :
    (ambientDiagonalShortComplex X).ShortExact where
  exact := (IsPushout.of_id_fst
    (f := 𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)))).exact_shortComplex
  epi_g := (IsPushout.of_id_fst
    (f := 𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)))).epi_shortComplex_g
  mono_f := by
    constructor
    intro Z f g h
    have hh := congrArg (fun k ↦ k ≫ biprod.fst) h
    simp only [ambientDiagonalShortComplex, CommSq.shortComplex_f, Category.assoc,
      biprod.lift_fst] at hh
    change f ≫ 𝟙 _ = g ≫ 𝟙 _ at hh
    simpa only [Category.comp_id] using hh


abbrev subsetAmbientChainMap (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion X A))
    (ModuleCat.of ℚ ℚ)

set_option backward.isDefEq.respectTransparency false in

theorem subsetIntersectionChainMap_left_comp :
    SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft X U V))
        (ModuleCat.of ℚ ℚ) ≫ subsetAmbientChainMap X U =
      subsetAmbientChainMap X (U ∩ V) := by
  let F := TopCat.toSSet ⋙
    (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map _ ≫ F.map _ = F.map _
  rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem subsetIntersectionChainMap_right_comp :
    SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight X U V))
        (ModuleCat.of ℚ ℚ) ≫ subsetAmbientChainMap X V =
      subsetAmbientChainMap X (U ∩ V) := by
  let F := TopCat.toSSet ⋙
    (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map _ ≫ F.map _ = F.map _
  rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in

def subsetMayerVietorisToAmbient :
    singularMayerVietorisShortComplex X U V ⟶ ambientDiagonalShortComplex X :=
  ShortComplex.homMk
    (subsetAmbientChainMap X (U ∩ V))
    (biprod.map (subsetAmbientChainMap X U) (subsetAmbientChainMap X V))
    (twoSubsetSmallChainInclusion X U V)
    (by
      apply biprod.hom_ext
      · simp only [Category.assoc, ambientDiagonalShortComplex, CommSq.shortComplex_f,
          biprod.lift_fst, singularMayerVietorisShortComplex,
          biprod.map_fst, biprod.lift_fst_assoc]
        exact (subsetIntersectionChainMap_left_comp X U V).symm
      · simp only [Category.assoc, ambientDiagonalShortComplex, CommSq.shortComplex_f,
          biprod.lift_snd, Preadditive.comp_neg,
          singularMayerVietorisShortComplex, biprod.map_snd, biprod.lift_snd_assoc,
          Preadditive.neg_comp]
        exact congrArg Neg.neg (subsetIntersectionChainMap_right_comp X U V).symm)
    (by
      change biprod.map (subsetAmbientChainMap X U) (subsetAmbientChainMap X V) ≫
          biprod.desc (𝟙 _) (𝟙 _) =
        singularMayerVietorisSumChainMap X U V
      rw [singularMayerVietorisSumChainMap_eq]
      apply biprod.hom_ext' <;> simp)

set_option backward.isDefEq.respectTransparency false in

theorem subsetMayerVietorisToAmbient_mono_third :
    Mono (subsetMayerVietorisToAmbient X U V).τ₃ := by
  change Mono (SSet.chainComplexMap
    (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι
      (ModuleCat.of ℚ ℚ))
  dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono


def relativeMayerVietorisSmallShortComplex : ShortComplex (ChainCategory ℚ) :=
  cokernel (subsetMayerVietorisToAmbient X U V)

set_option backward.isDefEq.respectTransparency false in

theorem relativeMayerVietorisSmallShortComplex_shortExact :
    (relativeMayerVietorisSmallShortComplex X U V).ShortExact := by
  let : Mono (subsetMayerVietorisToAmbient X U V).τ₃ :=
    subsetMayerVietorisToAmbient_mono_third X U V
  exact cokernel_shortExact_of_shortExact_of_mono_third
    (subsetMayerVietorisToAmbient X U V)
    (singularMayerVietorisShortComplex_shortExact X U V)
    (ambientDiagonalShortComplex_shortExact X)

set_option backward.isDefEq.respectTransparency false in

def relativeMayerVietorisSmallLeftIso :
    (relativeMayerVietorisSmallShortComplex X U V).X₁ ≅
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (U ∩ V)) :=
  PreservesCokernel.iso ShortComplex.π₁ (subsetMayerVietorisToAmbient X U V)

set_option backward.isDefEq.respectTransparency false in

def relativeMayerVietorisSmallMiddleIso :
    (relativeMayerVietorisSmallShortComplex X U V).X₂ ≅
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset U) ⊞
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset V) :=
  PreservesCokernel.iso ShortComplex.π₂ (subsetMayerVietorisToAmbient X U V) ≪≫
    cokernelBiprodMapIso (subsetAmbientChainMap X U) (subsetAmbientChainMap X V)

set_option backward.isDefEq.respectTransparency false in

def relativeMayerVietorisSmallRightIso :
    (relativeMayerVietorisSmallShortComplex X U V).X₃ ≅
      triadRelativeChainComplex ℚ X U V :=
  letI : Epi (singularMayerVietorisShortComplex X U V).g :=
    (singularMayerVietorisShortComplex_shortExact X U V).epi_g
  PreservesCokernel.iso ShortComplex.π₃ (subsetMayerVietorisToAmbient X U V) ≪≫
    (cokernelEpiComp (singularMayerVietorisShortComplex X U V).g
      (twoSubsetSmallChainInclusion X U V)).symm ≪≫
    cokernelIsoOfEq (singularMayerVietorisSumChainMap_eq X U V)


def relativeMayerVietorisRightComparison :
    (relativeMayerVietorisSmallShortComplex X U V).X₃ ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (U ∪ V)) :=
  (relativeMayerVietorisSmallRightIso X U V).hom ≫ triadToUnionRelativeChainMap ℚ X U V

set_option backward.isDefEq.respectTransparency false in

theorem relativeMayerVietorisRightComparison_quasiIso (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (relativeMayerVietorisRightComparison X U V) := by
  let : QuasiIso (triadToUnionRelativeChainMap ℚ X U V) :=
    triadToUnionRelativeChainMap_quasiIso_of_isOpen X U V hU hV
  change QuasiIso ((relativeMayerVietorisSmallRightIso X U V).hom ≫ _)
  infer_instance


def relativeMayerVietorisLeftHomologyIso (n : ℕ) :
    (relativeMayerVietorisSmallShortComplex X U V).X₁.homology n ≅
      RelativeHomology ℚ (TopPair.ofSubset (U ∩ V)) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (relativeMayerVietorisSmallLeftIso X U V)


def relativeMayerVietorisMiddleHomologyIso (n : ℕ) :
    (relativeMayerVietorisSmallShortComplex X U V).X₂.homology n ≅
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset U) ⊞
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset V)).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (relativeMayerVietorisSmallMiddleIso X U V)

set_option backward.isDefEq.respectTransparency false in

def relativeMayerVietorisRightHomologyIso (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (relativeMayerVietorisSmallShortComplex X U V).X₃.homology n ≅
      RelativeHomology ℚ (TopPair.ofSubset (U ∪ V)) n :=
  letI : QuasiIso (relativeMayerVietorisRightComparison X U V) :=
    relativeMayerVietorisRightComparison_quasiIso X U V hU hV
  asIso (HomologicalComplex.homologyMap (relativeMayerVietorisRightComparison X U V) n)


def relativeMayerVietorisBoundary (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (U ∪ V)) (n + 1) ⟶
      RelativeHomology ℚ (TopPair.ofSubset (U ∩ V)) n :=
  (relativeMayerVietorisRightHomologyIso X U V hU hV (n + 1)).inv ≫
    (relativeMayerVietorisSmallShortComplex_shortExact X U V).δ (n + 1) n
      (ComplexShape.down_mk (n + 1) n (by omega)) ≫
        (relativeMayerVietorisLeftHomologyIso X U V n).hom


private instance homology_preservesBinaryBiproducts (n : ℕ) :
    PreservesBinaryBiproducts
      (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

set_option backward.isDefEq.respectTransparency false in
/-- The relative connecting map is an isomorphism when both intermediate pair groups vanish.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer–Vietoris.
HC no distance; AV milestone no distance. -/
def relativeMayerVietorisBoundaryIso (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hzero : ∀ j ∈ ({n, n + 1} : Finset ℕ),
      IsZero (RelativeHomology ℚ (TopPair.ofSubset U) j) ∧
      IsZero (RelativeHomology ℚ (TopPair.ofSubset V) j)) :
    RelativeHomology ℚ (TopPair.ofSubset (U ∪ V)) (n + 1) ≅
      RelativeHomology ℚ (TopPair.ofSubset (U ∩ V)) n := by
  have hmid (j : ℕ) (hj : j ∈ ({n, n + 1} : Finset ℕ)) :
      IsZero ((relativeMayerVietorisSmallShortComplex X U V).X₂.homology j) := by
    let E := (relativeMayerVietorisMiddleHomologyIso X U V j) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
        (ComplexShape.down ℕ) j).mapBiprod
          ((relativeChainFunctor ℚ).obj (TopPair.ofSubset U))
          ((relativeChainFunctor ℚ).obj (TopPair.ofSubset V))
    exact ((biprod_isZero_iff _ _).mpr (hzero j hj)).of_iso E
  exact (relativeMayerVietorisRightHomologyIso X U V hU hV (n + 1)).symm ≪≫
    (relativeMayerVietorisSmallShortComplex_shortExact X U V).δIso (n + 1) n
      (ComplexShape.down_mk (n + 1) n (by omega))
      (hmid (n + 1) (by simp)) (hmid n (by simp)) ≪≫
    relativeMayerVietorisLeftHomologyIso X U V n


end Subsets
end HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeMV
