import HodgeLean.Foundations.BundleThom.SubsetRelativeCoclassNaturalityHelpers
import HodgeLean.Foundations.BundleThom.RelativeSubcomplexMonomorphismHelpers

/-! # Actual relative domain coordinates in the binary small-chain sequence

The intersection and both cover members retain their actual topological
pairs. Their chain isomorphisms identify the existing small-chain sequence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable (X : TopCat.{0}) (Z U V : Set X)

def i1_relativeDomainIntersectionChainIso :
    (relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z (U ∩ V)) ≅
      (i1_relativeSubcomplexChainSequence (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U)
        (i1_singularSubsetRange X V)).X₁ :=
  (i1_subsetRelativeChainIso X Z (U ∩ V)).trans
    (eqToIso (congrArg
      (i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj
      (i1_singularSubsetRange_inter X U V)))

def i1_relativeDomainMiddleChainIso :
    biprod ((relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z U))
      ((relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z V)) ≅
      (i1_relativeSubcomplexChainSequence (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U)
        (i1_singularSubsetRange X V)).X₂ :=
  biprod.mapIso (i1_subsetRelativeChainIso X Z U) (i1_subsetRelativeChainIso X Z V)

def i1_relativeDomainBinarySequence : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) where
  X₁ := (relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z (U ∩ V))
  X₂ := biprod ((relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z U))
    ((relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z V))
  X₃ := (i1_relativeSubcomplexChainSequence (TopCat.toSSet.obj X)
    (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U) (i1_singularSubsetRange X V)).X₃
  f := (i1_relativeDomainIntersectionChainIso X Z U V).hom ≫
    (i1_relativeSubcomplexChainSequence (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U) (i1_singularSubsetRange X V)).f ≫
    (i1_relativeDomainMiddleChainIso X Z U V).inv
  g := (i1_relativeDomainMiddleChainIso X Z U V).hom ≫
    (i1_relativeSubcomplexChainSequence (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U) (i1_singularSubsetRange X V)).g
  zero := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ShortComplex.zero, comp_zero]

def i1_relativeDomainBinarySequenceIso :
    i1_relativeDomainBinarySequence X Z U V ≅
      i1_relativeSubcomplexChainSequence (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U) (i1_singularSubsetRange X V) :=
  ShortComplex.isoMk (i1_relativeDomainIntersectionChainIso X Z U V)
    (i1_relativeDomainMiddleChainIso X Z U V) (Iso.refl _)
    (by
      dsimp only [i1_relativeDomainBinarySequence]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      dsimp only [i1_relativeDomainBinarySequence, Iso.refl_hom]
      rw [Category.comp_id])

theorem i1_relativeDomainBinarySequence_shortExact :
    (i1_relativeDomainBinarySequence X Z U V).ShortExact :=
  ShortComplex.shortExact_of_iso (i1_relativeDomainBinarySequenceIso X Z U V).symm
    (i1_relativeSubcomplexChainSequence_shortExact (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U) (i1_singularSubsetRange X V))

theorem i1_relativeDomainIntersectionChainIso_naturality
    (W : Set X) (h : U ∩ V ⊆ W) :
    (i1_relativeDomainIntersectionChainIso X Z U V).hom ≫
        (i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).map
          (homOfLE (i1_singularSubsetRange_inter X U V ▸ i1_singularSubsetRange_mono X h)) =
      (relativeChainFunctor ℚ).map (i1_subsetRelativePairMap X Z h) ≫
        (i1_subsetRelativeChainIso X Z W).hom := by
  let F := i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
  have he : (eqToIso (congrArg F.obj (i1_singularSubsetRange_inter X U V))).hom ≫
      F.map (homOfLE (i1_singularSubsetRange_inter X U V ▸ i1_singularSubsetRange_mono X h)) =
      F.map (homOfLE (i1_singularSubsetRange_mono X h)) := by
    change eqToHom (congrArg F.obj (i1_singularSubsetRange_inter X U V)) ≫ _ = _
    rw [← eqToHom_map F (i1_singularSubsetRange_inter X U V), ← F.map_comp]
    congr 1
  dsimp only [i1_relativeDomainIntersectionChainIso, Iso.trans_hom]
  rw [Category.assoc, he]
  exact (i1_subsetRelativeChainIso_naturality X Z h).symm

theorem i1_relativeDomainBinarySequence_f :
    (i1_relativeDomainBinarySequence X Z U V).f =
      biprod.lift
        ((relativeChainFunctor ℚ).map (i1_subsetRelativePairMap X Z
          (Set.inter_subset_left : U ∩ V ⊆ U)))
        (-((relativeChainFunctor ℚ).map (i1_subsetRelativePairMap X Z
          (Set.inter_subset_right : U ∩ V ⊆ V)))) := by
  apply (cancel_mono (i1_relativeDomainMiddleChainIso X Z U V).hom).mp
  dsimp only [i1_relativeDomainBinarySequence]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (i1_relativeDomainIntersectionChainIso X Z U V).hom ≫
      biprod.lift _ (-_) = biprod.lift _ (-_) ≫
        biprod.map (i1_subsetRelativeChainIso X Z U).hom (i1_subsetRelativeChainIso X Z V).hom
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
    exact i1_relativeDomainIntersectionChainIso_naturality X Z U V U Set.inter_subset_left
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
      Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg
      (i1_relativeDomainIntersectionChainIso_naturality X Z U V V Set.inter_subset_right)

end HodgeLean.Foundations.BundleResolution
