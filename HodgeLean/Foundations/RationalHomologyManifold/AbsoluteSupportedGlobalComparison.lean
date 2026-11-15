import HodgeLean.Foundations.RationalHomologyManifold.GlobalSupportedStageComparison
import HodgeLean.Foundations.RationalHomologyManifold.SupportedRelativePatching

/-! Actual absolute-chain comparison with global supported subdivision sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Project actual absolute chains to the original supported chain presheaf on the whole space.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains modulo the empty subspace.
HC no distance; AV milestone no distance.
-/
def absoluteSupportedGlobalProjection (X : TopCat.{0}) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (SingularChainComplex ℚ X) ⟶
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainPresheafComplex ℚ X) where
  f n := (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) ((⊤ : Opens X) : Set X)ᶜ)).f n)
  comm' i j hij := by
    obtain rfl := hij
    let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
    let P := TopPair.ofSubset (X := X) ((⊤ : Opens X) : Set X)ᶜ
    change F.map ((relativeChainProjection ℚ P).f (j + 1)) ≫
        ((singularChainPresheafComplex ℚ X).d (j + 1) j).app (Opposite.op ⊤) =
      F.map ((SingularChainComplex ℚ X).d (j + 1) j) ≫ F.map ((relativeChainProjection ℚ P).f j)
    rw [singularChainPresheafComplex_d]
    change F.map ((relativeChainProjection ℚ P).f (j + 1)) ≫
        F.map (((relativeChainFunctor ℚ).obj P).d (j + 1) j) =
      F.map ((SingularChainComplex ℚ X).d (j + 1) j) ≫ F.map ((relativeChainProjection ℚ P).f j)
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map ((relativeChainProjection ℚ P).comm (j + 1) j)

#print axioms absoluteSupportedGlobalProjection
/-- Actual absolute chains and supported chains on the whole space are canonically isomorphic as chain complexes.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains modulo the empty subspace.
HC no distance; AV milestone no distance.
-/
theorem absoluteSupportedGlobalProjection_isIso (X : TopCat.{0}) :
    IsIso (absoluteSupportedGlobalProjection X) := by
  letI : ∀ n, IsIso ((absoluteSupportedGlobalProjection X).f n) := fun n => by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective ((relativeChainProjection ℚ
      (TopPair.ofSubset (X := X) ((⊤ : Opens X) : Set X)ᶜ)).f n)
    exact ⟨topSupportedChainProjection_injective X n,
      relativeChainProjection_surjective (TopPair.ofSubset (X := X) ((⊤ : Opens X) : Set X)ᶜ) n⟩
  exact HomologicalComplex.Hom.isIso_of_components _

#print axioms absoluteSupportedGlobalProjection_isIso
/-- The actual absolute singular-chain map into global sections of the supported subdivision-limit sheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; the global singular-chain comparison.
HC no distance; AV milestone no distance.
-/
def absoluteSubdivisionGlobalComparison (X : TopCat.{0}) :
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (SingularChainComplex ℚ X) ⟶
    (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (subdivisionLimitSheafComplex X)) :=
  absoluteSupportedGlobalProjection X ≫ supportedStageZeroGlobalComparison X

#print axioms absoluteSubdivisionGlobalComparison
/-- The actual absolute singular-chain comparison with global subdivision sheaf sections is a quasi-isomorphism.
Source: Bredon, Sheaf Theory, second edition, VI.12; the global singular-chain comparison on compact spaces.
HC no distance; AV milestone no distance.
-/
theorem absoluteSubdivisionGlobalComparison_quasiIso (X : TopCat.{0})
    [CompactSpace X] [T2Space X] : QuasiIso (absoluteSubdivisionGlobalComparison X) := by
  letI := absoluteSupportedGlobalProjection_isIso X
  letI := supportedStageZeroGlobalComparison_quasiIso X
  change QuasiIso (absoluteSupportedGlobalProjection X ≫ supportedStageZeroGlobalComparison X)
  infer_instance

#print axioms absoluteSubdivisionGlobalComparison_quasiIso
/-- The global absolute-chain comparison uses the actual ambient projection at stage zero in every degree.
Source: Bredon, Sheaf Theory, second edition, VI.12; normalization of the canonical global chain map.
HC no distance; AV milestone no distance.
-/
theorem absoluteSubdivisionGlobalComparison_component (X : TopCat.{0}) (n : ℕ) :
    (absoluteSubdivisionGlobalComparison X).f n = subdivisionAmbientSectionMap X n ⊤ 0 := rfl

#print axioms absoluteSubdivisionGlobalComparison_component
end HodgeLean.Foundations.RationalHomologyManifold
