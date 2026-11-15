import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import HodgeLean.Foundations.Program.SchoenTransferC1a5ExactHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeDefs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! Functorial squares for relative chain comparisons.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Relative unit naturality for a square of simplicial maps.
Source: Hatcher, Algebraic Topology, §2.1, maps of pairs. -/
lemma c1a5_relative_square_naturality {A B C D : SSet.{0}}
    (f : A ⟶ B) (g : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : f ≫ b = a ≫ g) :
    c1a5RelativeMap c1a5Chains f g a b w ≫ c1a5RelativeUnit g =
      c1a5RelativeUnit f ≫ c1a5RelativeMap c1a5SingularChains f g a b w := by
  apply (cancel_epi (cokernel.π (c1a5Chains.map f))).1
  simp only [c1a5RelativeMap, c1a5RelativeUnit, cokernel.map, cokernel.π_desc_assoc, Category.assoc]
  simp only [cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc]
  rw [← Category.assoc, c1a5Unit_naturality, Category.assoc]

/-- Integral simplicial chains preserve pushouts degree by degree.
Source: Mathlib sigmaConst and alternatingFaceMapComplex. -/
instance c1a5_chains_preserves_pushouts :
    PreservesColimitsOfShape WalkingSpan c1a5Chains := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape WalkingSpan
    ((evaluation _ _).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj (ModuleCat.of ℤ ℤ))
  infer_instance

/-- Simplicial cell excision is an isomorphism on relative chains.
Source: Mathlib relativeCellComplexOfMono.isPushout and cokernel pushout transport. -/
lemma c1a5_simplicial_cell_excision {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    let l := SSet.relativeCellComplexOfMono.l i n
    let r := SSet.relativeCellComplexOfMono.r i n
    let t := SSet.relativeCellComplexOfMono.t i n
    let b := SSet.relativeCellComplexOfMono.b i n
    let w := (SSet.relativeCellComplexOfMono.w i n).symm
    IsIso (c1a5RelativeMap c1a5Chains l r t b w) := by
  dsimp only
  exact isIso_cokernel_map_of_isPushout
    ((SSet.relativeCellComplexOfMono.isPushout i n).flip.map c1a5Chains)

/-- A simplicial monomorphism induces a monomorphic integral chain map.
Source: Mathlib sigmaConst preserves monomorphisms. -/
lemma c1a5_chains_map_mono {A B : SSet.{0}} (f : A ⟶ B) [Mono f] :
    Mono (c1a5Chains.map f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (f.app (Opposite.op ⦋n⦌)))
  infer_instance

/-- Realized monomorphy supplies both short exact pair sequences.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair. -/
lemma c1a5_pair_comparison_of_realization_mono {A B : SSet.{0}} (f : A ⟶ B)
    [Mono f] [Mono (SSet.toTop.map f)]
    (ha : QuasiIso (c1a5Unit A)) (hb : QuasiIso (c1a5Unit B)) :
    QuasiIso (c1a5RelativeUnit f) := by
  have := c1a5_chains_map_mono f
  have : Mono (c1a5SingularChains.map f) :=
    inferInstanceAs (Mono ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ))).map (SSet.toTop.map f)))
  exact c1a5_cokernel_comparison _ _ _ _ (c1a5Unit_naturality f) ha hb

/-- Ambient comparison from the actual pair square with realized monomorphy explicit.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair and five lemma. -/
lemma c1a5_ambient_comparison_of_realization_mono {A B : SSet.{0}} (f : A ⟶ B)
    [Mono f] [Mono (SSet.toTop.map f)]
    (ha : QuasiIso (c1a5Unit A)) (hr : QuasiIso (c1a5RelativeUnit f)) :
    QuasiIso (c1a5Unit B) := by
  have := c1a5_chains_map_mono f
  have : Mono (c1a5SingularChains.map f) :=
    inferInstanceAs (Mono ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ))).map (SSet.toTop.map f)))
  exact c1a5_cokernel_middle_comparison _ _ _ _ (c1a5Unit_naturality f) ha hr

end HodgeLean.Foundations.Program
