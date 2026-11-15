import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonRestriction
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeForgetNaturality

/-! # Original degree-zero normal coclasses after forgetting support -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Pullback to the actual space of the original normalized zero-dimensional normal coclass.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3, relative normal coclasses.
HC no distance; AV milestone no distance. -/
def properCycle_zero_normal_absolute (X : TopCat.{0}) : Cohomology ℚ X 0 :=
  cohomologyMap ℚ 0 (TopCat.ofHom ⟨fun _ => (0 : Fin 0 → ℂ), continuous_const⟩)
    (relativeCohomologyToAbsolute ℚ (puncturedPair ℂ 0) 0
      (normalizedRelativeCoclass (standardComplexLocalClass ℚ 0)
        (standardComplexLocalClass_ne_zero_for_chart 0)))

/-- Original chart normalization determines the absolute class of every nonzero cycle on a zero-dimensional integral complex scheme.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 3.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_normalized_absolute
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    (γ : AlgebraicCycle X.left ℚ) (hγ : γ ≠ 0)
    (a : s2e_supportedClass X γ 0) (ha : a3b4_IsCycleClass X.hom γ 0 a) :
    s2e_classToAbsolute X γ 0 a =
      γ (genericPoint X.left) • properCycle_zero_normal_absolute (a3b4_an X.hom) := by
  classical
  letI : Subsingleton (ComplexPoint X) := properCycle_zero_dimension_complex_subsingleton X hdim
  letI : Subsingleton (a3b4_an X.hom) := properCycle_zero_dimension_complex_subsingleton X hdim
  letI : Unique (ComplexPoint X) :=
    { default := Classical.choice (properCycle_zero_dimension_complex_nonempty X hdim)
      uniq := fun _ => Subsingleton.elim _ _ }
  letI : Unique ((Fin 0 → ℂ) × (Fin 0 → ℂ)) :=
    { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  let e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin 0 → ℂ)) :=
    (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph
  let x : ComplexPoint X := default
  let S := a3b4_cycleSupport X.hom γ
  have hwhole : S = Set.univ := properCycle_zero_dimension_nonzero_support X hdim γ hγ
  have hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0 := by
    intro y _
    exact iff_of_true (by rw [hwhole]; trivial) (Subsingleton.elim _ _)
  have he : a3b4_IsHolChart X.hom e := ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  have hx : x ∈ e.source := Set.mem_univ x
  have hxS : x ∈ S := by rw [hwhole]; trivial
  have hξ : genericPoint X.left ∈ γ.support := by
    by_contra hn
    apply hγ
    ext η
    rw [properCycle_zero_dimension_point_eq_generic X hdim η]
    exact not_ne_iff.mp hn
  have hxξ : x.underlying ∈ closure ({genericPoint X.left} : Set X.left) := by
    apply specializes_iff_mem_closure.mp
    exact Scheme.le_iff_specializes.mp le_top
  have hm : a3b4_multiplicity X.hom γ x = γ (genericPoint X.left) :=
    a3b4a_classMultiplicity_eq_component X.hom γ _ hξ x hxξ
      (fun η _ hn _ => hn (properCycle_zero_dimension_point_eq_generic X hdim η))
  obtain ⟨W, hWe, hWo, hxW, hW⟩ := ha 0 e hS x hx hxS he
  rw [hm] at hW
  let P := TopPair.ofSubset (X := a3b4_an X.hom) Sᶜ
  let F : P ⟶ puncturedPair ℂ 0 := TopPair.ofHom
    (TopCat.ofHom ⟨fun _ => 0, continuous_const⟩)
    (TopCat.ofHom ⟨fun y => ⟨0, by exact (y.2 (Set.eq_univ_iff_forall.mp hwhole y.1)).elim⟩, by fun_prop⟩)
    (by ext y; rfl)
  letI : Subsingleton (puncturedPair ℂ 0).fst := inferInstanceAs (Subsingleton (Fin 0 → ℂ))
  letI : Subsingleton (puncturedPair ℂ 0).snd :=
    inferInstanceAs (Subsingleton ({0}ᶜ : Set (Fin 0 → ℂ)))
  have hcomp : a3b4_neighborhoodPairMap W S ≫ F =
      chartNormalProjectionPair (Fin 0 → ℂ) 0 e S hS W hWe := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y : 1
      exact Subsingleton.elim _ _
    · ext y : 1
      exact Subsingleton.elim _ _
  have hfa : a = γ (genericPoint X.left) • relativeCohomologyMap ℚ 0 F
      (normalizedRelativeCoclass (standardComplexLocalClass ℚ 0)
        (standardComplexLocalClass_ne_zero_for_chart 0)) := by
    apply properCycle_subsingleton_neighborhood_restriction_injective (a3b4_an X.hom) S W x hxW 0
    rw [map_smul, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomp]
    exact hW
  rw [hfa, map_smul]
  unfold properCycle_zero_normal_absolute
  exact congrArg (fun b => γ (genericPoint X.left) • b)
    (properCycle_relative_forget_naturality F 0 _)

/-- The original zero-dimensional normal absolute coclass is natural under every actual continuous map.
Source: Hatcher, Algebraic Topology, section 3.1, functoriality of pullback.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_normal_absolute_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    cohomologyMap ℚ 0 f (properCycle_zero_normal_absolute Y) = properCycle_zero_normal_absolute X := by
  unfold properCycle_zero_normal_absolute
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
  rfl

end HodgeLean.Foundations.QuotientDuality
