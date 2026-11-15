import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Proofs

/-! # First-stage singular cycle statements

Generic coefficients and relative pullback retain the existing constructions.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters TopologicalSpace
namespace AlgebraicGeometry.SingularCycles

/-- Supported pullback commutes with forgetting support.
Source: Hatcher, Algebraic Topology, §3.1. -/
theorem pullback_forget {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) (n : ℕ)
    (c : CohomologyWithSupport ℚ Y S n) :
    forgetSupport ℚ X (f ⁻¹' S) n (cohomologyWithSupportMap ℚ n f S c) =
      cohomologyMap ℚ n f (forgetSupport ℚ Y S n c) := pullback_forget_aux f S n c

example (X : TopCat.{0}) (S : Set X) (n : ℕ)
    (c : CohomologyWithSupport ℚ X S n) :
    cohomologyWithSupportMap ℚ n (𝟙 X) S c = c := by
  rw [cohomologyWithSupportMap_id]
  rfl

/-- Supported pullback is contravariant under composition.
Source: Hatcher, Algebraic Topology, §3.1. -/
theorem pullback_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (S : Set Z) (n : ℕ)
    (c : CohomologyWithSupport ℚ Z S n) :
    cohomologyWithSupportMap ℚ n (f ≫ g) S c =
      cohomologyWithSupportMap ℚ n f (g ⁻¹' S)
        (cohomologyWithSupportMap ℚ n g S c) := pullback_comp_aux f g S n c

example :
    (preimageSupportPairMap (TopCat.ofHom ⟨fun z : ℂ => -z, continuous_neg⟩)
      ({0} : Set ℂ)).hom.right (1 : ℂ) = (-1 : ℂ) := rfl

/-- Generic multiplicities are positive and recover the extended stalk length.
Source: Fulton, Intersection Theory, second edition, §1.5; ccm3_genericLength_finite_pos. -/
theorem genericMultiplicity_pos {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    0 < genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 ∧
      (genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 : ℕ∞) = ccm3_genericLength f.left x y := genericMultiplicity_pos_aux f x y hy

example {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    0 < ccm3_genericLength f.left x y :=
  (ccm3_genericLength_finite_pos f x y hy).1

/-- Prime inverse-image coefficients are the actual generic stalk multiplicities.
Source: Fulton, Intersection Theory, second edition, §1.7; ccm3_flatPullbackPrime_coeff. -/
theorem prime_coefficient {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    ccm3_flatPullbackPrime f.left x ((ccm3_inverseIdeal f.left x).subschemeι y) =
      (genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 : ℚ) := prime_coefficient_aux f x y hy

example {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    ccm3_flatPullbackPrime f.left x ((ccm3_inverseIdeal f.left x).subschemeι y) =
      (genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 : ℚ) :=
  ccm3_flatPullbackPrime_coeff f x y hy

/-- Reduced inverse images have generic coefficient one.
Source: Fulton, Intersection Theory, second edition, §1.5; Mathlib isField_stalk_of_closure_mem_irreducibleComponents. -/
theorem reduced_genericMultiplicity {X Z : Scheme} (f : X ⟶ Z) (x : Z)
    [IsReduced (ccm3_inverseIdeal f x).subscheme]
    (y : (ccm3_inverseIdeal f x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f x).subscheme) :
    genericMultiplicity f x y (by
        have hfield := isField_stalk_of_closure_mem_irreducibleComponents
          (ccm3_inverseIdeal f x).subscheme y hy
        letI := hfield.toField
        change Module.length _ _ < ⊤
        rw [Module.length_eq_one]
        exact ENat.coe_lt_top 1) = 1 := reduced_genericMultiplicity_aux f x y hy

example : Module.length ℚ ℚ = 1 := Module.length_eq_one ℚ ℚ

/-- Finite flat prime inverse images have the full inverse-image analytic support.
Source: Fulton, Intersection Theory, second edition, §1.7; ccm3_flatPullbackPrime_support. -/
theorem prime_support_preimage {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [IsFinite f.left] [Flat f.left] (x : Z.left) :
    a3b4_cycleSupport X.hom (ccm3_flatPullbackPrime f.left x) =
      Point.map f ⁻¹' a3b4_cycleSupport Z.hom
        (Function.locallyFinsuppWithin.single x (1 : ℚ)) := prime_support_preimage_aux f x

example (Z : Over (Spec ↧ℂ)) :
    a3b4_cycleSupport Z.hom (0 : AlgebraicCycle Z.left ℚ) = ∅ := by
  ext x
  simp [a3b4_cycleSupport]

/-- Finite étale pullback preserves local complex normalization on singular ambients.
Source: Fulton, Intersection Theory, second edition, §§1.7 and 19.1; Borel–Haefliger, La classe d’homologie fondamentale d’un espace analytique (1961), §2. -/
theorem etale_prime_normalized_pullback {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) [IsFinite f.left] [Etale f.left] (x : Z.left) (k : ℕ)
    (hx : Order.coheight x = k)
    (hS : ∀ z, Point.map f z ∈ a3b4_cycleSupport Z.hom
        (Function.locallyFinsuppWithin.single x (1 : ℚ)) →
      z ∈ a3b4_cycleSupport X.hom (ccm3_flatPullbackPrime f.left x))
    (c : CohomologyWithSupport ℚ (a3b4_an Z.hom)
      (a3b4_cycleSupport Z.hom (Function.locallyFinsuppWithin.single x (1 : ℚ))) (2 * k))
    (hc : a3b4_IsCycleClass Z.hom
      (Function.locallyFinsuppWithin.single x (1 : ℚ)) k c) :
    a3b4_IsCycleClass X.hom (ccm3_flatPullbackPrime f.left x) k
      (relativeCohomologyMap ℚ (2 * k)
        (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap f))
          (a3b4_cycleSupport X.hom (ccm3_flatPullbackPrime f.left x))
          (a3b4_cycleSupport Z.hom (Function.locallyFinsuppWithin.single x (1 : ℚ))) hS) c) := etale_prime_normalized_pullback_aux f x k hx hS c hc

example (Z : Over (Spec ↧ℂ)) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (k : ℕ) :
    a3b4_IsCycleClass Z.hom (0 : AlgebraicCycle Z.left ℚ) k 0 := by
  intro r e hS x _ hx
  simp [a3b4_cycleSupport] at hx

example : standardComplexLocalClass ℚ 1 ≠ 0 :=
  standardComplexLocalClass_ne_zero_for_chart 1

end AlgebraicGeometry.SingularCycles
