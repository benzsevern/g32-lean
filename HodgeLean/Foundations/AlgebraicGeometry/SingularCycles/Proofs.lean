import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs
import Other.AlgebraicTopology.Singular.SupportNaturality
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Support
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleChartTransport
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleMultiplicity
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.PrimeMultiplicity
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.LocalPairTransport

/-! # First-stage singular cycle proof obligations

Generic coefficients and relative pullback retain the existing constructions.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters TopologicalSpace
namespace AlgebraicGeometry.SingularCycles

/-- Supported pullback commutes with forgetting support.
Source: Hatcher, Algebraic Topology, §3.1. -/
theorem pullback_forget_aux {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) (n : ℕ)
    (c : CohomologyWithSupport ℚ Y S n) :
    forgetSupport ℚ X (f ⁻¹' S) n (cohomologyWithSupportMap ℚ n f S c) =
      cohomologyMap ℚ n f (forgetSupport ℚ Y S n c) := by
  exact (cohomologyMap_forgetSupport ℚ n f S c).symm

example (X : TopCat.{0}) (S : Set X) (n : ℕ)
    (c : CohomologyWithSupport ℚ X S n) :
    cohomologyWithSupportMap ℚ n (𝟙 X) S c = c := by
  rw [cohomologyWithSupportMap_id]
  rfl

/-- Supported pullback is contravariant under composition.
Source: Hatcher, Algebraic Topology, §3.1. -/
theorem pullback_comp_aux {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (S : Set Z) (n : ℕ)
    (c : CohomologyWithSupport ℚ Z S n) :
    cohomologyWithSupportMap ℚ n (f ≫ g) S c =
      cohomologyWithSupportMap ℚ n f (g ⁻¹' S)
        (cohomologyWithSupportMap ℚ n g S c) := by
  change relativeCohomologyMap ℚ n _ c = _
  rw [show preimageSupportPairMap (f ≫ g) S =
    preimageSupportPairMap f (g ⁻¹' S) ≫ preimageSupportPairMap g S from rfl]
  rw [relativeCohomologyMap_comp]
  rfl

example :
    (preimageSupportPairMap (TopCat.ofHom ⟨fun z : ℂ => -z, continuous_neg⟩)
      ({0} : Set ℂ)).hom.right (1 : ℂ) = (-1 : ℂ) := rfl

/-- Generic multiplicities are positive and recover the extended stalk length.
Source: Fulton, Intersection Theory, second edition, §1.5; ccm3_genericLength_finite_pos. -/
theorem genericMultiplicity_pos_aux {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    0 < genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 ∧
      (genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 : ℕ∞) = ccm3_genericLength f.left x y := by
  have h := ccm3_genericLength_finite_pos f x y hy
  exact ⟨ENat.toNat_pos (ne_of_gt h.1) (ne_of_lt h.2),
    ENat.natCast_toNat (ne_of_lt h.2)⟩

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
theorem prime_coefficient_aux {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    ccm3_flatPullbackPrime f.left x ((ccm3_inverseIdeal f.left x).subschemeι y) =
      (genericMultiplicity f.left x y (ccm3_genericLength_finite_pos f x y hy).2 : ℚ) := by
  exact ccm3_flatPullbackPrime_coeff f x y hy

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
theorem reduced_genericMultiplicity_aux {X Z : Scheme} (f : X ⟶ Z) (x : Z)
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
        exact ENat.coe_lt_top 1) = 1 := by
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents
    (ccm3_inverseIdeal f x).subscheme y hy
  letI := hfield.toField
  unfold genericMultiplicity ccm3_genericLength
  rw [Module.length_eq_one]
  rfl

example : Module.length ℚ ℚ = 1 := Module.length_eq_one ℚ ℚ

/-- Finite flat prime inverse images have the full inverse-image analytic support.
Source: Fulton, Intersection Theory, second edition, §1.7; ccm3_flatPullbackPrime_support. -/
theorem prime_support_preimage_aux {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [IsFinite f.left] [Flat f.left] (x : Z.left) :
    a3b4_cycleSupport X.hom (ccm3_flatPullbackPrime f.left x) =
      Point.map f ⁻¹' a3b4_cycleSupport Z.hom
        (Function.locallyFinsuppWithin.single x (1 : ℚ)) := by
  rw [a3b4_cycleSupport, prime_cycle_algebraic_support, prime_cycle_analytic_support]
  ext z
  change z.underlying ∈ (ccm3_inverseIdeal f.left x).support ↔
    (Point.map f z).underlying ∈ closure {x}
  rw [ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap]
  change f.left z.underlying ∈ (ccm3_primeIdeal Z.left x).support ↔ _
  simp only [ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

example (Z : Over (Spec ↧ℂ)) :
    a3b4_cycleSupport Z.hom (0 : AlgebraicCycle Z.left ℚ) = ∅ := by
  ext x
  simp [a3b4_cycleSupport]

/-- Finite étale pullback preserves local complex normalization on singular ambients.
Source: Fulton, Intersection Theory, second edition, §§1.7 and 19.1; Borel–Haefliger, La classe d’homologie fondamentale d’un espace analytique (1961), §2. -/
theorem etale_prime_normalized_pullback_aux {X Z : Over (Spec ↧ℂ)}
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
          (a3b4_cycleSupport Z.hom (Function.locallyFinsuppWithin.single x (1 : ℚ))) hS) c) := by
  let S := a3b4_cycleSupport X.hom (ccm3_flatPullbackPrime f.left x)
  let T := a3b4_cycleSupport Z.hom (Function.locallyFinsuppWithin.single x (1 : ℚ))
  let F : a3b4_an X.hom ⟶ a3b4_an Z.hom := TopCat.ofHom (Point.continuousMap f)
  have hSmap : ∀ z : a3b4_an X.hom, F z ∈ T → z ∈ S := fun z hz => hS z hz
  have hST : ∀ z : ComplexPoint X, Point.map f z ∈ T ↔ z ∈ S := by
    intro z
    exact (Set.ext_iff.mp (prime_support_preimage_aux f x) z).symm
  intro r e hflat z hz hzS he
  obtain ⟨W, hWo, hzW, hWe, _, E, hE, hEs, hval⟩ := etale_chart_transport f e he z hz
  have hflatT : ∀ y ∈ E.source, y ∈ T ↔ (E y).2 = 0 := by
    intro y hy
    rw [hEs] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hval w hw]
    exact (hST w).trans (hflat w (hWe hw))
  have hzE : Point.map f z ∈ E.source := by
    rw [hEs]
    exact ⟨z, hzW, rfl⟩
  have hzT : Point.map f z ∈ T := (hST z).mpr hzS
  obtain ⟨N, hNE, hNo, hzN, hnorm⟩ := hc r E hflatT (Point.map f z) hzE hzT hE
  rw [prime_cycle_multiplicity_one Z x _, one_smul] at hnorm
  let V : Set (ComplexPoint X) := W ∩ Point.map f ⁻¹' N
  have hVo : IsOpen V := hWo.inter (hNo.preimage (Point.continuous_map f))
  have hVe : V ⊆ e.source := fun w hw => hWe hw.1
  have hzV : z ∈ V := ⟨hzW, hzN⟩
  refine ⟨V, hVe, hVo, hzV, ?_⟩
  rw [etale_prime_chart_multiplicity_one f x e he hflat z hz hzS, one_smul]
  have hVN : ∀ w ∈ V, F w ∈ N := fun w hw => hw.2
  let p := neighborhoodPullbackPairMap F S T hSmap V N hVN
  have hcomp := neighborhoodPullbackPairMap_naturality F S T hSmap V N hVN
  calc
    relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap V S)
        (relativeCohomologyMap ℚ (2 * k) (a3b4_supportPairMap F S T hSmap) c) =
        relativeCohomologyMap ℚ (2 * k) p
          (relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N T) c) := by
      have h := congrArg (fun a => relativeCohomologyMap ℚ (2 * k) a c) hcomp.symm
      rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at h
      exact h
    _ = relativeCohomologyMap ℚ (2 * k) p
        (chartNormalProjectionCoclass (Fin r → ℂ) k E T hflatT N hNE) :=
      congrArg (relativeCohomologyMap ℚ (2 * k) p) hnorm
    _ = chartNormalProjectionCoclass (Fin r → ℂ) k e S hflat V hVe :=
      neighborhoodPullbackPairMap_normalCoclass F S T hSmap V N hVN r k e E
        hflat hflatT hVe hNE (fun w hw => (hval w hw.1).symm)

example (Z : Over (Spec ↧ℂ)) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (k : ℕ) :
    a3b4_IsCycleClass Z.hom (0 : AlgebraicCycle Z.left ℚ) k 0 := by
  intro r e hS x _ hx
  simp [a3b4_cycleSupport] at hx

example : standardComplexLocalClass ℚ 1 ≠ 0 :=
  standardComplexLocalClass_ne_zero_for_chart 1

end AlgebraicGeometry.SingularCycles
