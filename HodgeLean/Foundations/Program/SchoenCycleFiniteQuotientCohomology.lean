import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs
import Mathlib.RepresentationTheory.Invariants

/-! # Pullback compatibility for quotient comparison
Actual singular pullback respects an invariant scheme morphism in every degree.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Composition for the actual complex-point singular pullback.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of cohomology. -/
theorem s2e_quotient_pullback_comp {X Y Z : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    s2e_pullback ℚ (f ≫ g) n =
      (s2e_pullback ℚ f n).comp (s2e_pullback ℚ g n) := by
  exact AlgebraicTopology.Singular.cohomologyMap_comp ℚ n
    (TopCat.ofHom (Point.continuousMap f)) (TopCat.ofHom (Point.continuousMap g))

/-- The actual pullback takes values fixed by every symmetry over the quotient.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of cohomology;
Schoen, Compositio Mathematica 65 (1988), printed p. 18. -/
theorem s2e_quotient_pullback_invariant {X Y : Over (Spec ↧ℂ)}
    (G : Type*) (a : G → (X ⟶ X)) (q : X ⟶ Y)
    (hinv : ∀ u, a u ≫ q = q) (n : ℕ)
    (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint Y)) n)
    (u : G) :
    s2e_pullback ℚ (a u) n (s2e_pullback ℚ q n c) = s2e_pullback ℚ q n c := by
  have h := congrArg (fun f => f c) (s2e_quotient_pullback_comp (a u) q n)
  rw [hinv u] at h
  exact h.symm

/-- Surjectivity on points suffices for rational pullback injectivity in degree zero.
Source: Hatcher, Algebraic Topology, §2.1 (degree-zero homology) and
§3.1 (universal coefficients over a field). -/
theorem s2e_surjective_cohomology_zero_injective {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : Function.Surjective f) :
    Function.Injective (AlgebraicTopology.Singular.cohomologyMap ℚ 0 f) := by
  let φ := AlgebraicTopology.Singular.singularChainComplexMap ℚ f
  have hf₀ : Function.Surjective ((TopCat.toSSet.map f).app
      (Opposite.op (SimplexCategory.mk 0))) := by
    intro y
    let t := Y.toSSetObjEquiv _ y
    obtain ⟨x, hx⟩ := hf (t (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1)))
    refine ⟨(X.toSSetObjEquiv _).symm (ContinuousMap.const _ x), ?_⟩
    apply (Y.toSSetObjEquiv _).injective
    ext z
    change f x = t z
    exact hx.trans (congrArg t (Subsingleton.elim _ _))
  have hep : Epi (φ.f 0) := by
    constructor
    intro Z g h e
    apply SSet.chainComplex_hom_ext
    intro y
    obtain ⟨x, rfl⟩ := hf₀ y
    have he := congrArg (fun k => (TopCat.toSSet.obj X).ιChainComplex x ≫ k) e
    change ((TopCat.toSSet.obj X).ιChainComplex x ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0) ≫ g =
      ((TopCat.toSSet.obj X).ιChainComplex x ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0) ≫ h at he
    simpa only [SSet.ι_chainComplexMap_f] using he
  have hepH : Epi (HomologicalComplex.homologyMap φ 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel φ 0 (by intro j; simp)
  have hs : Function.Surjective (AlgebraicTopology.Singular.homologyMap ℚ 0 f) :=
    (ModuleCat.epi_iff_surjective _).mp hepH
  intro a b hab
  apply (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ Y 0).injective
  ext z
  obtain ⟨w, rfl⟩ := hs z
  have he := congrArg (fun c =>
    AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ X 0 c w) hab
  simpa only [AlgebraicTopology.Singular.cohomologyEquivDualHomology_cohomologyMap] using he

/-- The cohomology representation uses inverse symmetries because pullback is contravariant.
Source: Hatcher, Algebraic Topology, §3.1; Serre, Linear Representations
of Finite Groups, Part I, Chapter 1. -/
def s2e_quotientCohomologyRepresentation (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (n : ℕ) :
    Representation ℚ G
      (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) n) where
  toFun g := s2e_pullback ℚ (a g⁻¹) n
  map_one' := by
    rw [inv_one, ha1]
    exact AlgebraicTopology.Singular.cohomologyMap_id ℚ _ n
  map_mul' u v := by
    rw [mul_inv_rev, hamul, s2e_quotient_pullback_comp]
    rfl

example (X : Over (Spec ↧ℂ)) (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (g : G) :
    s2e_quotientCohomologyRepresentation X G a ha1 hamul n g =
      s2e_pullback ℚ (a g⁻¹) n := rfl

/-- The actual quotient pullback with codomain restricted to the invariant subspace.
Source: Hatcher, Algebraic Topology, §3.1, functoriality; Schoen,
Compositio Mathematica 65 (1988), printed p. 18. -/
def s2e_quotientPullbackToInvariants {X Y : Over (Spec ↧ℂ)}
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint Y)) n →ₗ[ℚ]
      (s2e_quotientCohomologyRepresentation X G a ha1 hamul n).invariants :=
  (s2e_pullback ℚ q n).codRestrict _ (fun c u =>
    s2e_quotient_pullback_invariant G a q hinv n c u⁻¹)

/-- Forgetting invariance recovers precisely pullback along the specified scheme map.
Source: Hatcher, Algebraic Topology, §3.1; Schoen, Compositio
Mathematica 65 (1988), printed p. 18. -/
theorem s2e_quotientPullbackToInvariants_coe {X Y : Over (Spec ↧ℂ)}
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (n : ℕ)
    (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint Y)) n) :
    (s2e_quotientPullbackToInvariants G a ha1 hamul q hinv n c).val =
      s2e_pullback ℚ q n c := rfl

example {X Y : Over (Spec ↧ℂ)}
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (n : ℕ) :
    s2e_quotientPullbackToInvariants G a ha1 hamul q hinv n 0 = 0 := map_zero _

/-- Natural universal coefficients turns rational homology surjectivity into
cohomology injectivity, and conversely, without a finiteness assumption.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficient theorem. -/
theorem s2e_cohomology_injective_iff_homology_surjective
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    Function.Injective (AlgebraicTopology.Singular.cohomologyMap ℚ n f) ↔
      Function.Surjective (AlgebraicTopology.Singular.homologyMap ℚ n f) := by
  let eX := AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ X n
  let eY := AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ Y n
  constructor
  · intro hf
    apply LinearMap.dualMap_injective_iff.mp
    intro a b hab
    have hc : AlgebraicTopology.Singular.cohomologyMap ℚ n f (eY.symm a) =
        AlgebraicTopology.Singular.cohomologyMap ℚ n f (eY.symm b) := by
      apply eX.injective
      ext z
      have hz := LinearMap.congr_fun hab z
      simpa only [eX, eY,
        AlgebraicTopology.Singular.cohomologyEquivDualHomology_cohomologyMap,
        LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply] using hz
    exact eY.symm.injective (hf hc)
  · intro hf a b hab
    apply eY.injective
    ext z
    obtain ⟨w, rfl⟩ := hf z
    have he := congrArg (fun c => eX c w) hab
    simpa only [eX,
      AlgebraicTopology.Singular.cohomologyEquivDualHomology_cohomologyMap] using he

/-- A homology transfer of nonzero degree gives injective rational pullback.
Source: Hatcher, Algebraic Topology, §3.1, natural universal coefficients. -/
theorem s2e_cohomology_injective_of_homology_transfer
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (d : ℚ) (hd : d ≠ 0)
    (T : AlgebraicTopology.Singular.Homology ℚ Y n →ₗ[ℚ]
      AlgebraicTopology.Singular.Homology ℚ X n)
    (hT : (AlgebraicTopology.Singular.homologyMap ℚ n f).comp T =
      d • LinearMap.id) :
    Function.Injective (AlgebraicTopology.Singular.cohomologyMap ℚ n f) := by
  apply (s2e_cohomology_injective_iff_homology_surjective f n).mpr
  intro y
  refine ⟨T (d⁻¹ • y), ?_⟩
  have h := LinearMap.congr_fun hT (d⁻¹ • y)
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_smul, mul_inv_cancel₀ hd, one_smul] using h

end HodgeLean.Foundations.Program
