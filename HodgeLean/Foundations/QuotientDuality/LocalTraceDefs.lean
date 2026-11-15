import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Relative
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CochainCohomologyEquiv
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartClassHomeomorph
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Local rational orientations and the actual cap pairing

Orientations are locally liftable sections of relative singular homology.
The pairing uses the Alexander–Whitney cap construction, with no supplied
bilinear product or perfectness field.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- A locally coherent rational orientation, before a global class is selected.
Source: Bredon, Sheaf Theory, second edition, V.9 (orientation sheaf);
Hatcher, Algebraic Topology, section 3.3, local orientations. -/
structure LocalRationalOrientation (X : TopCat.{0}) (n : ℕ) where
  generator : ∀ x : X, orientationGroup X n x
  generates : ∀ x, Function.Bijective
    (LinearMap.toSpanSingleton ℚ _ (generator x))
  vanishes : ∀ x i, i ≠ n → Subsingleton (orientationGroup X i x)
  coherent : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ c : RelativeHomology ℚ (TopPair.ofSubset (U : Set X)ᶜ) n,
      ∀ y (hy : y ∈ U), relativeHomologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hy)) c = generator y

example (X : TopCat.{0}) (n : ℕ) (o : LocalRationalOrientation X n) (x : X) :
    o.generator x ≠ 0 := by
  intro h
  have hi := (o.generates x).1
  have he := hi (show LinearMap.toSpanSingleton ℚ _ (o.generator x) (0 : ℚ) =
      LinearMap.toSpanSingleton ℚ _ (o.generator x) (1 : ℚ) by simp [h])
  exact zero_ne_one he

/-- Evaluation of the actual singular cap product, curried as the duality map.
The convention is evaluation of b on a cap c, fixing the order of the factors.
Source: Hatcher, Algebraic Topology, section 3.3, cap product and Theorem 3.30. -/
def localTracePairing (X : TopCat.{0}) (p q : ℕ) (c : Homology ℚ X (p + q)) :
    Cohomology ℚ X p →ₗ[ℚ] Module.Dual ℚ (Cohomology ℚ X q) where
  toFun a :=
    { toFun := fun b => cohomologyEquivDualHomology ℚ X q b
        (capCohomologyLinear ℚ X p q ((cochainCohomologyEquiv ℚ X p).symm a) c)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext b; simp
  map_smul' := by intros; ext b; simp

example (X : TopCat.{0}) (p q : ℕ) (c : Homology ℚ X (p + q))
    (a : Cohomology ℚ X p) (b : Cohomology ℚ X q) :
    localTracePairing X p q ((2 : ℚ) • c) a b =
      2 * localTracePairing X p q c a b := by
  simp [localTracePairing]

/-- Rational cup product reconstructed from the actual cap product and universal coefficients.
Source: Hatcher, Algebraic Topology, section 3.3, cup-cap evaluation identity. -/
def localTraceCup (X : TopCat.{0}) (p q : ℕ) :
    Cohomology ℚ X p →ₗ[ℚ] Cohomology ℚ X q →ₗ[ℚ] Cohomology ℚ X (p + q) where
  toFun a :=
    { toFun := fun b => (cohomologyEquivDualHomology ℚ X (p + q)).symm
        { toFun := fun c => localTracePairing X p q c a b
          map_add' := by intros; simp [localTracePairing]
          map_smul' := by intros; simp [localTracePairing] }
      map_add' := by
        intros
        apply (cohomologyEquivDualHomology ℚ X (p + q)).injective
        ext c
        simp [localTracePairing]
      map_smul' := by
        intros
        apply (cohomologyEquivDualHomology ℚ X (p + q)).injective
        ext c
        simp [localTracePairing] }
  map_add' := by
    intros
    ext b
    apply (cohomologyEquivDualHomology ℚ X (p + q)).injective
    ext c
    simp [localTracePairing]
  map_smul' := by
    intros
    ext b
    apply (cohomologyEquivDualHomology ℚ X (p + q)).injective
    ext c
    simp [localTracePairing]

example (X : TopCat.{0}) (p q : ℕ) (c : Homology ℚ X (p + q))
    (a : Cohomology ℚ X p) (b : Cohomology ℚ X q) :
    orientationIntegral X (p + q) c (localTraceCup X p q a b) =
      localTracePairing X p q c a b := by
  change cohomologyEquivDualHomology ℚ X (p + q)
    ((cohomologyEquivDualHomology ℚ X (p + q)).symm _) c = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual map of point-complement pairs at a singleton fibre.
Source: Hatcher, Algebraic Topology, section 2.2, local degree, Proposition 2.30. -/
def singletonFibrePairMap {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) (y : Y)
    (hf : ∀ z, f z = y → z = x) : pointComplementPair x ⟶ pointComplementPair y :=
  TopPair.ofHom f
    (TopCat.ofHom ⟨fun z => ⟨f z.val, fun h => z.property (hf z.val h)⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩) rfl

example {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) (y : Y)
    (hf : ∀ z, f z = y → z = x) :
    (singletonFibrePairMap f x y hf).hom.right = f := rfl

end HodgeLean.Foundations.QuotientDuality
