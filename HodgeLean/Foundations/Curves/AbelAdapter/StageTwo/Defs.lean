import HodgeLean.Foundations.Curves.AbelAdapter.Basic
import HodgeLean.Foundations.IntegralHomology.StageThree.Basic
import HodgeLean.Adapters.AbelianHomPullback
import HodgeLean.Adapters.HolomorphicFormValuesDefs
import HodgeLean.Adapters.CycleClassDivisorPowers

/-! # Integral and differential constructions for the retained Abel map

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program HodgeLean.Adapters
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- The B5 group structure on the retained model.
Source: Birkenhake–Lange, Theorem 4.5.1; b5_groupObj.
HC no distance; AV milestone no distance. -/
instance modelGroup (h : Module.finrank ℂ E = 1) : GrpObj (model (C := C) h) := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  exact b5_groupObj _ _ _ _ (b3_intersectionForm_isRiemannForm h _
    (b3_exists_intersectionForm (C := C) h).choose_spec)

/-- Integral geometry of the retained model.
Source: Birkenhake–Lange, Theorem 4.5.1; b5_integral.
HC no distance; AV milestone no distance. -/
instance modelIntegral (h : Module.finrank ℂ E = 1) : IsIntegral (model (C := C) h).left :=
  (projectiveGroup h).2.2.1

/-- Smooth geometry of the retained model.
Source: Birkenhake–Lange, Theorem 4.5.1; b5_smooth.
HC no distance; AV milestone no distance. -/
instance modelSmooth (h : Module.finrank ℂ E = 1) : Smooth (model (C := C) h).hom :=
  (projectiveGroup h).1

/-- Projective geometry of the retained model.
Source: Birkenhake–Lange, Theorem 4.5.1; b5_projective.
HC no distance; AV milestone no distance. -/
instance modelProjective (h : Module.finrank ℂ E = 1) : IsProjective (model (C := C) h).hom :=
  (projectiveGroup h).2.1

example (h : Module.finrank ℂ E = 1) : GrpObj (model (C := C) h) := inferInstance
example (h : Module.finrank ℂ E = 1) : IsIntegral (model (C := C) h).left := inferInstance
example (h : Module.finrank ℂ E = 1) : Smooth (model (C := C) h).hom := inferInstance
example (h : Module.finrank ℂ E = 1) : IsProjective (model (C := C) h).hom := inferInstance

/-- The actual continuous point map of a scheme morphism.
Source: Serre, GAGA, §2; Point.continuous_map.
HC no distance; AV milestone no distance. -/
def pointMap {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) :
    TopCat.of (ComplexPoint X) ⟶ TopCat.of (ComplexPoint Y) :=
  TopCat.ofHom ⟨Point.map f, Point.continuous_map f⟩

example {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (x : ComplexPoint X) :
    pointMap f x = Point.map f x := rfl

/-- The integral cycle of an actual smooth loop, followed by the torsion quotient.
Source: Hatcher, Algebraic Topology, §2.1; b3Rest2_circ.
HC no distance; AV milestone no distance. -/
def loopClass (c : b3_SmoothLoop E C) : IntegralHomology.Lattice (TopCat.of C) :=
  Submodule.Quotient.mk ((IntegralHomology.ZChains (TopCat.of C)).homologyπ 1
    (((IntegralHomology.ZChains (TopCat.of C)).sc 1).moduleCatCyclesIso.inv
      (HodgeLean.Adapters.loopCycle ℤ (b3Rest2_circ c))))

example (c : b3_SmoothLoop E C) :
    loopClass c + (0 : IntegralHomology.Lattice (TopCat.of C)) = loopClass c := add_zero _

/-- Form coordinates on the universal cover of the original period torus.
Source: Forster, §21; b3Rest2_ellV.
HC no distance; AV milestone no distance. -/
def periodCovector (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  exact b3Rest2_ellV θ

example (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    periodCovector h θ 0 = 0 := map_zero _

/-- Translation by a specified complex point on the actual group scheme.
Source: Mumford, Abelian Varieties, §1; GrpObj.mulRight.
HC no distance; AV milestone no distance. -/
def translation (A : Over (Spec ↧ℂ)) [GrpObj A] (a : ComplexPoint A) : A ≅ A :=
  GrpObj.mulRight a

example (A : Over (Spec ↧ℂ)) [GrpObj A] (a : ComplexPoint A) :
    (translation A a).hom ≫ (translation A a).inv = 𝟙 A := Iso.hom_inv_id _

/-- Center a scheme morphism at its specified source point.
Source: Birkenhake–Lange, §11.4.
HC no distance; AV milestone no distance. -/
def centered {X A : Over (Spec ↧ℂ)} [GrpObj A]
    (f : X ⟶ A) (p : ComplexPoint X) : X ⟶ A :=
  f ≫ (translation A (Point.map f p)⁻¹).hom

example {X A : Over (Spec ↧ℂ)} [GrpObj A] (f : X ⟶ A) (p : ComplexPoint X) :
    centered f p = f ≫ (translation A (Point.map f p)⁻¹).hom := rfl

/-- Read a scheme one-form in its actual complex-point tangent chart.
Source: Griffiths–Harris, chapter 0 §2; globalOneFormCovector.
HC no distance; AV milestone no distance. -/
def schemeForm (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) :
    TangentBundle 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) (ComplexPoint X) → ℂ :=
  fun v ↦ globalOneFormCovector X (TopologicalSpace.dim X.left) θ v.1 v.2

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (x : ComplexPoint X) :
    schemeForm X θ ⟨x, 0⟩ = 0 := map_zero _

/-- The B5 integral period map with the retained theta normalization.
Source: Birkenhake–Lange, §§1.1–1.2; b5_periodMap.
HC no distance; AV milestone no distance. -/
def modelPeriod (h : Module.finrank ℂ E = 1) :
    b3_periodLattice E C →ₗ[ℤ] abelianPeriodLattice (model (C := C) h) := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  exact (b5_periodMap _ _ _ _ (b3_intersectionForm_isRiemannForm h _
    (b3_exists_intersectionForm (C := C) h).choose_spec)).toIntLinearMap

example (h : Module.finrank ℂ E = 1) : modelPeriod (C := C) h 0 = 0 := map_zero _

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
