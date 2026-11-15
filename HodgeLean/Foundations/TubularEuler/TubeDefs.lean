import HodgeLean.Foundations.BundleThom.ImmersionDefs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Smooth oriented tubes on the actual dual conormal

Local real smoothness is measured in holomorphic scheme charts and complex
linear normal charts. The transverse derivative is complex linear and
invertible. No supported class occurs in the geometric data.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

/-- A radial geometric tube on a fixed bundle, with its exact zero-support equation.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24.
HC no distance; AV milestone no distance. -/
structure RadialTube {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    {X : Type} [TopologicalSpace X] (zeroMap : C(B, X)) (Z : Set X) where
  source : Opens (TotalSpace (Fin k → ℂ) E)
  target : Opens X
  map : source ≃ₜ target
  contains_zero : ∀ x, zeroSection (Fin k → ℂ) E x ∈ source
  radial : ∀ z : source, ∀ a : ℝ, a ∈ Set.Icc 0 1 →
    (⟨z.1.proj, (a : ℂ) • z.1.2⟩ : TotalSpace (Fin k → ℂ) E) ∈ source
  map_zero : ∀ x hx, (map ⟨zeroSection (Fin k → ℂ) E x, hx⟩).val = zeroMap x
  support : ∀ z : source, (map z).val ∈ Z ↔ z.val.2 = 0

example {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    {X : Type} [TopologicalSpace X] (zeroMap : C(B, X)) (Z : Set X)
    (t : RadialTube k E zeroMap Z) (z : t.source) (hz : z.val.2 ≠ 0) :
    (t.map z).val ∉ Z := fun h => hz ((t.support z).mp h)

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)

include ι in
private theorem qFiniteType : LocallyOfFiniteType Q.hom := by
  rw [← Over.w ι]
  infer_instance
include ι in
private theorem qQuasiCompact : QuasiCompact Q.hom := by
  rw [← Over.w ι]
  infer_instance
include ι in
private theorem qSeparated : IsSeparated Q.hom := by
  rw [← Over.w ι]
  infer_instance
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Geometric neighbourhoods of the actual zero section and immersion.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24;
Bott–Tu, Differential Forms in Algebraic Topology, §6.
HC no distance; AV milestone no distance. -/
structure NormalTube extends RadialTube k (i1_normalFibre j)
    (Point.continuousMap (i1_smoothLift ι v j hj))
    (Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W) ⁻¹'
      a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)) where
  ambient : OpenPartialHomeomorph
    (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) (ComplexPoint W)
  ambient_source : ambient.source = source
  ambient_map : ∀ z : source,
    ambient z.1 = i1_tubularAmbientMap v j k source target map z

/-- Coordinates of the actual tubular map in a base chart and a normal frame.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24.
HC no distance; AV milestone no distance. -/
def tubeCoordinates (t : NormalTube ι k v j hj)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ))) :=
  ((e.toOpenPartialHomeomorph.trans
    (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm.trans t.ambient).trans a

/-- Smooth local charts with the complex transverse orientation on the actual tube.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24;
Milnor–Stasheff, Characteristic Classes, §§10–11.
HC no distance; AV milestone no distance. -/
structure SmoothNormalTube extends NormalTube ι k v j hj where
  localCharts :
    letI := qFiniteType ι
    letI := qQuasiCompact ι
    letI := qSeparated ι
    ∀ z ∈ toNormalTube.source,
    ∃ (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
      (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
      (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ))),
      a3b4_IsHolChart Q.hom (b.trans
        ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)) ∧
      e.IsLinear ℂ ∧ a3b4_IsHolChart W.hom a ∧
      z.proj ∈ b.source ∧ z ∈ e.source ∧ toNormalTube.ambient z ∈ a.source ∧
      (∀ y ∈ a.source, y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔
        (a y).2 = 0) ∧
      let c := tubeCoordinates ι k v j hj toNormalTube b e a
      (b z.proj, (0 : Fin k → ℂ)) ∈ c.source ∧
      ContDiffOn ℝ ⊤ c c.source ∧ ContDiffOn ℝ ⊤ c.symm c.target ∧
      ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
        HasFDerivAt (fun w : Fin k → ℂ => (c (b z.proj, w)).2)
          A.toContinuousLinearMap 0

/-- A normal map with local smooth inverses along the zero section.
The domain and the local inverses precede any global injectivity choice.
Source: Lee, Introduction to Smooth Manifolds, second edition, proof of Theorem 6.24.
HC no distance; AV milestone no distance. -/
structure LocalNormalMap where
  domain : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j))
  map : C(domain, ComplexPoint (Over.mk (v ≫ W.hom)))
  contains_zero : ∀ x, zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ domain
  map_zero : ∀ x hx,
    map ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, hx⟩ =
      Point.map (i1_smoothLift ι v j hj) x
  localInverse : ComplexPoint Q → OpenPartialHomeomorph
    (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) (ComplexPoint W)
  local_zero : ∀ x, zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈
    (localInverse x).source
  local_domain : ∀ x, (localInverse x).source ⊆ domain
  local_map : ∀ x z hz, (localInverse x) z =
    Point.map ((Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)) (map ⟨z, local_domain x hz⟩)
  local_support : ∀ x z, z ∈ (localInverse x).source →
    ((localInverse x) z ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ z.2 = 0)
  localCharts :
    letI := qFiniteType ι
    letI := qQuasiCompact ι
    letI := qSeparated ι
    ∀ x, ∀ z ∈ (localInverse x).source,
    ∃ (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
      (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
      (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ))),
      a3b4_IsHolChart Q.hom (b.trans
        ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)) ∧
      e.IsLinear ℂ ∧ a3b4_IsHolChart W.hom a ∧
      z.proj ∈ b.source ∧ z ∈ e.source ∧ (localInverse x) z ∈ a.source ∧
      (∀ y ∈ a.source, y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔
        (a y).2 = 0) ∧
      let c := ((e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm.trans (localInverse x)).trans a
      (b z.proj, (0 : Fin k → ℂ)) ∈ c.source ∧
      ContDiffOn ℝ ⊤ c c.source ∧ ContDiffOn ℝ ⊤ c.symm c.target ∧
      ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
        HasFDerivAt (fun w : Fin k → ℂ => (c (b z.proj, w)).2)
          A.toContinuousLinearMap 0

example (n : LocalNormalMap ι k v j hj) (x : ComplexPoint Q) :
    zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ (n.localInverse x).source :=
  n.local_zero x

example (n : LocalNormalMap ι k v j hj) (x : ComplexPoint Q)
    (z : TotalSpace (Fin k → ℂ) (i1_normalFibre j))
    (hz : z ∈ (n.localInverse x).source) (hn : z.2 ≠ 0) :
    n.localInverse x z ∉ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) :=
  fun h => hn ((n.local_support x z hz).mp h)

example (t : NormalTube ι k v j hj) (x : ComplexPoint Q) :
    (t.map ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, t.contains_zero x⟩).1 =
      Point.map (i1_smoothLift ι v j hj) x := t.map_zero x _

example (t : NormalTube ι k v j hj) (z : t.source) :
    t.ambient z.1 = i1_tubularAmbientMap v j k t.source t.target t.map z := t.ambient_map z

example (t : SmoothNormalTube ι k v j hj) (x : ComplexPoint Q) :
    zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ t.source := t.contains_zero x

example (t : NormalTube ι k v j hj)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ)))
    (w : (Fin k → ℂ) × (Fin k → ℂ)) :
    tubeCoordinates ι k v j hj t b e a w =
      a (t.ambient ((e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm w)) := rfl

end HodgeLean.Foundations.TubularEuler
