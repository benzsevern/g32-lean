import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianDefs
import HodgeLean.Adapters.RiemannFormHermitian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Projective local lifts, curvature and lattice averaging

The curvature is computed from logarithmic squared norms of homogeneous lifts.
The average is an actual integral over the lattice-coordinate unit cube.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open Filter Set Topology MeasureTheory
namespace HodgeLean.Adapters

/-- Local homogeneous representatives of a lattice-periodic projective immersion.
The derivative condition means immersion modulo the radial line, not a positive form.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Chapter 0, projective embeddings
and the Fubini--Study metric. -/
structure bh8_ProjectiveAtlas (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ)) where
  N : ℕ
  U : (Fin n → ℂ) → Set (Fin n → ℂ)
  s : (Fin n → ℂ) → (Fin n → ℂ) → (Fin (N + 1) → ℂ)
  open_U : ∀ p, IsOpen (U p)
  anchor : ∀ p, p ∈ U p
  analytic : ∀ p, AnalyticOnNhd ℂ (s p) (U p)
  nonzero : ∀ p z, z ∈ U p → s p z ≠ 0
  immersion : ∀ p z, z ∈ U p → ∀ (v : Fin n → ℂ) (c : ℂ),
    fderiv ℂ (s p) z v = c • s p z → v = 0
  transition : ∀ (l : Λ) p q z, z ∈ U p → z + l ∈ U q →
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, s q (w + l) = u w • s p w

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ)) (A : bh8_ProjectiveAtlas n Λ)
    (p : Fin n → ℂ) : p ∈ A.U p := A.anchor p

/-- The fixed real-linear complex structure.
Source: multiplication by i on the complex tangent space. -/
def bh8_complexStructure (n : ℕ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  (Complex.I • ContinuousLinearMap.id ℂ (Fin n → ℂ)).restrictScalars ℝ

example : bh8_complexStructure 1 (fun _ ↦ 1) = fun _ ↦ Complex.I := by
  ext i
  simp [bh8_complexStructure]

/-- The local logarithmic squared-norm potential of a homogeneous lift.
Source: Griffiths--Harris, Chapter 0, Fubini--Study form. -/
def bh8_potential (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (p z : Fin n → ℂ) : ℝ :=
  Real.log (∑ j, Complex.normSq (A.s p z j))

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ)) (A : bh8_ProjectiveAtlas n Λ)
    (p z : Fin n → ℂ) : bh8_potential n Λ A p z =
      Real.log (∑ j, Complex.normSq (A.s p z j)) := rfl

/-- The normalized real curvature d d-c log of the squared norm, with positive complex orientation.
The chart anchored at the evaluation point is used; transition invariance is a theorem obligation.
Source: Griffiths--Harris, Chapter 0, c1(O(1)) = (i / 2π) ∂∂bar log norm squared. -/
def bh8_curvature (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (A : bh8_ProjectiveAtlas n Λ) (z : Fin n → ℂ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ :=
  let H := fderiv ℝ (fderiv ℝ (bh8_potential n Λ A z)) z
  let T := H.flip.comp (bh8_complexStructure n)
  (1 / (4 * Real.pi)) • (T - T.flip)

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ)) (A : bh8_ProjectiveAtlas n Λ)
    (z v : Fin n → ℂ) : bh8_curvature n Λ A z v v = 0 := by
  simp [bh8_curvature]

/-- Integrate a two-form on the actual affine period parallelogram.
Source: Birkenhake--Lange, section 1.3, periods of differential forms. -/
def bh8_surfacePeriod (n : ℕ)
    (ω : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (z l m : Fin n → ℂ) : ℝ :=
  ∫ t in Icc (0 : Fin 2 → ℝ) 1, ω (z + t 0 • l + t 1 • m) l m

example (n : ℕ) (z l m : Fin n → ℂ) :
    bh8_surfacePeriod n (fun _ ↦ 0) z l m = 0 := by
  simp [bh8_surfacePeriod]

/-- Translation average over the specified lattice-coordinate cube, of volume one.
Source: Birkenhake--Lange, section 4.3, invariant representatives on a complex torus. -/
def bh8_average (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (b : Module.Basis (Fin (2 * n)) ℤ Λ)
    (ω : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ :=
  ∫ t in Icc (0 : Fin (2 * n) → ℝ) 1, ω (∑ j, t j • (b j : Fin n → ℂ))

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (b : Module.Basis (Fin (2 * n)) ℤ Λ) : bh8_average n Λ b (fun _ ↦ 0) = 0 := by
  simp [bh8_average]

/-- Forget continuity in both slots of a continuous real bilinear form.
Source: the forgetful map from continuous linear maps to linear maps. -/
def bh8_bilinear (n : ℕ)
    (B : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ where
  toFun v := (B v).toLinearMap
  map_add' v w := by apply LinearMap.ext; intro x; exact congrArg (fun T ↦ T x) (map_add B v w)
  map_smul' r v := by apply LinearMap.ext; intro x; exact congrArg (fun T ↦ T x) (map_smul B r v)

example (n : ℕ) (B : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
    (v w : Fin n → ℂ) : bh8_bilinear n B v w = B v w := rfl

/-- The integral restriction of a real bilinear form, computed by integer floor.
Source: Birkenhake--Lange, section 1.3, integral alternating forms on a lattice. -/
def bh8_integralRestriction (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hi : ∀ l m : Λ, ∃ k : ℤ, B l m = k) : Λ →+ Λ →+ ℤ where
  toFun l :=
    { toFun := fun m ↦ ⌊B l m⌋
      map_zero' := by simp
      map_add' := by
        intro m k
        obtain ⟨a, ha⟩ := hi l m
        obtain ⟨b, hb⟩ := hi l k
        simp only [Submodule.coe_add, map_add, ha, hb]
        rw [← Int.cast_add, Int.floor_intCast, Int.floor_intCast, Int.floor_intCast] }
  map_zero' := by ext m; simp
  map_add' := by
    intro l k
    ext m
    obtain ⟨a, ha⟩ := hi l m
    obtain ⟨b, hb⟩ := hi k m
    change ⌊B (l + k) m⌋ = ⌊B l m⌋ + ⌊B k m⌋
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply, ha, hb]
    rw [← Int.cast_add, Int.floor_intCast, Int.floor_intCast, Int.floor_intCast]

example (n : ℕ) (Λ : Submodule ℤ (Fin n → ℂ)) (l m : Λ) :
    bh8_integralRestriction n Λ 0 (fun _ _ ↦ ⟨0, by simp⟩) l m = 0 := by
  simp [bh8_integralRestriction]

end HodgeLean.Adapters
