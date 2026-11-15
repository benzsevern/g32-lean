import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ThirdKindLocalSolutions
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.AmbientScalarPrimitive
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.LogarithmicDivisor
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.Defs

/-! # Period coordinates for Abel's theorem

All integrals use the retained B3 paths and the actual divisor complement.
HC no distance; AV milestone no distance.
-/
noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Integration along an actual B3 loop, also for meromorphic forms regular on its image.
Source: Farkas–Kra, Riemann Surfaces, III.6.
HC no distance; AV milestone no distance.
-/
def loopIntegral (γ : b3_SmoothLoop E C)
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) : ℂ := b3_pathIntegral E C γ.val w

example (γ : b3_SmoothLoop E C) : loopIntegral γ 0 = 0 := by
  simp [loopIntegral, b3_pathIntegral]

/-- The additive integral of a finite divisor along specified paths.
Source: Miranda, Algebraic Curves and Riemann Surfaces, VIII.2.
HC no distance; AV milestone no distance.
-/
def divisorIntegral (D : C →₀ ℤ) (paths : C → ℝ → C)
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) : ℂ :=
  D.sum (fun x n => (n : ℂ) * b3_pathIntegral E C (paths x) w)

example (x : C) (paths : C → ℝ → C) (w : TangentBundle 𝓘(ℂ, E) C → ℂ) :
    divisorIntegral (Finsupp.single x (1 : ℤ)) paths w =
      b3_pathIntegral E C (paths x) w := by
  classical
  simp [divisorIntegral]

/-- Exponentiated path integration with the unscaled B3 convention.
Source: Griffiths–Harris, Principles of Algebraic Geometry, 2.2.
HC no distance; AV milestone no distance.
-/
def exponentialIntegral (γ : ℝ → C)
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) : ℂ :=
  Complex.exp (b3_pathIntegral E C γ w)

example (γ : ℝ → C) : exponentialIntegral γ (0 : TangentBundle 𝓘(ℂ, E) C → ℂ) = 1 := by
  simp [exponentialIntegral, b3_pathIntegral]

/-- A scalar function written in the actual centered curve coordinate.
Source: Miranda, Algebraic Curves and Riemann Surfaces, VIII.2.
HC no distance; AV milestone no distance.
-/
def centeredScalar (h : Module.finrank ℂ E = 1) (f : C → ℂ) (x : C) : ℂ → ℂ :=
  fun z => f ((extChartAt 𝓘(ℂ, E) x).symm
    (extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h z))

example (h : Module.finrank ℂ E = 1) (x : C) :
    centeredScalar h (fun _ : C => (2 : ℂ)) x 0 = 2 := rfl

/-- A normalized symplectic period basis on the retained curve, avoiding the divisor.
The integral basis is in B3's period lattice, rather than a chosen coordinate lattice.
Source: Farkas–Kra, Riemann Surfaces, III.2 and III.6.
HC no distance; AV milestone no distance.
-/
structure PeriodFrame [FiniteDimensional ℂ E] [T2Space C] (D : C →₀ ℤ) where
  genus : ℕ
  a : Fin genus → b3_SmoothLoop E C
  b : Fin genus → b3_SmoothLoop E C
  latticeBasis : Module.Basis (Fin genus ⊕ Fin genus) ℤ (b3_periodLattice E C)
  forms : Module.Basis (Fin genus) ℂ (b3_HolForm E C)
  a_basis : ∀ i, latticeBasis (Sum.inl i) = b3_latticePeriod E C (a i)
  b_basis : ∀ i, latticeBasis (Sum.inr i) = b3_latticePeriod E C (b i)
  a_avoids : ∀ i t, (a i).val t ∉ D.support
  b_avoids : ∀ i t, (b i).val t ∉ D.support
  intersection : LinearMap.BilinForm ℤ (b3_periodLattice E C)
  intersection_spec : b3_IsIntersectionForm E intersection
  aa : ∀ i j, intersection (latticeBasis (Sum.inl i)) (latticeBasis (Sum.inl j)) = 0
  bb : ∀ i j, intersection (latticeBasis (Sum.inr i)) (latticeBasis (Sum.inr j)) = 0
  ab : ∀ i j, intersection (latticeBasis (Sum.inl i)) (latticeBasis (Sum.inr j)) =
    if i = j then 1 else 0
  normalized : ∀ i j, loopIntegral (a i) (forms j) = if i = j then 1 else 0

example [FiniteDimensional ℂ E] [T2Space C] (D : C →₀ ℤ) (F : PeriodFrame (E := E) D) (i : Fin F.genus) :
    loopIntegral (F.a i) (F.forms i) = 1 := by
  simpa using F.normalized i i

end HodgeLean.Foundations.Curves.AbelTheorem
