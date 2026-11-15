import HodgeLean.Foundations.Program.RelativeFrameChartsDefs

/-! # Restated relative frames: definitions for D2–D4
The family of transported primitive filtrations over the whole parameter space, zero off the
parameter set, in the shape that the frame premise of the B6-4c period function uses.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

/-- The transported primitive filtrations `F_{s,u}` as a family over `ℂ¹⁰`: at `u ∈ V` the period
filtration of the fibre at `u` pulled back to `ℂ ⊗ Λ_s` (`b63e_transportedF`), and `⊥` off `V`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1; `b63e_transportedF`. -/
def rf6_transportedFamily (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s : V) (u : Fin 10 → ℂ) :
    Submodule ℂ (ℂ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) :=
  haveI := Classical.dec (u ∈ V)
  if hu : u ∈ V then b63e_transportedF b C hC V hV P s ⟨u, hu⟩ else ⊥

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s t : V) :
    rf6_transportedFamily b C hC V hV P s t.val = b63e_transportedF b C hC V hV P s t := by
  simp [rf6_transportedFamily, t.property]

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s : V) (u : Fin 10 → ℂ)
    (hu : u ∉ V) :
    rf6_transportedFamily b C hC V hV P s u = ⊥ := by
  simp [rf6_transportedFamily, hu]

end HodgeLean.Foundations.Program
