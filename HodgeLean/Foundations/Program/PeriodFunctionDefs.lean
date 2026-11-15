import HodgeLean.Foundations.Program.PeriodMarking
import HodgeLean.Papers.G32DominanceDefs

/-! # B6-4c: the period function (definitions)

The period function of a family of filtrations of a lattice `M`, read in the fixed chart
`b60_F` of `ℂ ⊗ ℤ[ω]⁶` after a rational marking `m : ℚ ⊗ M ≃ ℚ ⊗ ℤ[ω]⁶`: at a parameter
`t ∈ V` it is the coordinate `b64_coordOf` of the marked filtration, and it is `0` off `V`.
The geometric period function takes for the family the transported period filtrations
`b63e_transportedF … s t` of B6-3e on the saturated singular lattice at one fixed parameter
`s`. No marking, frame or chart membership is selected from a statement.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- **The marked filtration**: the image of the filtration at `t` under the complexified
rational marking.
Source: Bourbaki, *Algebra*, Ch. II, §5, extension of scalars; `b64b_complexMarking`. -/
def b64c_markedF (M : Type*) [AddCommGroup M]
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M)) (t : Fin 10 → ℂ) :
    Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice) :=
  (G t).map (b64b_complexMarking M m).toLinearMap

/-- With the identity marking of the fixed lattice, the marked filtration is the filtration.
A direct computation, used by the instance checks.
Source: `b64b_complexMarking`; Mathlib `LinearEquiv.baseChange_tmul`. -/
theorem b64c_markedF_refl (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (t : Fin 10 → ℂ) :
    b64c_markedF b60_Lattice (LinearEquiv.refl ℚ _) G t = G t := by
  have h : b64b_complexMarking b60_Lattice (LinearEquiv.refl ℚ _) =
      LinearEquiv.refl ℂ _ := by
    apply LinearEquiv.toLinearMap_injective
    ext c
    simp [b64b_complexMarking, LinearEquiv.baseChange_tmul]
  rw [b64c_markedF, h]
  exact Submodule.map_id (G t)

example (z : Fin 9 → ℂ) :
    b64c_markedF b60_Lattice (LinearEquiv.refl ℚ _) (fun _ => b60_F z) 0 = b60_F z :=
  b64c_markedF_refl _ 0

open Classical in
/-- **The period function** of a family of filtrations over `V`: the chart coordinate of the
marked filtration at `t ∈ V`, and `0` off `V`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1 (period maps in graph coordinates); van Geemen, LNM 1594, §5.10; `b64_coordOf`. -/
def b64c_period (M : Type*) [AddCommGroup M]
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) (V : Set (Fin 10 → ℂ))
    (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M)) : (Fin 10 → ℂ) → Fin 9 → ℂ :=
  fun t => if t ∈ V then b64_coordOf (b64c_markedF M m G t) else 0

example (M : Type*) [AddCommGroup M] (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (t : Fin 10 → ℂ) (ht : t ∈ V) :
    b64c_period M m V G t = b64_coordOf (b64c_markedF M m G t) := by
  simp [b64c_period, ht]

example (M : Type*) [AddCommGroup M] (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (t : Fin 10 → ℂ) (ht : t ∉ V) :
    b64c_period M m V G t = 0 := by
  simp [b64c_period, ht]

open Classical in
/-- **The transported family**: the period filtration of the fibre at `u ∈ V`, pulled back to
the complexified saturated singular lattice at the fixed parameter `s`; `⊥` off `V`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, §1;
`b63e_transportedF`. -/
def b64c_transportedFamily (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s : V) (u : Fin 10 → ℂ) :
    Submodule ℂ (ℂ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) :=
  if h : u ∈ V then b63e_transportedF b C hC V hV P s ⟨u, h⟩ else ⊥

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s t : V) :
    b64c_transportedFamily b C hC V hV P s t.val = b63e_transportedF b C hC V hV P s t := by
  simp [b64c_transportedFamily]

/-- **The geometric period function**: the period function of the transported family, marked
by a rational marking of the saturated singular lattice at `s`.
Source: G32 v0.16, first paragraph of the proof of Theorem 7.2 (the period map `Φ : Δ → 𝓗₃`);
Griffiths, *Periods of integrals on algebraic manifolds I*, §1. -/
def b64c_geomPeriod (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s : V)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    (Fin 10 → ℂ) → Fin 9 → ℂ :=
  b64c_period (b63l_parameterLattice b C hC V hV s) m V
    (b64c_transportedFamily b C hC V hV P s)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s t : V)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    b64c_geomPeriod b C hC V hV P s m t.val =
      b64_coordOf ((b63e_transportedF b C hC V hV P s t).map
        (b64b_complexMarking _ m).toLinearMap) := by
  simp [b64c_geomPeriod, b64c_period, b64c_markedF, b64c_transportedFamily]

end HodgeLean.Foundations.Program
