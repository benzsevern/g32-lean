import HodgeLean.Foundations.Program.HurwitzFamilyProofs

/-! # B6-1: normalized configurations and fibrewise Hurwitz covers

Implication from a finite-group Nielsen tuple to properties of its selected covers over
an open ten-dimensional configuration slice. No holomorphic total family, Prym variation,
period map or Schlesinger comparison is asserted. HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The normalized collision-free configuration slice is open.
Source: Finite intersections of complements of Hausdorff diagonals; `b6_branch`. -/
theorem b6_chart_open  :
    IsOpen b6_chart :=
  b6_chart_open_aux 

example  :
    IsOpen b6_chart :=
  b6_chart_open 

/-- The ten integers from two through eleven give a point of the slice.
Source: `b6_base` and the normalized sphere coordinates. -/
theorem b6_base_mem  :
    b6_base ∈ b6_chart :=
  b6_base_mem_aux 

example  :
    b6_base ∈ b6_chart :=
  b6_base_mem 

/-- Coordinates are distinct and avoid the two finite fixed points.
Source: Forster, *Lectures on Riemann Surfaces*, §1.3; ordered configurations. -/
theorem b6_chart_coordinates (t : Fin 10 → ℂ) :
    t ∈ b6_chart ↔ Function.Injective t ∧ ∀ i, t i ≠ 0 ∧ t i ≠ 1 :=
  b6_chart_coordinates_aux t

example (t : Fin 10 → ℂ) :
    t ∈ b6_chart ↔ Function.Injective t ∧ ∀ i, t i ≠ 0 ∧ t i ≠ 1 :=
  b6_chart_coordinates t

/-- Each marked point depends continuously on the ambient coordinates.
Source: Continuity of coordinate evaluation and the sphere inclusion. -/
theorem b6_branch_continuous (j : Fin 13) :
    Continuous (fun t : (Fin 10 → ℂ) ↦ b6_branch t j) :=
  b6_branch_continuous_aux j

example (j : Fin 13) :
    Continuous (fun t : (Fin 10 → ℂ) ↦ b6_branch t j) :=
  b6_branch_continuous j

/-- Every parameter has a point in its selected covering fibre.
Source: `b4_riemannExistence`; Forster, Theorem 8.4. -/
theorem b6_projection_surjective (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) :
    Function.Surjective (b6_projection G g hg) :=
  b6_projection_surjective_aux G g hg

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) :
    Function.Surjective (b6_projection G g hg) :=
  b6_projection_surjective G g hg

/-- The selected covering map on each fibre is holomorphic.
Source: `b4_riemannExistence`; Forster, Theorem 8.4. -/
theorem b6_fiber_holomorphic (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b6_coverMap G g hg t) :=
  b6_fiber_holomorphic_aux G g hg t

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b6_coverMap G g hg t) :=
  b6_fiber_holomorphic G g hg t

/-- The selected fibre retains its Galois and local rotation properties.
Source: `b4_riemannExistence`; Völklein, *Groups as Galois Groups*, Theorem 2.13. -/
theorem b6_fiber_geometry (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    b4_IsGaloisCover G (b6_coverMap G g hg t) ∧
      (∀ x, b6_coverMap G g hg t x ∉ Set.range (b6_branch t.val) →
        MulAction.stabilizer G x = ⊥) ∧
      ∀ j, ∃ x, b6_coverMap G g hg t x = b6_branch t.val j ∧
        b4_IsRotGen ℂ x (g j) :=
  b6_fiber_geometry_aux G g hg t

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    b4_IsGaloisCover G (b6_coverMap G g hg t) ∧
      (∀ x, b6_coverMap G g hg t x ∉ Set.range (b6_branch t.val) →
        MulAction.stabilizer G x = ⊥) ∧
      ∀ j, ∃ x, b6_coverMap G g hg t x = b6_branch t.val j ∧
        b4_IsRotGen ℂ x (g j) :=
  b6_fiber_geometry G g hg t

/-- The group action on each selected surface is holomorphic.
Source: `b4_riemannExistence`; Forster, Theorem 8.4. -/
theorem b6_fiber_action_holomorphic (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    ∀ a : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : b6_Cover G g hg t ↦ a • x) :=
  b6_fiber_action_holomorphic_aux G g hg t

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g)
    (t : b6_chart) :
    ∀ a : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : b6_Cover G g hg t ↦ a • x) :=
  b6_fiber_action_holomorphic G g hg t

end HodgeLean.Foundations.Program
