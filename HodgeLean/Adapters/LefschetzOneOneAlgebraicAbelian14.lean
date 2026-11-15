import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian14Proofs

/-! # Singular restriction: local analytic and geometric primitives

Implications from reduced local factorization and from explicit continuous or
smooth map data. These are intermediate constructions for the critical cover
and complement filling. The global cover and cohomological endpoints require
further work. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped ContDiff
open Set Filter Topology TopologicalSpace CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- On the regular part of a factor, critical zeros are precisely intersections
with the residual factor, which cannot vanish on the whole factor germ.
Source: `bh12_no_critical_hypersurface`, the analytic product rule, and
Gunning--Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem bh14_factor_intersection (n : ℕ) (p : Fin n → ℂ)
    (f g h : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hred : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hi : IsIrreducibleAt g p) (hd : fderiv ℂ g p ≠ 0)
    (heq : f =ᶠ[𝓝 p] fun z ↦ g z * h z) :
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, g z = 0 → (f z = 0 ∧ fderiv ℂ f z = 0 ↔ h z = 0)) ∧
    ¬ (∀ᶠ z in 𝓝 p, g z = 0 → h z = 0) :=
  bh14_factor_intersection_aux n p f g h hf hg hh hred hi hd heq

/-- Approximate prescribed continuous sphere data by a globally smooth vector-valued map.
Source: `ContinuousMap.exists_restrict_eq`, coordinatewise Tietze extension, and
`Continuous.exists_contDiff_approx`. -/
theorem bh14_sphere_approximation (n k : ℕ)
    (u : (Fin (k + 1) → ℝ) → (Fin n → ℂ))
    (hu : ContinuousOn u (Metric.sphere 0 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ), ContDiff ℝ ∞ v ∧
      ∀ z ∈ Metric.sphere 0 1, dist (v z) (u z) < ε :=
  bh14_sphere_approximation_aux n k u hu ε hε

/-- Small translations avoid a countable differentiable cover when each incidence
parameter space has smaller real dimension than the target.
Source: `DifferentiableOn.dimH_image_le`, `dimH_iUnion`,
`Real.dimH_univ_eq_finrank`, and `dense_compl_of_dimH_lt_finrank`. -/
theorem bh14_small_translation (n m : ℕ)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j)) (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → 2 * d j + m < 2 * n)
    (v : (Fin m → ℝ) → (Fin n → ℂ)) (hv : ContDiff ℝ 1 v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Fin n → ℂ, ‖a‖ < ε ∧
      ∀ z ∈ Metric.closedBall (0 : Fin m → ℝ) 1,
        v z + a ∉ ⋃ j, g j '' U j :=
  bh14_small_translation_aux n m d U g hU hg hd v hv ε hε

/-- A uniform boundary tolerance permits restoring exact continuous sphere data
by a collar inside the prescribed open set.
Source: compactness of the sphere, positive distance to a closed complement,
and the radial collar construction in Hatcher, Algebraic Topology, §0 (homotopy extension). -/
theorem bh14_collar_restoration (n k : ℕ) (U : Set (Fin n → ℂ))
    (hU : IsOpen U) (u : (Fin (k + 1) → ℝ) → (Fin n → ℂ))
    (hu : ContinuousOn u (Metric.sphere 0 1)) (huU : MapsTo u (Metric.sphere 0 1) U) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn v (Metric.closedBall 0 1) →
        MapsTo v (Metric.closedBall 0 1) U →
        (∀ z ∈ Metric.sphere 0 1, dist (v z) (u z) < ε) →
        ∃ w : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn w (Metric.closedBall 0 1) ∧
          MapsTo w (Metric.closedBall 0 1) U ∧
          ∀ z ∈ Metric.sphere 0 1, w z = u z :=
  bh14_collar_restoration_aux n k U hU u hu huU

/-- The ball and simplex models have a homeomorphism carrying sphere to boundary.
Source: `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`, applied
in affine coordinates on the simplex, and Hatcher, Algebraic Topology, §2.1. -/
theorem bh14_simplex_ball (k : ℕ) :
    ∃ e : (Metric.closedBall (0 : Fin (k + 1) → ℝ) 1) ≃ₜ
      (Convexity.StdSimplex ℝ (Fin (k + 2))),
      ∀ z, (z.1 ∈ Metric.sphere (0 : Fin (k + 1) → ℝ) 1 ↔
        ∃ i : Fin (k + 2), (e z).weights i = 0) :=
  bh14_simplex_ball_aux k

/-- A countable cover of real codimension at least four permits exact sphere
fillings in its open complement in dimensions zero through two.
Source: `bh14_sphere_approximation`, `bh14_small_translation`, and
`bh14_collar_restoration`. -/
theorem bh14_cover_sphere_filling (n : ℕ) (O : Set (Fin n → ℂ))
    (hO : IsOpen O) (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j)) (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j)
    (k : ℕ) (hk : k ≤ 2)
    (u : (Fin (k + 1) → ℝ) → (Fin n → ℂ))
    (hu : ContinuousOn u (Metric.sphere 0 1)) (huO : MapsTo u (Metric.sphere 0 1) O) :
    ∃ w : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
      ContinuousOn w (Metric.closedBall 0 1) ∧ MapsTo w (Metric.closedBall 0 1) O ∧
      ∀ z ∈ Metric.sphere 0 1, w z = u z :=
  bh14_cover_sphere_filling_aux n O hO d U g hU hg hd hcover k hk u hu huO

/-- Sphere filling supplies an extension of the entire compatible simplex boundary.
This is a geometric intermediate for building cones on singular simplices.
Source: `bh14_simplex_ball` and Hatcher, Algebraic Topology, §2.1 (singular simplices). -/
theorem bh14_simplex_extension (n : ℕ) (U : Opens (Fin n → ℂ))
    (hne : (U : Set (Fin n → ℂ)).Nonempty) (k : ℕ) (hk : k ≤ 2)
    (hfill : ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
      ContinuousOn u (Metric.sphere 0 1) →
      MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
      ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn v (Metric.closedBall 0 1) ∧
        MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
        ∀ z ∈ Metric.sphere 0 1, v z = u z)
    (u : C({x : Convexity.StdSimplex ℝ (Fin (k + 2)) | ∃ i, x.weights i = 0}, U)) :
    ∃ v : C(Convexity.StdSimplex ℝ (Fin (k + 2)), U), ∀ z, v z.1 = u z :=
  bh14_simplex_extension_aux n U hne k hk hfill u

end HodgeLean.Adapters
