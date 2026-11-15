import HodgeLean.Foundations.ChowTheorem2Proofs

/-! # Standard-chart cone comparison: frozen specification

An implication from analytic normalized slices and nonzero scalar stability to
finite local analytic equations on each nonzero coordinate patch. This is the
coordinate part of the projective comparison. Vertex extension, quotient/scheme
chart compatibility, and the scheme closed carrier remain separate work.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations
open Set

/-- Analytic equations on a normalized standard slice lift to the cone off its vertex.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
standard affine coordinates in the cone proof of Chow's theorem. -/
theorem chow2_chart_cone (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (i : Fin (n + 1))
    (hslice : IsClosedAnalytic (Fin n → ℂ)
      {w | i.insertNth (1 : ℂ) w ∈ C})
    (x : Fin (n + 1) → ℂ) (hx : x ∈ C) (hxi : x i ≠ 0) :
    ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z i ≠ 0} ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0) :=
  chow2_chart_cone_aux n C hscale i hslice x hx hxi

/-- The cone over the unique point of projective zero-space has a nonzero chart anchor.
Source: Griffiths--Harris, Chapter 1 §3, projective zero-space. -/
example : ∃ U : Set (Fin 1 → ℂ), IsOpen U ∧ (fun _ ↦ 1) ∈ U ∧
    U ⊆ {z | z 0 ≠ 0} ∧
    ∃ (m : ℕ) (f : Fin m → (Fin 1 → ℂ) → ℂ),
      (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
      ∀ z ∈ U, (z ∈ (univ : Set (Fin 1 → ℂ)) ↔ ∀ j, f j z = 0) := by
  refine chow2_chart_cone 0 univ ?_ 0 ?_ (fun _ ↦ 1) ?_ ?_
  · intro t _ z _
    exact mem_univ _
  · exact isClosedAnalytic_univ
  · exact mem_univ _
  · exact one_ne_zero

end HodgeLean.Foundations
