import HodgeLean.Foundations.ChowAbelianSurface3Proofs

/-! # Cone closure and the E² Chow endpoint

Implication from punctured analytic cone data to vertex analyticity, followed by
projective carrier assembly and the premise-free E² Hodge-span statement.
Vertex extension uses the homogeneous-cone projection theorems.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Curves
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- The closure of a nonempty punctured cone adds precisely its vertex.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
topology of the cone construction. -/
theorem chowEE3_closure_eq (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ A) (hne : A.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ A})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ A, t • z ∈ A) :
    closure A = insert 0 A :=
  chowEE3_closure_eq_aux n A hzero hne hclosed hscale

/-- Vertex assembly through a finite proper whole-cone projection.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3;
Chirka, Complex Analytic Sets, §§2–4. -/
theorem chowEE3_vertex_extension_of_point (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ A) (hne : A.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ A})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ A, t • z ∈ A)
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 A) :=
  chowEE3_vertex_extension_of_point_aux n A hzero hne hclosed hscale hloc

/-- Every closed analytic subset of the actual E² has a closed scheme carrier.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
cone proof of Chow; Serre, GAGA, §§1–2, analytification comparison. -/
theorem chowEE3_setLevel :
    ∀ Z : Set (ComplexPoint (g3_power E 2)),
      IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z →
        ∃ C : Set (g3_power E 2).left, IsClosed C ∧
          Z = (Point.underlying : ComplexPoint (g3_power E 2) →
            (g3_power E 2).left) ⁻¹' C :=
  chowEE3_setLevel_aux

/-- The E² Hodge-span endpoint with no geometric premise.
Source: the E² divisor-power theorem `ccm10_hdg_le_span_EE` and the
Chow-to-Lefschetz bridge `bhg_lefschetzOneOne_of_chow`. -/
theorem chowEE3_hdg_le_span_EE :
    ∀ p : ℕ, Hdg^p(g3_power E 2; ℚ) ≤ algebraicCycleClassSpan (g3_power E 2) p :=
  ccm10_hdg_le_span_EE
    (bhg_lefschetzOneOne_of_chow (g3_power E 2) chowEE3_setLevel)

/-- W1: the proper, nonempty punctured coordinate line supplies every premise
of closure and vertex assembly.
Source: linear analytic equations and nonzero scalar orbits. -/
example :
    closure {z : Fin 2 → ℂ | z ≠ 0 ∧ z 1 = 0} =
      insert 0 {z : Fin 2 → ℂ | z ≠ 0 ∧ z 1 = 0} ∧
    IsClosedAnalytic (Fin 2 → ℂ)
      (insert 0 {z : Fin 2 → ℂ | z ≠ 0 ∧ z 1 = 0}) := by
  have hclosed : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} |
      z.val ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0}} := by
    have he : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} | z.val 1 = 0} :=
      isClosed_eq ((continuous_apply (1 : Fin 2) :
        Continuous (fun z : Fin 2 → ℂ ↦ z 1)).comp continuous_subtype_val) continuous_const
    convert he using 1
    ext z
    exact and_iff_right z.property
  have hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0},
      t • z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0} := by
    intro t ht z hz
    exact ⟨smul_ne_zero ht hz.1, by simp [Pi.smul_apply, hz.2]⟩
  have hloc : ∀ x ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0},
      ∃ U : Set (Fin 2 → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ {z | z ≠ 0} ∧
        ∃ (m : ℕ) (f : Fin m → (Fin 2 → ℂ) → ℂ),
          (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
          ∀ z ∈ U, (z ∈ {w : Fin 2 → ℂ | w ≠ 0 ∧ w 1 = 0} ↔ ∀ j, f j z = 0) := by
    intro x hx
    refine ⟨{z | z ≠ 0}, isOpen_ne, hx.1,
      subset_rfl, 1, fun _ z ↦ z 1, ?_, ?_⟩
    · exact fun _ ↦ (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _
    · intro z hz
      exact ⟨fun h _ ↦ h.2, fun h ↦ ⟨hz, h 0⟩⟩

  have hne : ({z : Fin 2 → ℂ | z ≠ 0 ∧ z 1 = 0} : Set (Fin 2 → ℂ)).Nonempty := by
    refine ⟨![1, 0], ?_, by simp⟩
    intro h
    have := congrFun h 0
    norm_num at this
  exact ⟨chowEE3_closure_eq 1 _ (by simp) hne hclosed hscale,
    chowEE3_vertex_extension_of_point 1 _ (by simp) hne hclosed hscale hloc⟩

/-- W2: the full E² is an analytic input with its actual projective presentation.
Source: the empty family of local analytic equations. -/
example : ∃ C : Set (g3_power E 2).left, IsClosed C ∧
    (univ : Set (ComplexPoint (g3_power E 2))) =
      Point.underlying ⁻¹' C :=
  chowEE3_setLevel univ isClosedAnalytic_univ

/-- W3: empty input exercises the separate empty-carrier branch.
Source: empty analytic subsets. -/
example : ∃ C : Set (g3_power E 2).left, IsClosed C ∧
    (∅ : Set (ComplexPoint (g3_power E 2))) =
      Point.underlying ⁻¹' C :=
  chowEE3_setLevel ∅ isClosedAnalytic_empty

/-- W4: codimension one on the actual surface has no additional premises.
Source: the E² endpoint specialized to divisor classes. -/
example : Hdg^1(g3_power E 2; ℚ) ≤ algebraicCycleClassSpan (g3_power E 2) 1 :=
  chowEE3_hdg_le_span_EE 1

/-- W5: codimension two on the actual surface has no additional premises.
Source: the E² endpoint specialized to top-degree classes. -/
example : Hdg^2(g3_power E 2; ℚ) ≤ algebraicCycleClassSpan (g3_power E 2) 2 :=
  chowEE3_hdg_le_span_EE 2

end HodgeLean.Foundations
