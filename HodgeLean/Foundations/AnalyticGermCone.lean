import HodgeLean.Foundations.AnalyticGermConeProofs

/-! # Anchored analytic germs and cones: frozen statements

Implication from closed analyticity to anchored finite equations, from finite
equations to a minimal-prime zero-germ cover, and from punctured analyticity
and scalar invariance to positive Krull dimension at every minimal prime.
Geometric dimension comparison and vertex extension remain deferred.

HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.A,
local equations and translation of analytic germs. -/
theorem adim3_local_equations (n : ℕ) (A : Set (Fin n → ℂ))
    (hA : IsClosedAnalytic (Fin n → ℂ) A) (x : Fin n → ℂ) :
    ∃ s : Finset (AnalyticGerm n), adim2_germ n A x = s.inf (adim2_zero n) :=
  adim3_local_equations_aux n A hA x

/-- Source: Gunning--Rossi, III.A, zero germs; de Jong--Pfister,
Local Analytic Geometry, Chapters 3--4, minimal primes in Noetherian local rings. -/
theorem adim3_minimal_prime_cover (n : ℕ) (s : Finset (AnalyticGerm n)) :
    ∃ F : Finset (Ideal (AnalyticGerm n)),
      (F : Set (Ideal (AnalyticGerm n))) =
        (adim2_ideal n (s.inf (adim2_zero n))).minimalPrimes ∧
      s.inf (adim2_zero n) = F.sup (adim2_zeroSet n) :=
  adim3_minimal_prime_cover_aux n s

/-- Source: Chirka, Complex Analytic Sets, §§2--3, local dimension;
Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3, the cone route. -/
theorem adim3_cone_lower_bound (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ A)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ A})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ A, t • z ∈ A)
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    ∀ x ∈ A, ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes,
      (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ P) :=
  adim3_cone_lower_bound_aux n A hzero hclosed hscale hloc

/-- W1: the affine line through (1, 0) has finite equations at that anchor.
Source: Gunning--Rossi, III.A, linear analytic sets. -/
example : ∃ s : Finset (AnalyticGerm 2),
    adim2_germ 2 {z : Fin 2 → ℂ | z 1 = 0} ![1, 0] = s.inf (adim2_zero 2) := by
  apply adim3_local_equations
  simpa using adim_equations_analytic 2 1 (fun _ z ↦ z 1)
    (fun _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticOnNhd _)

/-- W2: the doubled coordinate line is covered by the minimal-prime zero germs.
Source: Gunning--Rossi, III.A, reduced zero loci. -/
example : ∃ F : Finset (Ideal (AnalyticGerm 2)),
    (F : Set (Ideal (AnalyticGerm 2))) =
      (adim2_ideal 2 (adim2_zero 2 (adim_coordinate 1 ^ 2))).minimalPrimes ∧
    adim2_zero 2 (adim_coordinate 1 ^ 2) = F.sup (adim2_zeroSet 2) := by
  simpa using adim3_minimal_prime_cover 2 {adim_coordinate 1 ^ 2}

/-- W3: the punctured line through (1, 0) supplies every geometric premise.
Source: Griffiths--Harris, Chapter 1 §3, linear cones. -/
example : ∀ P ∈ (adim2_ideal 2
    (adim2_germ 2 {z : Fin 2 → ℂ | z ≠ 0 ∧ z 1 = 0} ![1, 0])).minimalPrimes,
    (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm 2 ⧸ P) := by
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
  apply adim3_cone_lower_bound 1 _ (by simp) hclosed hscale hloc ![1, 0]
  constructor
  · intro h
    have := congrFun h 0
    norm_num at this
  · simp

/-- W4: the zero-dimensional ambient space and an empty equation family are valid.
Source: Gunning--Rossi, III.A, empty families of equations. -/
example : ∃ F : Finset (Ideal (AnalyticGerm 0)),
    (F : Set (Ideal (AnalyticGerm 0))) = (adim2_ideal 0 ⊤).minimalPrimes ∧
    (⊤ : adim2_SetGerm 0) = F.sup (adim2_zeroSet 0) := by
  simpa using adim3_minimal_prime_cover 0 ∅

end HodgeLean.Foundations
