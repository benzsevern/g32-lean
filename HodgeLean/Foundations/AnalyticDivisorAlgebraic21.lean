import HodgeLean.Foundations.AnalyticDivisorAlgebraic21Proofs

/-! # Analytic divisor gluing, stage 21

This spec states consequences of genuine local divisor data for the explicitly constructed
branch quotient. Carrier geometry, multiplicity descent and restriction are mathematical proof
obligations, not fields of the output. The finite-product formulation permits a node to have
one global component with two local branches. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic21

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic17

/-- Every constructed component carrier has finite local branch equations in every chart.
Source: Chirka §5.1; `gaga20_component_identification` and local factor matching. -/
theorem gaga21_componentCarrier_finiteLocalBranches {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (C : gaga21_GlobalComponent V f) :
    gaga21_FiniteLocalBranches V f (gaga21_componentCarrier C) :=
  (gaga21_carrier_finite_local_branches_aux hD C).1

/-- Carriers have finite local branch equations, relative closedness, and a connected dense
regular part. No single irreducible local equation is asserted for a global component.
Source: Chirka §5.1; `gaga20_component_identification` and local factor matching. -/
theorem gaga21_carrier_geometry {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) :
    (gaga21_componentCarrier C).Nonempty ∧
    gaga21_componentCarrier C ⊆ U ∧
    IsClosed (((↑) : U → E) ⁻¹' gaga21_componentCarrier C) ∧
    IsConnected (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) ∧
    IsConnected {p | p ∈ gaga21_componentCarrier C ∧ ∃ h : E → ℂ,
      AnalyticAt ℂ h p ∧ h p = 0 ∧ fderiv ℂ h p ≠ 0 ∧
      ∀ᶠ y in 𝓝 p, y ∈ gaga21_componentCarrier C ↔ h y = 0} ∧
    closure (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) ∩ U =
      gaga21_componentCarrier C ∧
    ∀ q ∈ gaga21_componentCarrier C, ∀ i, q ∈ V i →
      ∃ k : ℕ, ∃ a : Fin k → gaga21_LocalFactorOccurrence V f,
        0 < k ∧ (∀ j, (a j).point = q ∧ (a j).chart = i ∧
          Quotient.mk (gaga21_componentSetoid V f) (a j) = C) ∧
        (∀ᶠ y in 𝓝 q, y ∈ gaga21_componentCarrier C ↔ ∃ j, (a j).factor y = 0) ∧
        (∀ b : gaga21_LocalFactorOccurrence V f, b.point = q → b.chart = i →
          (Quotient.mk (gaga21_componentSetoid V f) b = C ↔
            ∃ j, AreAssociatedAt b.factor (a j).factor q)) := by
  rcases gaga21_carrier_nonempty_contained_aux hD C with ⟨hne, hsub⟩
  rcases gaga21_carrier_regular_connected_aux hD C with ⟨hreg, hintrinsic⟩
  exact ⟨hne, hsub, gaga21_carrier_closed_aux hD C, hreg, hintrinsic,
    gaga21_carrier_density_aux hD C, (gaga21_carrier_finite_local_branches_aux hD C).2⟩

/-- The selected exponents agree for any two occurrences in one global component.
Source: `spec_nearby_factor_matching`, `spec_nearby_distinct_group_matching`,
`gaga20_clean_multiplicity`, and `gaga20_multiplicity_constancy`. -/
theorem gaga21_multiplicity_invariance {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f)
    (a b : gaga21_LocalFactorOccurrence V f)
    (hab : Quotient.mk (gaga21_componentSetoid V f) a = Quotient.mk (gaga21_componentSetoid _ _) b) :
    a.exponents a.selected = b.exponents b.selected :=
  gaga21_multiplicity_invariance_aux hD a b hab

/-- Only finitely many constructed carriers meet a sufficiently small neighbourhood.
The analytic finite-incidence input is derived here, not assumed.
Source: Chirka §5.1 (local finiteness of irreducible components);
`spec_nearby_factor_matching` and `spec_nearby_distinct_group_matching`. -/
theorem gaga21_finite_incidence {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f)
    (q : E) (hq : q ∈ U) : ∃ W ∈ 𝓝 q,
      {C : gaga21_GlobalComponent V f | (gaga21_componentCarrier C ∩ W).Nonempty}.Finite :=
  gaga21_finite_incidence_aux hD q hq

/-- Restriction computed only from carrier germs and weights recovers each irreducible local
coefficient of the input equation. This compares independent constructions, including branches
absent from the divisor (coefficient zero).
Source: Griffiths--Harris Ch. 1 §1; `spec_localDivisorAt_eq_of_areAssociatedAt`. -/
theorem gaga21_restriction_multiplicity {n : ℕ} {ι : Type} {U : Set ((Fin n → ℂ) × ℂ)}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {f : ι → (Fin n → ℂ) × ℂ → ℂ}
    (hD : IsLocalDivisorData U V f) (i : ι) (q : (Fin n → ℂ) × ℂ) (hq : q ∈ V i)
    (h : (Fin n → ℂ) × ℂ → ℂ)
    (hh : AnalyticAt ℂ (fun y ↦ h (q + y)) 0) (hi : IsIrreducibleAt h q) :
    gaga21_restrictMultiplicity (gaga21_gluedDivisor V f) q h =
      localDivisorAt n (f i) q (Associates.mk (productAnalyticGermOf (fun y ↦ h (q + y)) hh)) :=
  gaga21_restriction_multiplicity_aux hD i q hq h hh hi

/-- The two coordinate branches define distinct classes and exhaust the quotient of the
two-chart crossing. This quantifies over all certified factorizations and all anchors.
Source: Chirka §5.1; `gaga17_crossing_data` and coordinate-axis connectedness. -/
theorem gaga21_crossing_classes :
    Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 0 0) ≠
      Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 1 1) ∧
    ∀ C : gaga21_GlobalComponent
      (fun _ : Fin 2 ↦ (univ : Set ((Fin 1 → ℂ) × ℂ)))
      (fun _ y ↦ y.1 0 * y.2),
      C = Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 0 0) ∨
      C = Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 1 1) :=
  gaga21_crossing_classes_aux

/-- A single coordinate hyperplane has one global class, in every positive ambient dimension.
Source: Chirka §5.1; `gaga17_axis_power_data` and connectedness of complex affine space. -/
theorem gaga21_axis_classes (n : ℕ) :
    ∀ C : gaga21_GlobalComponent
      (fun _ : Unit ↦ (univ : Set ((Fin n → ℂ) × ℂ))) (fun _ y ↦ y.2),
      C = Quotient.mk (gaga21_componentSetoid _ _) (gaga21_axisOccurrence n 0 rfl) :=
  gaga21_axis_classes_aux n

/-- The nodal polynomial is genuine local divisor data on the whole affine plane.
Source: Gunning--Rossi II.B; polynomial identity and the nonzero quadratic coefficient in `y`. -/
theorem gaga21_node_data  :
    IsLocalDivisorData (univ : Set ((Fin 1 → ℂ) × ℂ))
      (fun _ : Unit ↦ univ) (fun _ ↦ gaga21_node) :=
  gaga21_node_data_aux

/-- The node has one global component and exactly two local branch classes at its singular
point. Nonassociation distinguishes the branches; both lie in the same global quotient class.
Source: normalization `(t²-1,t(t²-1))`, with the two preimages `t=±1`, and Chirka §5.1. -/
theorem gaga21_node_branches  :
    ∃ a b : gaga21_LocalFactorOccurrence
      (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node),
      a.point = 0 ∧ b.point = 0 ∧ ¬ AreAssociatedAt a.factor b.factor 0 ∧
      (∀ c : gaga21_LocalFactorOccurrence
        (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node),
        c.point = 0 → AreAssociatedAt c.factor a.factor 0 ∨
          AreAssociatedAt c.factor b.factor 0) ∧
      ∀ C : gaga21_GlobalComponent
        (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node),
        C = Quotient.mk (gaga21_componentSetoid _ _) a :=
  gaga21_node_branches_aux

/-- Every zero of an input chart has a certified occurrence at that same point.
This supplies non-vacuity of the quotient directly from stage fourteen.
Source: `spec_exists_irreducible_decomposition_at`, Gunning--Rossi II.B, Theorems 3--6. -/
theorem gaga21_occurrence_exists {n : ℕ} {ι : Type} {U : Set ((Fin n → ℂ) × ℂ)}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {f : ι → (Fin n → ℂ) × ℂ → ℂ}
    (hD : IsLocalDivisorData U V f) (i : ι) (q : (Fin n → ℂ) × ℂ)
    (hq : q ∈ V i) (hz : f i q = 0) :
    ∃ a : gaga21_LocalFactorOccurrence V f, a.chart = i ∧ a.point = q := by
  obtain ⟨k, u, P, m, hu, hu0, hP, hcop, hfac⟩ :=
    spec_exists_irreducible_decomposition_at (hD.2.2.1 i q hq) hz
      (hD.2.2.2.1 i q hq)
  have h := hfac.self_of_nhds
  change f i q = u q * ∏ j, P j q ^ m j at h
  rw [hz] at h
  have hp : ∏ j, P j q ^ m j = 0 := (mul_eq_zero.mp h.symm).resolve_left hu0
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  have hj0 : P j q = 0 := eq_zero_of_pow_eq_zero hj
  exact ⟨⟨i, q, hq, k, u, P, m, j, hu, hu0, hP, hcop, hfac, hj0⟩, rfl, rfl⟩

/-- The constructed weights read the selected exponent at every representative.
Source: `gaga21_multiplicity_invariance` and quotient representative selection. -/
theorem gaga21_glued_multiplicity {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (a : gaga21_LocalFactorOccurrence V f) :
    (gaga21_gluedDivisor V f).multiplicity (Quotient.mk (gaga21_componentSetoid V f) a) =
      a.exponents a.selected := by
  exact gaga21_multiplicity_invariance hD _ a (Quotient.out_eq _)

/-- The weighted quotient has positive weights without a positivity input from the caller.
Source: the positive exponents in `spec_exists_irreducible_decomposition_at`. -/
theorem gaga21_glued_positive {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ι → Set E) (f : ι → E → ℂ) (C : gaga21_GlobalComponent V f) :
    0 < (gaga21_gluedDivisor V f).multiplicity C :=
  ((Quotient.out C).factor_data (Quotient.out C).selected).2.2

/-- Analytic finite incidence supplies the input to the existing relative-local-finiteness theorem.
Source: `gaga21_finite_incidence` and `gaga20_relative_local_finiteness`. -/
theorem gaga21_component_locallyFinite {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) :
    LocallyFinite fun C : gaga21_GlobalComponent V f ↦
      ((↑) : U → E) ⁻¹' gaga21_componentCarrier C := by
  apply HodgeLean.Foundations.AnalyticDivisorAlgebraic20.gaga20_relative_local_finiteness
  · rw [← hD.2.1]
    exact isOpen_iUnion hD.1
  · exact gaga21_finite_incidence hD

end HodgeLean.Foundations.AnalyticDivisorAlgebraic21
