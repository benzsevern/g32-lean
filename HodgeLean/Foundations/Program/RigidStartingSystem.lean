import HodgeLean.Foundations.Program.RigidStartingSystemProofs

/-! # Starting-system statements

Implication from explicit residues and the index-two criterion to the four-point
local-class and rigidity assertions, with a separate marked-chart comparison.
The thirteen-point pullback requires a further marking comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
open Set Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The finite chart identifies the marked sphere and the finite-pole plane, including all thirteen generators.
Source: Forster, Lectures on Riemann Surfaces, §1.3 and §13; b65f_monodromy_representation; mr_curve and b63gP_loops. -/
theorem b65r_marked_comparison (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (R : ℂ → E →L[ℂ] E) :
    ∃ x : {z : ℂ // z ∉ b65r_marks},
      ∃ e : {z : ℂ // z ∉ b65r_marks} ≃ₜ b6t_punctured mr_base,
      ∃ hx : e x = b63gP_basePoint,
        (∀ z, (e z : OnePoint ℂ) = ((z.val : ℂ) : OnePoint ℂ)) ∧
        ∃ P : FundamentalGroup {z : ℂ // z ∉ b65r_marks} x →* (E →L[ℂ] E)ˣ,
        ∃ M : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* (E →L[ℂ] E)ˣ,
          (∀ γ : Path x x,
            (P (FundamentalGroup.fromPath ⟦γ⟧) : E →L[ℂ] E) =
              b65f_transport E (b65f_coefficient E b65r_marks R)
                (fun t ↦ (γ.extend t).val)) ∧
          (∀ c, M (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ hx c) = P c) ∧
          (∀ i, (M (b63gP_loops i) : E →L[ℂ] E) =
            b65f_transport E (b65f_coefficient E b65r_marks R) (b65r_curve i)) :=
  b65r_marked_comparison_aux E R

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (R : ℂ → E →L[ℂ] E) :
    ∃ x : {z : ℂ // z ∉ b65r_marks},
      ∃ e : {z : ℂ // z ∉ b65r_marks} ≃ₜ b6t_punctured mr_base,
      ∃ hx : e x = b63gP_basePoint,
        (∀ z, (e z : OnePoint ℂ) = ((z.val : ℂ) : OnePoint ℂ)) ∧
        ∃ P : FundamentalGroup {z : ℂ // z ∉ b65r_marks} x →* (E →L[ℂ] E)ˣ,
        ∃ M : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* (E →L[ℂ] E)ˣ,
          (∀ γ : Path x x,
            (P (FundamentalGroup.fromPath ⟦γ⟧) : E →L[ℂ] E) =
              b65f_transport E (b65f_coefficient E b65r_marks R)
                (fun t ↦ (γ.extend t).val)) ∧
          (∀ c, M (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ hx c) = P c) ∧
          (∀ i, (M (b63gP_loops i) : E →L[ℂ] E) =
            b65f_transport E (b65f_coefficient E b65r_marks R) (b65r_curve i)) :=
  b65r_marked_comparison E R

/-- The w = 1/z chart has residue minus the sum of finite residues.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §16; G32 v0.16, §5.2. -/
theorem b65r_infinity_residue (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (s : Finset ℂ) (R : ℂ → E →L[ℂ] E) :
    Filter.Tendsto
      (fun w : ℂ ↦ -w⁻¹ • b65f_coefficient E s R w⁻¹)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (-∑ a ∈ s, R a)) :=
  b65r_infinity_residue_aux E s R

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (s : Finset ℂ) (R : ℂ → E →L[ℂ] E) :
    Filter.Tendsto
      (fun w : ℂ ↦ -w⁻¹ • b65f_coefficient E s R w⁻¹)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (-∑ a ∈ s, R a)) :=
  b65r_infinity_residue E s R

/-- The four explicit nonresonant residues have the printed four exponential conjugacy classes.
Source: G32 v0.16, §5.2 and Appendix A; Ilyashenko–Yakovenko, §16. -/
theorem b65r_residue_classes  :
    ∀ i : Fin 4,
      (∀ k : ℕ, 0 < k → Function.Bijective
        (fun T : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦
          (k : ℂ) • T - (b65r_operator (b65r_residues i) * T -
            T * b65r_operator (b65r_residues i)))) ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          NormedSpace.exp ((2 * Real.pi * Complex.I) • b65r_operator (b65r_residues i)) *
          ↑(C⁻¹) = b65r_operator (b4b_toMatrix (b4b_generators i)) :=
  b65r_residue_classes_aux 

example  :
    ∀ i : Fin 4,
      (∀ k : ℕ, 0 < k → Function.Bijective
        (fun T : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦
          (k : ℂ) • T - (b65r_operator (b65r_residues i) * T -
            T * b65r_operator (b65r_residues i)))) ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          NormedSpace.exp ((2 * Real.pi * Complex.I) • b65r_operator (b65r_residues i)) *
          ↑(C⁻¹) = b65r_operator (b4b_toMatrix (b4b_generators i)) :=
  b65r_residue_classes 

/-- An irreducible product-one tuple of index two determines every tuple in its local classes.
Only T is required to be irreducible.
Source: Katz, Rigid Local Systems, Theorem 1.1.2; G32 v0.16, §5.2, Hom-local-system argument. -/
theorem b65r_rigidity (n r : ℕ) (hn : 0 < n)
    (T S : Fin r → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hT : (List.ofFn T).prod = 1) (hS : (List.ofFn S).prod = 1)
    (hirr : ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ i v, v ∈ W → (T i).val.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hidx : b65r_index (fun i ↦ (T i).val) = 2)
    (hloc : ∀ i, ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, C * T i * C⁻¹ = S i) :
    ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ i, C * T i * C⁻¹ = S i :=
  b65r_rigidity_aux n r hn T S hT hS hirr hidx hloc

example (n r : ℕ) (hn : 0 < n)
    (T S : Fin r → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hT : (List.ofFn T).prod = 1) (hS : (List.ofFn S).prod = 1)
    (hirr : ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ i v, v ∈ W → (T i).val.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hidx : b65r_index (fun i ↦ (T i).val) = 2)
    (hloc : ∀ i, ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, C * T i * C⁻¹ = S i) :
    ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ i, C * T i * C⁻¹ = S i :=
  b65r_rigidity n r hn T S hT hS hirr hidx hloc

/-- Centralizer dimensions and irreducibility for the four-point printed tuple.
Source: G32 v0.16, §5.2 and Appendix A, class dimensions 6, 6, 10, 8 and generated matrix algebra. -/
theorem b65r_four_point_data  :
    (∀ i : Fin 4,
      Module.finrank ℂ (b65r_centralizer (b4b_toMatrix (b4b_generators i))) =
        (![10, 10, 6, 8] : Fin 4 → ℕ) i) ∧
      b65r_index (fun i ↦ b4b_toMatrix (b4b_generators i)) = 2 ∧
      (∀ W : Submodule ℂ (Fin 4 → ℂ),
        (∀ i v, v ∈ W → (b4b_toMatrix (b4b_generators i)).mulVec v ∈ W) →
          W = ⊥ ∨ W = ⊤) :=
  b65r_four_point_data_aux 

example  :
    (∀ i : Fin 4,
      Module.finrank ℂ (b65r_centralizer (b4b_toMatrix (b4b_generators i))) =
        (![10, 10, 6, 8] : Fin 4 → ℕ) i) ∧
      b65r_index (fun i ↦ b4b_toMatrix (b4b_generators i)) = 2 ∧
      (∀ W : Submodule ℂ (Fin 4 → ℂ),
        (∀ i v, v ∈ W → (b4b_toMatrix (b4b_generators i)).mulVec v ∈ W) →
          W = ⊥ ∨ W = ⊤) :=
  b65r_four_point_data 

/-- The explicit residue expression is the degree-six pullback coefficient on its regular domain.
Source: G32 v0.16, §5.2, Appendix A and §5.4, the initial pulled-back residues. -/
theorem b65r_pullback_identity (s : ℂ) (h0 : s ≠ 0) (h3 : s ≠ 3)
    (h1 : s ≠ 1) (hneg2 : s ≠ -2)
    (h5 : b65r_P 5 s ≠ 0) (hneg7 : b65r_P (-7) s ≠ 0) :
    deriv b65r_phi s = 3*s*(s-3)^3*(5*s^2-3*s+4) / ((s-1)^4*(s+2)^4) ∧
      b65r_pullback s = deriv b65r_phi s • b65r_A (b65r_phi s) :=
  b65r_pullback_identity_aux s h0 h3 h1 hneg2 h5 hneg7

example (s : ℂ) (h0 : s ≠ 0) (h3 : s ≠ 3)
    (h1 : s ≠ 1) (hneg2 : s ≠ -2)
    (h5 : b65r_P 5 s ≠ 0) (hneg7 : b65r_P (-7) s ≠ 0) :
    deriv b65r_phi s = 3*s*(s-3)^3*(5*s^2-3*s+4) / ((s-1)^4*(s+2)^4) ∧
      b65r_pullback s = deriv b65r_phi s • b65r_A (b65r_phi s) :=
  b65r_pullback_identity s h0 h3 h1 hneg2 h5 hneg7

/-- Small positive circles of the pullback have the ramification-power local classes.
This includes the resonant and apparent poles by pullback of the nonresonant system.
Source: G32 v0.16, §5.2 and §5.4, the local monodromy of φ*L. -/
theorem b65r_pullback_local_monodromy (a : ℂ)
    (ha : a = 0 ∨ a = 3 ∨ a = 1 ∨ a = -2 ∨
      b65r_P 5 a = 0 ∨ b65r_P (-7) a = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (b65f_circle a ρ) =
          (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
            b65r_operator (b4b_toMatrix (b65r_localTarget a)) * ↑(C⁻¹) :=
  b65r_pullback_local_monodromy_aux a ha

example (a : ℂ)
    (ha : a = 0 ∨ a = 3 ∨ a = 1 ∨ a = -2 ∨
      b65r_P 5 a = 0 ∨ b65r_P (-7) a = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (b65f_circle a ρ) =
          (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
            b65r_operator (b4b_toMatrix (b65r_localTarget a)) * ↑(C⁻¹) :=
  b65r_pullback_local_monodromy a ha

/-- The four-point system has the printed faithful G32 representation as its monodromy image.
The quotient map is supplied, rather than assumed as a premise.
Source: G32 v0.16, §5.2, the monodromy of L; Katz, Rigid Local Systems, Theorem 1.1.2. -/
theorem b65r_four_point_monodromy (x : {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}) :
    ∃ ρ : FundamentalGroup {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} x →* b4b_Group,
      Function.Surjective ρ ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        ∀ γ : Path x x,
          b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
            (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
              b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹) :=
  b65r_four_point_monodromy_aux x

example (x : {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}) :
    ∃ ρ : FundamentalGroup {z : ℂ // z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7} x →* b4b_Group,
      Function.Surjective ρ ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        ∀ γ : Path x x,
          b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
            (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
              b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹) :=
  b65r_four_point_monodromy x

/-- Field-type check for the path inputs of the downstream period map.
Source: HodgeLean/Papers/G32DominanceDefs.lean, curve_cont and curve_zero. -/
example (V : Set (Fin 10 → ℂ)) (hV : mr_base ∈ V) :
    ∃ curve : ℂ → Fin 10 → ℂ,
      (∀ θ i, curve θ i = mr_base i + θ * b65r_phi 2) ∧
      ContinuousAt curve 0 ∧ curve 0 ∈ V ∧ curve 1 ≠ curve 0 := by
  refine ⟨fun θ i ↦ mr_base i + θ * b65r_phi 2, ?_, ?_, ?_, ?_⟩
  · intro θ i; rfl
  · fun_prop
  · simpa using hV
  · intro h
    have hv := congrFun h (0 : Fin 10)
    norm_num [mr_base, b65r_phi] at hv

end HodgeLean.Foundations.Program
