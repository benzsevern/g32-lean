import HodgeLean.Foundations.Program.CodifferentialDictionaryProofs
import HodgeLean.Foundations.Program.CodifferentialDictionarySolutions
import HodgeLean.Foundations.Program.CodifferentialComparison

/-! # B6-6 stage 6e: the cover-to-residue dictionary

Implication from a cover solution record, Nielsen data, a compatible marking and the named
cover frame and matrix inputs to the residue dictionary of b66f_numerator_codiff.
The comparison is pointwise; it supplies no analytic choice of changes of frames or rank value.
The four auxiliary bodies are open. HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

/-- First-coordinate evaluation gives a linear injective realization in the labelled direction.
Source: G32 v0.16, §3.1 and §5.1; hg6_sigma_projector; CodifferentialComparison.md, amendment 2. -/
theorem b66d_forms_of_homG (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (S : b65g_Solutions p O D) (hconj : S.conj = true)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (t : b6t_polydisc (b65z_centre p)) (conj : Bool) :
    ∃ Φ : b65g_homG D t conj →ₗ[ℂ] b66f_primitiveForms D t,
      Function.Injective Φ ∧
      (∀ φ : b65g_homG D t conj,
        b66f_chartForm D t (Φ φ).val = φ.val (Pi.single 0 1)) ∧
      ∀ φ : b65g_homG D t conj,
        (Φ φ).val ∈ b66f_direction D (b65z_s₀ (b65z_centre p)) t m (b66d_dir S conj) :=
  b66d_forms_of_homG_aux p O hg D S hconj m hJ hpair t conj

example := @b66d_forms_of_homG

/-- The r and q representation labels are opposite.
Source: G32 v0.16, §5.5(6); CodifferentialComparison.md, 6e-dictionary, item 2. -/
theorem b66d_direction_of_conj (p : Fin 12 → ℂ) (O : b65p_Outputs p) {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    b66d_dir S S.conj = 0 ∧ b66d_dir S (!S.conj) = 1 :=
  b66d_direction_of_conj_aux p O D S

example := @b66d_direction_of_conj

/-- The residue array of first-coordinate forms is a nonzero scalar times a permuted
numerator array in branch coordinates; the scalar and permutation are uniform near zero.
Source: G32 v0.16, §5.1, Lemmas 5.3 and 5.5; Forster, Lectures on Riemann Surfaces, §17;
CodifferentialComparison.md, 6e-dictionary, item 3. -/
theorem b66d_residue_normalization (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (S : b65g_Solutions p O D)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    : ∃ (κ : ℂ) (π : Equiv.Perm (Fin 9)) (ε : ℝ),
      κ ≠ 0 ∧ 0 < ε ∧ ε ≤ S.radius ∧
      ∀ θ ∈ Metric.ball (0 : ℂ) ε,
      ∀ (t : b6t_polydisc (b65z_centre p)), t.val = b65p_curve p θ →
      ∀ (φ : Fin 3 → b65g_homG D t S.conj)
        (ψ : Fin 3 → b65g_homG D t (!S.conj))
        (q r : Fin 3 → b66f_primitiveForms D t)
        (G : Matrix (Fin 9) (Fin 10) ℂ),
        LinearIndependent ℂ φ → LinearIndependent ℂ ψ →
        (∀ i, b66f_chartForm D t (q i).val = (φ i).val (Pi.single 0 1)) →
        (∀ i, b66f_chartForm D t (r i).val = (ψ i).val (Pi.single 0 1)) →
        (∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
          u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
          b65g_contract (φ a).val (ψ b).val u =
            b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11)
              (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) →
        ∃ (Z : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ),
          (∀ j a z, z ∈ b66f_domain D t a → MeromorphicAt (v j a) z) ∧
          (∀ j a z, z ∈ b66f_domain D t a →
            ((D.atlas.A a).symm (t.val, z)).2 ∉ Z j → AnalyticAt ℂ (v j a) z) ∧
          (∀ j a b x, x ∉ Z j → (t, x) ∈ (D.atlas.A a).source →
            (t, x) ∈ (D.atlas.A b).source →
            b66f_cocycle D t (Pi.single j 1) a b x = b66f_boundary D t (v j) a b x) ∧
          b66f_multiplicationMatrix D t q r Z v =
            κ • ((Matrix.of (fun i j : Fin 9 ↦ if π i = j then (1 : ℂ) else 0)) * G * b65g_branchMatrix p θ) :=
  b66d_residue_normalization_aux p O hg D S m hJ hpair

example := @b66d_residue_normalization

/-- Implication from the cover frame, unit and branch-coordinate statements to the
residue dictionary binder used by b66f_numerator_codiff.
Source: G32 v0.16, Lemma 5.8; CodifferentialComparison.md, 6e-dictionary assembly. -/
theorem b66d_dictionary (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (S : b65g_Solutions p O D) (hconj : S.conj = true)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (hframes : ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∃ φ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ a, φ a ∈ b65g_homG D t S.conj ∧ b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) (φ a)) ∧
        LinearIndependent ℂ φ ∧ Submodule.span ℂ (Set.range φ) = b65g_homG D t S.conj) ∧
      ∃ ψ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ b, ψ b ∈ b65g_homG D t (!S.conj) ∧ b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) (ψ b)) ∧
        LinearIndependent ℂ ψ ∧ Submodule.span ℂ (Set.range ψ) = b65g_homG D t (!S.conj))
    (hunits : ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (βr βq : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (c : Matrix (Fin 36) (Fin 3) ℂ)
        (d : Matrix (Fin 48) (Fin 3) ℂ),
        (∀ a, βr a ∈ b65g_homG D t S.conj) → (∀ b, βq b ∈ b65g_homG D t (!S.conj)) →
        LinearIndependent ℂ βr → LinearIndependent ℂ βq →
        (∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c i a)) (βr a)) →
        (∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d i b)) (βq b)) →
        (∃! G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G) ∧
        IsUnit (b65g_A c d) ∧
        ∀ G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G →
          b65q_numMatrix p O.residue θ = b65g_A c d * G)
    (hbranch : ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ j k : Fin 10, AnalyticOnNhd ℂ (fun θ ↦ b65g_B p θ j k) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, IsUnit (b65g_branchMatrix p θ) ∧
        ∀ (N : Fin 10 → ℂ) (k : Fin 10),
          Tendsto (fun s : ℂ ↦ (s - b65p_moving p θ (Fin.castLE (by norm_num) k)) *
              (∑ j : Fin 10, N j * s ^ j.val) /
              ((b65q_denominator (b65p_poles p θ)).eval s *
                deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11)) s))
            (𝓝[≠] (b65p_moving p θ (Fin.castLE (by norm_num) k)))
            (𝓝 ((N ᵥ* b65g_branchMatrix p θ) k)))
    : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ ht : b65p_curve p θ ∈ b6t_polydisc (b65z_centre p),
      ∃ (q r : Fin 3 → b66f_primitiveForms D ⟨b65p_curve p θ, ht⟩)
        (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
        (A : Matrix (Fin 9) (Fin 9) ℂ) (B : Matrix (Fin 10) (Fin 10) ℂ),
        (∀ i, (q i).val ∈
          b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩ m 0) ∧
        (∀ i, (r i).val ∈
          b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩ m 1) ∧
        LinearIndependent ℂ q ∧ LinearIndependent ℂ r ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a → MeromorphicAt (v j a) z) ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a →
          ((D.atlas.A a).symm (b65p_curve p θ, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z) ∧
        (∀ j a b x, x ∉ S j → (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A a).source →
          (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A b).source →
          b66f_cocycle D ⟨b65p_curve p θ, ht⟩ (Pi.single j 1) a b x =
            b66f_boundary D ⟨b65p_curve p θ, ht⟩ (v j) a b x) ∧
        IsUnit A ∧ IsUnit B ∧
        b65q_numMatrix p O.residue θ =
          A * b66f_multiplicationMatrix D ⟨b65p_curve p θ, ht⟩ q r S v * B :=
  b66d_dictionary_aux p O hg D S hconj m hJ hpair hframes hunits hbranch

example := @b66d_dictionary

/-- Interface check: the dictionary result occupies the existing hdict argument. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (S : b65g_Solutions p O D) (hconj : S.conj = true)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (hframes : ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∃ φ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ a, φ a ∈ b65g_homG D t S.conj ∧ b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) (φ a)) ∧
        LinearIndependent ℂ φ ∧ Submodule.span ℂ (Set.range φ) = b65g_homG D t S.conj) ∧
      ∃ ψ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ b, ψ b ∈ b65g_homG D t (!S.conj) ∧ b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) (ψ b)) ∧
        LinearIndependent ℂ ψ ∧ Submodule.span ℂ (Set.range ψ) = b65g_homG D t (!S.conj))
    (hunits : ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (βr βq : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (c : Matrix (Fin 36) (Fin 3) ℂ)
        (d : Matrix (Fin 48) (Fin 3) ℂ),
        (∀ a, βr a ∈ b65g_homG D t S.conj) → (∀ b, βq b ∈ b65g_homG D t (!S.conj)) →
        LinearIndependent ℂ βr → LinearIndependent ℂ βq →
        (∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c i a)) (βr a)) →
        (∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d i b)) (βq b)) →
        (∃! G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G) ∧
        IsUnit (b65g_A c d) ∧
        ∀ G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G →
          b65q_numMatrix p O.residue θ = b65g_A c d * G)
    (hbranch : ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ j k : Fin 10, AnalyticOnNhd ℂ (fun θ ↦ b65g_B p θ j k) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, IsUnit (b65g_branchMatrix p θ) ∧
        ∀ (N : Fin 10 → ℂ) (k : Fin 10),
          Tendsto (fun s : ℂ ↦ (s - b65p_moving p θ (Fin.castLE (by norm_num) k)) *
              (∑ j : Fin 10, N j * s ^ j.val) /
              ((b65q_denominator (b65p_poles p θ)).eval s *
                deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11)) s))
            (𝓝[≠] (b65p_moving p θ (Fin.castLE (by norm_num) k)))
            (𝓝 ((N ᵥ* b65g_branchMatrix p θ) k)))
    (hker : ∀ᶠ θ in 𝓝 (0 : ℂ),
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0)
    :
    ∀ᶠ θ in 𝓝 (0 : ℂ),
      ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
        IsUnit L ∧ IsUnit T ∧
        b65e_numerator p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ
            (b65z_period D (b65z_s₀ (b65z_centre p)) m)
            (b65p_curve p θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T :=
  b66f_numerator_codiff p O hg D m hJ hpair hker
    (b66d_dictionary p O hg D S hconj m hJ hpair hframes hunits hbranch)

/-- The two Boolean choices give the same r/q label order. -/
example {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
    {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)
    (h : S.conj = false) : b66d_dir S false = 0 ∧ b66d_dir S true = 1 := by
  simp [b66d_dir, h]

example {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
    {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)
    (h : S.conj = true) : b66d_dir S true = 0 ∧ b66d_dir S false = 1 := by
  simp [b66d_dir, h]

/-- First-coordinate evaluation distinguishes the chosen line from the next line. -/
example : (LinearMap.proj (0 : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (Pi.single 0 1) = 1 ∧
    (LinearMap.proj (0 : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (Pi.single 1 1) = 0 := by
  norm_num [Pi.single_apply]

end HodgeLean.Foundations.Program
