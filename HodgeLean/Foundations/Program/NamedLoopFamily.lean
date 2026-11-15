import HodgeLean.Foundations.Program.NamedLoopFamilyProofs

/-! # Retained family with specified monodromy on the named loops

Implication from a labelled root witness to the Möbius restriction and the retained family
identified with the pullback system; implication from specified sphere monodromy to a family
preserving that monodromy on every based class. The final interface uses the stage-three
braid chain. Marking and polarization at the new centre remain separate stages.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- Möbius restriction and the thirteen branch labels.
Source: SchlesingerPathMobius, b65p_mobiusHomeomorph_apply and b65p_mobius_labels; b65p_base_system and b65p_normalized_path. -/
theorem b65w_mobius_restriction (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z) ∧
      ∀ k, b65p_mobius (p 10) (p 11) (b65p_source p 0 k) =
        b6_branch (b65z_centre p) k :=
  b65w_mobius_restriction_aux p hp

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z) ∧
      ∀ k, b65p_mobius (p 10) (p 11) (b65p_source p 0 k) =
        b6_branch (b65z_centre p) k :=
  b65w_mobius_restriction p hp

/-- A sphere marking compatible with pullback transport is onto.
Source: G32 v0.16, §5.2, Lemma 5.2; b65t_pullback_monodromy; faithful matrix image cardinalities and b65t_puncture_fill. -/
theorem b65w_marking_surjective (x : b65s_regular) (ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix
          (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
            (C⁻¹).val) :
    Function.Surjective ρ :=
  b65w_marking_surjective_aux x ρ C hT

example (x : b65s_regular) (ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix
          (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
            (C⁻¹).val) :
    Function.Surjective ρ :=
  b65w_marking_surjective x ρ C hT

/-- Retained family preserving the specified sphere monodromy.
Source: Forster, Lectures on Riemann Surfaces, Theorem 8.4; Völklein, Groups as Galois Groups, Theorem 2.13; b65z_marked_cover, b65z_rot_transfer and b65z_family_construction, with the specified representation replacing the existential presentation. -/
theorem b65w_named_family (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group)
    (hρ : Function.Surjective ρ)
    (hnamed : ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) :
    ∃ g : Fin 13 → b4b_Group, g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) ∧
    ∃ D : b65z_SharedFamily (b65z_centre p) g,
    ∃ u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)},
      ∀ a : FundamentalGroup b65s_sphere (b65s_inclusion x),
        D.atlas.hπ.fundamentalGroupToMulOpposite u₀
          ((FundamentalGroup.map (⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))) (b65s_inclusion x)) a) = MulOpposite.op (ρ a)⁻¹ :=
  b65w_named_family_aux p hp e he x δ hδ ρ hρ hnamed

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group)
    (hρ : Function.Surjective ρ)
    (hnamed : ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) :
    ∃ g : Fin 13 → b4b_Group, g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) ∧
    ∃ D : b65z_SharedFamily (b65z_centre p) g,
    ∃ u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)},
      ∀ a : FundamentalGroup b65s_sphere (b65s_inclusion x),
        D.atlas.hπ.fundamentalGroupToMulOpposite u₀
          ((FundamentalGroup.map (⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))) (b65s_inclusion x)) a) = MulOpposite.op (ρ a)⁻¹ :=
  b65w_named_family p hp e he x δ hδ ρ hρ hnamed

/-- Column conversion for the specified inverse-op monodromy.
Source: b65s_opposite_conversion; G32 v0.16, §5.3, column action convention. -/
theorem b65w_column_conversion (Γ : Type*) [Group Γ] (ρ : Γ →* b4b_Group)
    (μ : Γ →* b4b_Groupᵐᵒᵖ)
    (hμ : ∀ a, μ a = MulOpposite.op (ρ a)⁻¹) :
    ∀ a, (b65s_column μ a).val = b65r_operator (b4b_toMatrix (ρ a)) :=
  b65w_column_conversion_aux Γ ρ μ hμ

example (Γ : Type*) [Group Γ] (ρ : Γ →* b4b_Group)
    (μ : Γ →* b4b_Groupᵐᵒᵖ)
    (hμ : ∀ a, μ a = MulOpposite.op (ρ a)⁻¹) :
    ∀ a, (b65s_column μ a).val = b65r_operator (b4b_toMatrix (ρ a)) :=
  b65w_column_conversion Γ ρ μ hμ

/-- Identification at the G32 centre with the archived interface.
Source: docs/specs/PathCoverFamily.md, set-aside signature; b65b_transported_identification; b65w_mobius_restriction, b65w_marking_surjective, b65w_named_family and b65w_column_conversion. -/
theorem b65z_schlesinger_identification (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ g : Fin 13 → b4b_Group, g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) ∧
    ∃ D : b65z_SharedFamily (b65z_centre p) g,
    ∃ e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z) ∧
    ∃ x : b65s_regular, ∃ u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)},
    ∃ δ : Fin 13 → Path x x,
      (∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) ∧
      (∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹) ∧
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val :=
  b65z_schlesinger_identification_aux p hp

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ g : Fin 13 → b4b_Group, g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) ∧
    ∃ D : b65z_SharedFamily (b65z_centre p) g,
    ∃ e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z) ∧
    ∃ x : b65s_regular, ∃ u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)},
    ∃ δ : Fin 13 → Path x x,
      (∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) ∧
      (∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹) ∧
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val :=
  b65z_schlesinger_identification p hp

end HodgeLean.Foundations.Program
