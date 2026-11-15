import HodgeLean.Foundations.Program.G32SelectedRealizationSecondProofs

/-! # Retained G32 realization: second stage (FROZEN SPEC)

Implication from retained cover data, Nielsen membership and the retained lattice
basis to the marked comparison, primitive factors and realization record.
The comparisons retain one Jacobian and one deck action throughout.
No Schoen class input or Milne invariant input occurs.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected

/-- The image comparison with its central operator, on the same pair of maps.
Source: G32 v0.16, Definition 3.2 and Lemma 3.3; Birkenhake–Lange, §5.3; `b63l_fibre_image_transport`, `b63g5_fiber`. -/
theorem g32y_marked_comparison {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∃ i : (b65z_fiber D B t).X ⟶ g32x_J D t,
    ∃ q : g32x_J D t ⟶ (b65z_fiber D B t).X,
    ∃ N : ℕ, 0 < N ∧ IsMonHom i ∧ IsMonHom q ∧
      i ≫ q = 𝟙 (b65z_fiber D B t).X ^ N ∧
      (∃ z : g32p_G → ℤ, q ≫ i = ∏ a, (f a).hom ^ z a) ∧
      LinearMap.range (homPullback q 1) = LinearMap.range (g32x_projector D t) ∧
      ∃ a : g32p_G, (∃ l : ℂ, l ^ 2 + l + 1 = 0 ∧ b4b_toMatrix a = l • 1) ∧
        ∀ x, homPullback q 1 ((b65z_fiber D B t).W.J x) =
          homPullback q 1 x + (2 : ℚ) • homPullback (f a).hom 1 (homPullback q 1 x) :=
  g32y_marked_comparison_aux D t hg B f hf

example := @g32y_marked_comparison

/-- The rational subgroup-ring projector selects the primitive character factor.
Source: G32 v0.16, Subsection 4.1, the idempotent πχ; Serre, Linear Representations of Finite Groups, §2.6. -/
theorem g32y_primitive_projector {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) :
    letI : Fintype S.H := Fintype.ofFinite S.H
    ∃ u : S.H → ℚ,
      let e : Module.End ℚ (HQ (g32x_J D t) 1) :=
        ∑ h : S.H, u h • homPullback (f h).hom 1
      e ∘ₗ e = e ∧ LinearMap.range e = g32p_primitive (fun a ↦ (f a).hom) S :=
  g32y_primitive_projector_aux D t f hf S

example := @g32y_primitive_projector

/-- Algebraize the primitive image with its inclusion and positive retraction degree.
Source: G32 v0.16, Subsection 4.1; Birkenhake–Lange, §5.3; `b2_subTorus_range`, `b2_image_isWeightOne`, `b2_image_isRiemannForm`, `b5_model`. -/
theorem g32y_primitive_image {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier)
    (hS : g32p_Admissible (fun a ↦ (f a).hom) S) :
    ∃ (P : Over (Spec ↧ℂ)) (_ : GrpObj P) (_ : IsCommMonObj P)
      (_ : IsIntegral P.left) (_ : Smooth P.hom) (_ : IsProjective P.hom),
    ∃ i : P ⟶ g32x_J D t, ∃ q : g32x_J D t ⟶ P,
    ∃ N : ℕ, 0 < N ∧ IsMonHom i ∧ IsMonHom q ∧
      i ≫ q = 𝟙 P ^ N ∧
      LinearMap.range (homPullback q 1) = g32p_primitive (fun a ↦ (f a).hom) S :=
  g32y_primitive_image_aux D t f hf S hS

example := @g32y_primitive_image

/-- Simple exponents give positive even field rank and balanced primitive Hodge multiplicities.
Source: G32 v0.16, Subsection 4.1, the paragraph defining h and simple exponents; Schoen (1988), §1, Lemma 1.5; `b4_chevalleyWeil_holo`. -/
theorem g32y_primitive_balance {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier)
    (hS : g32p_Admissible (fun a ↦ (f a).hom) S) :
    let V := g32p_primitive (fun a ↦ (f a).hom) S
    let M := (abelianVarietyCohomologyOf (finiteBetti_abelian (g32x_J D t))
      (spec_bettiDeRhamIso_abelian (g32x_J D t))
      (hodgeDecomposition_of_abelian (g32x_J D t))
      (torusCohomology_cupProductOf (g32x_J D t))).weight1
    ∃ k : ℕ, 0 < k ∧ ∃ e : V ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field S.m),
      (∀ h : S.H, V.subtype ∘ₗ cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ V.subtype) ∧
      (∀ a pq, ((M.H pq).comap (V.subtype.baseChange ℂ)).map
        ((cyc_scalar e a).baseChange ℂ) ≤ (M.H pq).comap (V.subtype.baseChange ℂ)) ∧
      ∀ σ : cyc_Field S.m →ₐ[ℚ] ℂ,
        Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
          (M.H (1, 0)).comap (V.subtype.baseChange ℂ)) = k :=
  g32y_primitive_balance_aux D t hg f hf S hS

example := @g32y_primitive_balance

/-- Transport the balanced primitive action to its algebraic image and assemble every part field.
Source: G32 v0.16, Subsection 4.1; Birkenhake–Lange, §1.2 and §5.3; `g32y_primitive_image`, `g32y_primitive_balance`. -/
theorem g32y_part {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier)
    (hS : g32p_Admissible (fun a ↦ (f a).hom) S) :
    Nonempty (g32p_Part (g32x_J D t) (fun a ↦ (f a).hom) S) :=
  g32y_part_aux D t hg f hf S hS

example := @g32y_part

/-- Assemble the retained-fibre realization with the specified period Jacobian.
Source: G32 v0.16, Definition 3.2, Lemma 3.3 and Subsection 4.1; `b63g_model_finrank`; the first-stage `g32x` statements and `g32y_marked_comparison`, `g32y_part`. -/
theorem g32y_cover {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∃ R : g32p_Cover (b65z_fiber D B t), R.J = g32x_J D t :=
  g32y_cover_aux D t hg B

example := @g32y_cover

end HodgeLean.Foundations.Program
