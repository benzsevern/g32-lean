import HodgeLean.Foundations.Program.G32SelectedRealizationProofs

/-! # Retained G32 fibre realization: first stage (FROZEN SPEC)

Implication from retained cover data, and where needed its Nielsen membership,
to algebraic deck maps, multiplicities, theta polarization and the Prym image comparison.
The image comparison identifies rational cohomology of the algebraic image with
that of the already retained analytic fibre. The rho statement locates that image.
This first stage does not construct `g32p_Cover`: central Weil compatibility and
primitive cyclotomic factors require further statements, as listed in the scope note.
It uses neither Schoen classes nor Milne invariants.
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

/-- Inverse deck transformations induce algebraic group endomorphisms of the specified Jacobian.
Source: Birkenhake–Lange, §11.4 and Proposition 1.2.1; Serre, GAGA, §3, Proposition 13. -/
theorem g32x_deck_realization {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    ∃ f : g32p_G → AbelianEnd (g32x_J D t),
      ∀ a, homPullback (f a).hom 1 = g32x_deck D t a :=
  g32x_deck_realization_aux D t

example := @g32x_deck_realization

/-- The rationally identified deck maps have the composition convention of the realization record.
Source: Birkenhake–Lange, §1.2 (faithfulness of the rational representation) and §11.4. -/
theorem g32x_deck_laws {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    (f 1).hom = 𝟙 (g32x_J D t) ∧
      ∀ a b, (f (a * b)).hom = (f a).hom ≫ (f b).hom :=
  g32x_deck_laws_aux D t f hf

example := @g32x_deck_laws

/-- Chevalley–Weil multiplicities for the algebraized retained cover fibre.
Source: G32 v0.16, Proposition 3.1 and Definition 3.5; `b4_chevalleyWeil_top`. -/
theorem g32x_multiplicity {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∀ τ : FDRep ℂ g32p_G, Simple τ → (∃ a, τ.ρ a ≠ 1) →
      g32p_multiplicity (fun a ↦ (f a).hom) τ = g32p_cwMult τ :=
  g32x_multiplicity_aux D t hg f hf

example := @g32x_multiplicity

/-- The original theta class is positive, nondegenerate and invariant under the identified deck maps.
Source: Birkenhake–Lange, §11.2; `b4_intersectionForm_invariant`, `b63g4_abelian_positive`. -/
theorem g32x_theta_invariant {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∃ hn : IsNondegenerate
        (polarizationVec (torusCohomology_cupProductOf (g32x_J D t)) (g32x_theta D t)),
      PolarizationPositive (finiteBetti_abelian (g32x_J D t))
        (spec_bettiDeRhamIso_abelian (g32x_J D t))
        (hodgeDecomposition_of_abelian (g32x_J D t))
        (torusCohomology_cupProductOf (g32x_J D t)) hn ∧
      ∀ a, homPullback (f a).hom 2 (g32x_theta D t) = g32x_theta D t :=
  g32x_theta_invariant_aux D t f hf

example := @g32x_theta_invariant

/-- Algebraic group-ring images and rational cohomology agree with the retained analytic Prym fibre.
Source: G32 v0.16, Definition 3.2 and Lemma 3.3; Birkenhake–Lange, §5.3 and Ch. 12; `b2_subTorus_range`, `b63g5_fiber`. -/
theorem g32x_image_comparison {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
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
      LinearMap.range (homPullback q 1) = LinearMap.range (g32x_projector D t) :=
  g32x_image_comparison_aux D t hg B f hf

example := @g32x_image_comparison

/-- The primitive projector image lies in the sum of the natural and conjugate isotypic blocks.
Source: G32 v0.16, Definition 3.2; Serre, Linear Representations of Finite Groups, §2.6, Theorem 8. -/
theorem g32x_rho_image {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    ∀ x ∈ LinearMap.range (g32x_projector D t),
      g32p_rhoProjector (fun a ↦ (f a).hom) ((1 : ℂ) ⊗ₜ[ℚ] x) =
        (1 : ℂ) ⊗ₜ[ℚ] x :=
  g32x_rho_image_aux D t f hf

example := @g32x_rho_image

end HodgeLean.Foundations.Program
