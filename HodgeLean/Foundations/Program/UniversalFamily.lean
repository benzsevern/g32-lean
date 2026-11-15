import HodgeLean.Foundations.Program.UniversalFamilyProofs

/-! # B6-0b: algebraic fibres and their marked periods

The implication from bounded-domain membership to polarized Weil membership uses B5's
explicit theta model and marking. The period comparison identifies all nine coordinates.
Landherr coverage and the full universal-family record belong to B6-0c and later assembly.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Foundations.Program

/-- The transported action satisfies the quadratic relation and preserves the Hodge pieces.
Source: G32 v0.16, Definition 2.1; van Geemen, LNM 1594, §5.1; B5 period filtration. -/
theorem b60b_action_valid (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_model τ)).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
      (spec_bettiDeRhamIso_abelian (b60b_model τ))
      (hodgeDecomposition_of_abelian (b60b_model τ))
      (torusCohomology_cupProductOf (b60b_model τ))
    (b60b_J τ).comp (b60b_J τ) = (-3 : ℚ) • LinearMap.id ∧
      ∀ pq : ℤ × ℤ, (S.weight1.H pq).map ((b60b_J τ).baseChange ℂ) ≤ S.weight1.H pq :=
  b60b_action_valid_aux τ

example (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_model τ)).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
      (spec_bettiDeRhamIso_abelian (b60b_model τ))
      (hodgeDecomposition_of_abelian (b60b_model τ))
      (torusCohomology_cupProductOf (b60b_model τ))
    (b60b_J τ).comp (b60b_J τ) = (-3 : ℚ) • LinearMap.id ∧
      ∀ pq : ℤ × ℤ, (S.weight1.H pq).map ((b60b_J τ).baseChange ℂ) ≤ S.weight1.H pq := b60b_action_valid τ

/-- The H¹ action is dual to the specified integral action.
Source: G32 v0.16, Definition 2.1; Birkenhake–Lange, §1.2. -/
theorem b60b_action (τ : g32m_Domain) (v : HQ (b60b_univ τ).X 1) (l : b60_Lattice) :
    abelianPeriodEquiv (b60b_univ τ).X ((b60b_univ τ).W.J v) (b60b_marking τ l) =
      abelianPeriodEquiv (b60b_univ τ).X v (b60b_marking τ (b60_omega l)) :=
  b60b_action_aux τ v l

example (τ : g32m_Domain) (v : HQ (b60b_univ τ).X 1) (l : b60_Lattice) :
    abelianPeriodEquiv (b60b_univ τ).X ((b60b_univ τ).W.J v) (b60b_marking τ l) =
      abelianPeriodEquiv (b60b_univ τ).X v (b60b_marking τ (b60_omega l)) := b60b_action τ v l

/-- Each fibre has complex dimension six.
Source: G32 v0.16, §2.1; Birkenhake–Lange, §1.1. -/
theorem b60b_dimension (τ : g32m_Domain) :
    dim (b60b_univ τ).X.left = 6 :=
  b60b_dimension_aux τ

example (τ : g32m_Domain) :
    dim (b60b_univ τ).X.left = 6 := b60b_dimension τ

/-- The two embeddings contribute three holomorphic dimensions each, giving Weil type.
Source: G32 v0.16, Definition 2.1; van Geemen, LNM 1594, §§5.1–5.7. -/
theorem b60b_signature (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X)
    Module.finrank ℂ ↥((b60b_univ τ).W.Vs ⊓ S.weight1.H (1, 0)) = 3 ∧
      Module.finrank ℂ ↥((b60b_univ τ).W.Vsbar ⊓ S.weight1.H (1, 0)) = 3 ∧
      (b60b_univ τ).W.IsWeilType :=
  b60b_signature_aux τ

example (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X)
    Module.finrank ℂ ↥((b60b_univ τ).W.Vs ⊓ S.weight1.H (1, 0)) = 3 ∧
      Module.finrank ℂ ↥((b60b_univ τ).W.Vsbar ⊓ S.weight1.H (1, 0)) = 3 ∧
      (b60b_univ τ).W.IsWeilType := b60b_signature τ

/-- The original polarization has nondegenerate alternating form.
Source: Birkenhake–Lange, §2.1; G32 v0.16, §2.1. -/
theorem b60b_nondegenerate (τ : g32m_Domain) :
    IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol) :=
  b60b_nondegenerate_aux τ

example (τ : g32m_Domain) :
    IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol) := b60b_nondegenerate τ

/-- The action is Rosati skew and the polarization satisfies Hodge–Riemann positivity.
Source: G32 v0.16, Definition 2.1; Birkenhake–Lange, §§2.1–2.2. -/
theorem b60b_polarization (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol) (b60b_univ τ).W.J ∧
    PolarizationPositive (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_nondegenerate τ) :=
  b60b_polarization_aux τ

example (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol) (b60b_univ τ).W.J ∧
    PolarizationPositive (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_nondegenerate τ) := b60b_polarization τ

/-- The Hermitian discriminant is the norm class of −2.
Source: G32 v0.16, §2; van Geemen, LNM 1594, Lemma 5.2. -/
theorem b60b_discriminant (τ : g32m_Domain) :
    weilDatumClass (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).W
      (b60b_nondegenerate τ) (b60b_polarization τ).1 = classNegTwo :=
  b60b_discriminant_aux τ

example (τ : g32m_Domain) :
    weilDatumClass (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).W
      (b60b_nondegenerate τ) (b60b_polarization τ).1 = classNegTwo := b60b_discriminant τ

/-- The explicit algebraic fibre belongs to the specified polarized Weil moduli problem.
Source: G32 v0.16, §2.1 and Theorem A (membership clauses). -/
theorem b60b_member (τ : g32m_Domain) :
    g32t_IsMember (b60b_univ τ) :=
  b60b_member_aux τ

example (τ : g32m_Domain) :
    g32t_IsMember (b60b_univ τ) := b60b_member τ

/-- The H² class is the exterior transport of the original Chern pairing.
Source: Birkenhake–Lange, Lemma 1.3.1 and §2.2; B5 polarization normalization. -/
theorem b60b_polarization_transport (τ : g32m_Domain) :
    (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol =
      exteriorPower.map 2 (abelianPeriodEquiv (b60b_univ τ).X).symm.toLinearMap
        (latticeClass (b2_bilinToAddHom (b60b_form τ)))) ∧
    ∀ l m : b2_abelianLattice (b60b_model τ),
      b60b_form τ l m = b5_originalChernPairing b60_Lattice (b60_F τ)
        (b60_weight_one τ) b60_E ((b60_riemann_iff τ).2 τ.property) l m :=
  b60b_polarization_transport_aux τ

example (τ : g32m_Domain) :
    (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol =
      exteriorPower.map 2 (abelianPeriodEquiv (b60b_univ τ).X).symm.toLinearMap
        (latticeClass (b2_bilinToAddHom (b60b_form τ)))) ∧
    ∀ l m : b2_abelianLattice (b60b_model τ),
      b60b_form τ l m = b5_originalChernPairing b60_Lattice (b60_F τ)
        (b60_weight_one τ) b60_E ((b60_riemann_iff τ).2 τ.property) l m := b60b_polarization_transport τ

/-- The marked algebraic period has exactly the original nine domain coordinates.
Source: G32 v0.16, §2.1; van Geemen, LNM 1594, §§5.7–5.11. -/
theorem b60b_period (τ σ : g32m_Domain) :
    (b60_F σ).map (b2_cplxMap (b60b_marking τ).toAddMonoidHom) =
      b2_abelianF (b60b_univ τ).X ↔ σ = τ :=
  b60b_period_aux τ σ

example (τ σ : g32m_Domain) :
    (b60_F σ).map (b2_cplxMap (b60b_marking τ).toAddMonoidHom) =
      b2_abelianF (b60b_univ τ).X ↔ σ = τ := b60b_period τ σ

end HodgeLean.Foundations.Program
