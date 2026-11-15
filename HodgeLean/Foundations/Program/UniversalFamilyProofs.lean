import HodgeLean.Foundations.Program.UniversalFamilyDefs
import HodgeLean.Foundations.Program.PrymFamilyB4Proofs
import HodgeLean.Foundations.Program.UniversalFamilyB60bDiscriminant

/-! # B6-0b: fibre construction and proof obligations

The sixfold uses explicit data and proof-valued compatibility fields.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b60b_action_valid_aux (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_model τ)).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
      (spec_bettiDeRhamIso_abelian (b60b_model τ))
      (hodgeDecomposition_of_abelian (b60b_model τ))
      (torusCohomology_cupProductOf (b60b_model τ))
    (b60b_J τ).comp (b60b_J τ) = (-3 : ℚ) • LinearMap.id ∧
      ∀ pq : ℤ × ℤ, (S.weight1.H pq).map ((b60b_J τ).baseChange ℂ) ≤ S.weight1.H pq := by
  constructor
  · apply b4b_action_sq_aux
    intro l
    exact LinearMap.congr_fun b60_omega_square l
  · apply b4b_action_preserves_aux b60_Lattice (b60b_model τ) (b60b_marking τ)
      (b60_F τ)
    · exact b5_period_filtration _ _ (b60_weight_one τ) _ ((b60_riemann_iff τ).2 τ.property)
    · intro x hx
      exact b60_omega_preserves τ ⟨x, hx, rfl⟩

/-- The marked algebraic fibre with the dual ω action and original polarization.
Source: G32 v0.16, §2.1; van Geemen, LNM 1594, §§5.7–5.11;
Birkenhake–Lange, Theorem 4.5.1. -/
def b60b_univ (τ : g32m_Domain) : g32t_Sixfold where
  X := b60b_model τ
  W := { J := b60b_J τ
         J_sq := (b60b_action_valid_aux τ).1
         preserves := (b60b_action_valid_aux τ).2 }
  pol := b60b_pol τ

example (τ : g32m_Domain) : (b60b_univ τ).X = b60b_model τ := rfl


theorem b60b_action_aux (τ : g32m_Domain) (v : HQ (b60b_univ τ).X 1) (l : b60_Lattice) :
    abelianPeriodEquiv (b60b_univ τ).X ((b60b_univ τ).W.J v) (b60b_marking τ l) =
      abelianPeriodEquiv (b60b_univ τ).X v (b60b_marking τ (b60_omega l)) := by
  exact b60b_action_model τ v l

theorem b60b_dimension_aux (τ : g32m_Domain) :
    dim (b60b_univ τ).X.left = 6 := by
  have hmark := (b60b_marking τ).toIntLinearEquiv.finrank_eq
  have hab : Module.finrank ℤ (b2_abelianLattice (b60b_model τ)) =
      2 * dim (b60b_model τ).left := by
    rw [← b2_two_mul_finrank (b2_abelianF (b60b_model τ))
      (b2_abelianF_isWeightOne (b60b_model τ)), b2_abelian_finrank]
  rw [b60b_lattice_finrank] at hmark
  rw [hab] at hmark
  dsimp only [b60b_univ]
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  norm_num
  exact hmark.symm

theorem b60b_signature_aux (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X)
    Module.finrank ℂ ↥((b60b_univ τ).W.Vs ⊓ S.weight1.H (1, 0)) = 3 ∧
      Module.finrank ℂ ↥((b60b_univ τ).W.Vsbar ⊓ S.weight1.H (1, 0)) = 3 ∧
      (b60b_univ τ).W.IsWeilType := by
  let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
    (spec_bettiDeRhamIso_abelian (b60b_model τ))
    (hodgeDecomposition_of_abelian (b60b_model τ))
    (torusCohomology_cupProductOf (b60b_model τ))
  let A : HodgeBlocks.WeilAction S.weight1 3 :=
    { J := b60b_J τ
      J_sq := (b60b_action_valid_aux τ).1
      preserves := (b60b_action_valid_aux τ).2 }
  change Module.finrank ℂ ↥(A.Vs ⊓ S.weight1.H (1, 0)) = 3 ∧
    Module.finrank ℂ ↥(A.Vsbar ⊓ S.weight1.H (1, 0)) = 3 ∧ A.IsWeilType
  let e := b60b_homologyCohomologyEquiv τ
  let F := b60_F τ
  let rp : ℂ := Complex.I * (Real.sqrt 3 : ℂ)
  have hF := b60b_homologyCohomology_F τ
  have hp := b60b_map_eigenspace τ rp
  have hn := b60b_map_eigenspace τ (-rp)
  have hmapP : (F ⊓ Module.End.eigenspace b60_omegaC (-rp)).map e.toLinearMap =
      A.Vs ⊓ S.weight1.H (1, 0) := by
    rw [Submodule.map_inf _ e.injective, hF, hp, inf_comm]
    rfl
  have hmapN : (F ⊓ Module.End.eigenspace b60_omegaC rp).map e.toLinearMap =
      A.Vsbar ⊓ S.weight1.H (1, 0) := by
    have hneg : -(-rp) = rp := neg_neg rp
    rw [Submodule.map_inf _ e.injective, hF, ← hneg, hn, inf_comm]
    rfl
  have hdimP : Module.finrank ℂ ↥(A.Vs ⊓ S.weight1.H (1, 0)) = 3 := by
    calc
      _ = Module.finrank ℂ ↥((F ⊓ Module.End.eigenspace b60_omegaC (-rp)).map
          e.toLinearMap) := congrArg (fun P : Submodule ℂ _ => Module.finrank ℂ P) hmapP.symm
      _ = Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace b60_omegaC (-rp)) :=
        (e.submoduleMap _).finrank_eq.symm
      _ = 3 := by
        rw [show -(Complex.I * (Real.sqrt 3 : ℂ)) =
          -Complex.I * (Real.sqrt 3 : ℂ) by ring]
        exact (b60_weil_dimensions τ).2
  have hdimN : Module.finrank ℂ ↥(A.Vsbar ⊓ S.weight1.H (1, 0)) = 3 := by
    calc
      _ = Module.finrank ℂ ↥((F ⊓ Module.End.eigenspace b60_omegaC rp).map
          e.toLinearMap) := congrArg (fun P : Submodule ℂ _ => Module.finrank ℂ P) hmapN.symm
      _ = Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace b60_omegaC rp) :=
        (e.submoduleMap _).finrank_eq.symm
      _ = 3 := by simpa [F, rp] using (b60_weil_dimensions τ).1
  refine ⟨hdimP, hdimN, ?_⟩
  unfold HodgeBlocks.WeilAction.IsWeilType
  rw [hdimP]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A.Vs A.Vsbar
  have hc := HodgeBlocks.WeilAction.isCompl_Vs_Vsbar A (by norm_num : (0 : ℚ) < 3)
  have hdim : dim (b60b_model τ).left = 6 := by
    change dim (b60b_univ τ).X.left = 6
    exact b60b_dimension_aux τ
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot,
    add_zero, Module.finrank_baseChange,
    (torusCohomology_cupProductOf (b60b_model τ)).finrank_eq,
    A.finrank_Vsbar_eq_Vs, hdim] at hsum
  omega

theorem b60b_nondegenerate_aux (τ : g32m_Domain) :
    IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol) := by
  exact b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ) (b60b_form_riemann τ)

theorem b60b_rosati_aux (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol) (b60b_univ τ).W.J := by
  exact b60b_rosati_model τ

theorem b60b_polarization_aux (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol) (b60b_univ τ).W.J ∧
    PolarizationPositive (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_nondegenerate_aux τ) := by
  exact ⟨b60b_rosati_aux τ, b60b_polarization_positive τ⟩

theorem b60b_discriminant_aux (τ : g32m_Domain) :
    weilDatumClass (finiteBetti_abelian (b60b_univ τ).X)
      (spec_bettiDeRhamIso_abelian (b60b_univ τ).X)
      (hodgeDecomposition_of_abelian (b60b_univ τ).X)
      (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).W
      (b60b_nondegenerate_aux τ) (b60b_polarization_aux τ).1 = classNegTwo := by
  exact b60_cohomology_weilDetClass τ

theorem b60b_member_aux (τ : g32m_Domain) :
    g32t_IsMember (b60b_univ τ) := by
  refine
    { dim_eq := b60b_dimension_aux τ
      isWeilType := (b60b_signature_aux τ).2.2
      nondegenerate := b60b_nondegenerate_aux τ
      rosati := (b60b_polarization_aux τ).1
      positive := (b60b_polarization_aux τ).2
      datum := b60b_discriminant_aux τ }

theorem b60b_polarization_transport_aux (τ : g32m_Domain) :
    (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
      (b60b_univ τ).pol =
      exteriorPower.map 2 (abelianPeriodEquiv (b60b_univ τ).X).symm.toLinearMap
        (latticeClass (b2_bilinToAddHom (b60b_form τ)))) ∧
    ∀ l m : b2_abelianLattice (b60b_model τ),
      b60b_form τ l m = b5_originalChernPairing b60_Lattice (b60_F τ)
        (b60_weight_one τ) b60_E ((b60_riemann_iff τ).2 τ.property) l m := by
  exact ⟨b60b_polarization_vec_model τ, b60b_original_pairing_model τ⟩

set_option maxHeartbeats 400000 in
theorem b60b_period_aux (τ σ : g32m_Domain) :
    (b60_F σ).map (b2_cplxMap (b60b_marking τ).toAddMonoidHom) =
      b2_abelianF (b60b_univ τ).X ↔ σ = τ := by
  have hτ := b5_period_filtration b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)
  change (b60_F τ).map (b2_cplxMap (b60b_marking τ).toAddMonoidHom) =
    b2_abelianF (b60b_model τ) at hτ
  constructor
  · intro h
    apply Subtype.ext
    apply b60b_marked_filtration_injective τ
    exact h.trans hτ.symm
  · intro hEq
    subst σ
    change (b60_F τ).map (b2_cplxMap (b60b_marking τ).toAddMonoidHom) =
      b2_abelianF (b60b_model τ)
    exact hτ

end HodgeLean.Foundations.Program
