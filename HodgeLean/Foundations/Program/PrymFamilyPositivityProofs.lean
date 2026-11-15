import HodgeLean.Foundations.Program.PrymFamilyPositivityDefs
import HodgeLean.Foundations.Program.UniversalFamilyB60bTransport

/-! # B6-3g, part 4: proof obligations

One auxiliary statement for each public statement of `PrymFamilyPositivity.lean`, each with a
body, and the `b63g4_` helper lemmas they use.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic TopologicalSpace
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

theorem b63g4_contract_eval_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (halt : ∀ l, Q l l = 0) (l : b2_abelianLattice X) :
    contract (polarizationVec (torusCohomology_cupProductOf X)
        (latticeClassHQ X (b2_bilinToAddHom Q))) (b63g4_periodEval X l) =
      b63g4_column X Q l := by
  have hv : polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q)) =
      exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap
        (AppellHumbert.latticeClass (b2_bilinToAddHom Q)) :=
    ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm_apply_apply _
  rw [hv, b2a_contract_map]
  apply (abelianPeriodEquiv X).injective
  ext m
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [b60b_contract_latticeClass_apply _ halt]
  simp [b63g4_periodEval, b63g4_column, b60b_rationalColumn, b2_bilinToAddHom]

theorem b63g4_polarizationForm_column_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (l m : b2_abelianLattice X) :
    polarizationForm (torusCohomology_cupProductOf X) (b2_abelian_nondegenerate X Q hQ)
        (b63g4_column X Q l) (b63g4_column X Q m) = (Q l m : ℚ) := by
  change dualForm (b2_abelian_nondegenerate X Q hQ) _ _ = _
  rw [← b63g4_contract_eval_aux X Q hQ.alt l,
    ← b63g4_contract_eval_aux X Q hQ.alt m, dualForm_contract_contract]
  rw [b63g4_contract_eval_aux X Q hQ.alt]
  simp [b63g4_periodEval, b63g4_column, b2_bilinToAddHom]

theorem b63g4_cplxColumn_tmul (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) (c : ℂ)
    (l : b2_abelianLattice X) :
    b63g4_cplxColumn X Q (c ⊗ₜ l) = c ⊗ₜ b63g4_column X Q l := by
  simp [b63g4_cplxColumn, TensorProduct.smul_tmul']

theorem b63g4_polarizationForm_cplx_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (u v : ℂ ⊗[ℤ] b2_abelianLattice X) :
    (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ
        (b63g4_cplxColumn X Q u) (b63g4_cplxColumn X Q v) =
      Q.baseChange ℂ u v := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | tmul c l =>
    induction v using TensorProduct.inductionOn with
    | add v v' hv hv' => simp only [map_add, hv, hv']
    | tmul d m =>
      rw [b63g4_cplxColumn_tmul, b63g4_cplxColumn_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, b63g4_polarizationForm_column_aux X Q hQ]
      simp [Algebra.smul_def]

theorem b63g4_cplxColumn_conj_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b63g4_cplxColumn X Q (b2_conj _ u) =
      HodgeBlocks.sigmaQ (HQ X 1) (b63g4_cplxColumn X Q u) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => rw [map_add, map_add, hu, hu', map_add, map_add]
  | tmul c l =>
    rw [b2a_conj_tmul, b63g4_cplxColumn_tmul, b63g4_cplxColumn_tmul]
    exact (HodgeBlocks.sigmaQ_tmul _ c _).symm

theorem b63g4_period_cplxColumn (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X) (b63g4_cplxColumn X Q u) =
      b2bpol_musical (b2_abelianLattice X) Q u := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [map_add, hu, hu']
  | tmul c l =>
    rw [b63g4_cplxColumn_tmul, LinearEquiv.baseChange_tmul, b2bpol_musical_tmul]
    congr 1
    ext m
    simp [b60b_periodLinearEquiv, b60b_addHomLinearEquiv, b63g4_column, b2b_flat,
      b2_bilinToAddHom]
    rfl

theorem b63g4_h10_eq_map_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    let := (torusCohomology_cupProductOf X).finite
    (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0) =
      (b2_abelianF X).map (b63g4_cplxColumn X Q) := by
  let := (torusCohomology_cupProductOf X).finite
  have hflat := b2bpol_flat_bijective _ Q (fun u hu ↦ b2_riemannForm_nondegenerate
    (b2_abelianF X) Q (b2_abelianF_isWeightOne X) hQ u hu)
  have hp := b60b_h10_period X
  dsimp only at hp
  rw [b2bpol_hodgeOne_eq_map _ _ Q (b2_abelianF_isWeightOne X) hQ hflat] at hp
  have hm : b2bpol_musical _ Q = (LinearEquiv.baseChange ℚ ℂ _ _
      (b60b_periodLinearEquiv X)).toLinearMap ∘ₗ b63g4_cplxColumn X Q :=
    LinearMap.ext fun u ↦ (b63g4_period_cplxColumn X Q u).symm
  rw [hm, Submodule.map_comp] at hp
  exact Submodule.map_injective_of_injective (LinearEquiv.injective _) hp

theorem b63g4_isotropic_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    let := (torusCohomology_cupProductOf X).finite
    (∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      ∀ y ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x y = 0) ∧
    (∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (0, 1),
      ∀ y ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (0, 1),
      (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x y = 0) := by
  let := (torusCohomology_cupProductOf X).finite
  let S := abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
  have hiso10 : ∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
      (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x y = 0 := by
    intro x hx y hy
    rw [b63g4_h10_eq_map_aux X Q hQ] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [b63g4_polarizationForm_cplx_aux X Q hQ]
    exact hQ.isotropic u hu v hv
  refine ⟨hiso10, ?_⟩
  intro x hx y hy
  have hsx : HodgeBlocks.sigmaQ _ x ∈ S.weight1.H (1, 0) := by
    rw [← S.weight1.conj_symm 0 1]
    exact Submodule.mem_map_of_mem hx
  have hsy : HodgeBlocks.sigmaQ _ y ∈ S.weight1.H (1, 0) := by
    rw [← S.weight1.conj_symm 0 1]
    exact Submodule.mem_map_of_mem hy
  have hz := hiso10 _ hsx _ hsy
  rw [pol1_bilin_conj] at hz
  exact (map_eq_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mp hz

theorem b63g4_h10_positive_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    let := (torusCohomology_cupProductOf X).finite
    ∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      x ≠ 0 →
      0 < (Complex.I * (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x
          (HodgeBlocks.sigmaQ (HQ X 1) x)).re := by
  intro _ x hx hx0
  rw [b63g4_h10_eq_map_aux X Q hQ] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [← b63g4_cplxColumn_conj_aux, b63g4_polarizationForm_cplx_aux X Q hQ]
  exact hQ.positive u hu (by rintro rfl; exact hx0 (map_zero _))

theorem b63g4_abelian_positive_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
      (b2_abelian_nondegenerate X Q hQ) := by
  let := (torusCohomology_cupProductOf X).finite
  exact (pol1_polarisation_iff_h10_positive _ _ (isAlt_polarizationForm _ _)
    (nondegenerate_polarizationForm _ _)
    (fun pq h10 h01 ↦ cohomologyHodgePiece_one_eq_bot X pq h10 h01)
    (b63g4_isotropic_aux X Q hQ).1 (b63g4_isotropic_aux X Q hQ).2).2
    (b63g4_h10_positive_aux X Q hQ)

theorem b63g4_dualForm_neg {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (hn : IsNondegenerate (-ω)) (x y : V) :
    dualForm hn x y = -dualForm hω x y := by
  obtain ⟨φ, rfl⟩ := hω.2 y
  have h : contract (-ω) (-φ) = contract ω φ := by simp
  rw [dualForm_apply, dualForm_apply]
  conv_lhs => rw [← h]
  rw [contractEquiv_symm_contract, contractEquiv_symm_contract]
  rfl

theorem b63g4_neg_not_positive_aux (hdim : 0 < dim X.left)
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    ¬ PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
      (b63g4_neg_nondegenerate X (b2_abelian_nondegenerate X Q hQ)) := by
  let := (torusCohomology_cupProductOf X).finite
  rintro ⟨P, hP⟩
  have hω := b2_abelian_nondegenerate X Q hQ
  let E := polarizationForm (torusCohomology_cupProductOf X) hω
  have hvec : polarizationVec (torusCohomology_cupProductOf X)
      (-latticeClassHQ X (b2_bilinToAddHom Q)) =
      -polarizationVec (torusCohomology_cupProductOf X)
        (latticeClassHQ X (b2_bilinToAddHom Q)) := by
    simp [polarizationVec]
  have hn : IsNondegenerate (-polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q))) :=
    hvec ▸ b63g4_neg_nondegenerate X hω
  have hform : P.form = -E := by
    rw [hP]
    change dualForm (b63g4_neg_nondegenerate X hω) = -dualForm hω
    rw [b60b_dualForm_congr hvec _ hn]
    exact LinearMap.ext₂ fun x y ↦ b63g4_dualForm_neg hω hn x y
  have hneg : (-E).baseChange ℂ = -(E.baseChange ℂ) := by
    ext x y
    simp [LinearMap.BilinForm.baseChange_tmul]
  have hfin := (spec_finrank_cohomologyHodgePiece_one X (hodgeDecomposition_of_abelian X)).1
  rw [← hfin] at hdim
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hdim
  have hx0' : x ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
  have h1 := P.positive 1 0 (by norm_num) x hx hx0'
  have h2 := b63g4_h10_positive_aux X Q hQ x hx hx0'
  rw [hform, hneg] at h1
  simp only [HodgeBlocks.Iexp, sub_zero, zpow_one, LinearMap.neg_apply, mul_neg,
    Complex.neg_re] at h1
  linarith

end HodgeLean.Foundations.Program
