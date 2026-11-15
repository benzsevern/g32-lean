import HodgeLean.Foundations.Program.UniversalFamilyDefs
import HodgeLean.Foundations.Program.PrymFamilyB4Proofs
import HodgeLean.Foundations.Program.RelativeTorusVHSPol

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Foundations.Program

theorem b60b_dualForm_map_equiv {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (e : V ≃ₗ[K] W) {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω)
    (hmap : IsNondegenerate (exteriorPower.map 2 e.toLinearMap ω)) (x y : V) :
    dualForm hmap (e x) (e y) = dualForm hω x y := by
  rw [dualForm_apply, dualForm_apply]
  let ψ := (contractEquiv hω).symm y
  have heq : (contractEquiv hmap).symm (e y) = e.symm.dualMap ψ := by
    apply (contractEquiv hmap).injective
    rw [contractEquiv_apply, contract_contractEquiv_symm]
    change e y = contract (exteriorPower.map 2 e.toLinearMap ω) (e.symm.dualMap ψ)
    symm
    rw [b2a_contract_map]
    change e (contract ω (ψ ∘ₗ e.symm.toLinearMap ∘ₗ e.toLinearMap)) = e y
    have hc : ψ ∘ₗ e.symm.toLinearMap ∘ₗ e.toLinearMap = ψ := by
      ext z
      simp
    rw [hc, show contract ω ψ = y by exact contract_contractEquiv_symm hω y]
  rw [heq]
  change ψ (e.symm (e x)) = _
  rw [e.symm_apply_apply]

theorem b60b_dualForm_congr {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω ω' : ⋀[K]^2 V} (h : ω = ω') (hω : IsNondegenerate ω)
    (hω' : IsNondegenerate ω') : dualForm hω = dualForm hω' := by
  subst ω'
  rfl

def b60b_addHomLinearEquiv (Λ : Type) [AddCommGroup Λ] :
    (Λ →+ ℚ) ≃ₗ[ℚ] b2b_dual Λ where
  toFun f := f.toIntLinearMap
  invFun f := f.toAddMonoidHom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def b60b_periodLinearEquiv
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : HQ X 1 ≃ₗ[ℚ] b2b_dual (b2_abelianLattice X) :=
  (abelianPeriodEquiv X).trans (b60b_addHomLinearEquiv (b2_abelianLattice X))

theorem b60b_h10_period
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    letI := (torusCohomology_cupProductOf X).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian X)
      (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
      (torusCohomology_cupProductOf X)
    (S.weight1.H (1, 0)).map
        (LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)).toLinearMap =
      b2b_hodgeOne (b2_abelianLattice X) (b2_abelianF X) := by
  letI := (torusCohomology_cupProductOf X).finite
  let S := abelianVarietyCohomologyOf (finiteBetti_abelian X)
    (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
    (torusCohomology_cupProductOf X)
  dsimp only [S]
  change (cohomologyHodgePiece X 1 (1, 0)).map
      (LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)).toLinearMap = _
  rw [spec_g4_cohomologyHodgePiece_one_eq X]
  simp only [latticeHodgePieces, if_pos (by norm_num : (1 : ℤ) = 1)]
  have hpair : (b2b_pairing (b2_abelianLattice X)).comp
      (LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)).toLinearMap =
      b2_abelianPairing X := by
    apply LinearMap.ext
    intro u
    induction u using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul c x =>
      apply LinearMap.ext
      intro v
      induction v using TensorProduct.inductionOn with
      | add y z hy hz => rw [map_add, map_add, hy, hz]
      | tmul d l =>
        change c * (d * (((abelianPeriodEquiv X) x l : ℚ) : ℂ)) =
          c * (d * (((abelianPeriodEquiv X) x l : ℚ) : ℂ))
        rfl
  ext z
  simp only [Submodule.mem_map, b2b_hodgeOne, Submodule.mem_comap,
    Submodule.mem_dualAnnihilator]
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    simp only [if_true] at hx
    rw [← b2_abelianHodgeF_eq X] at hy
    change ((b2b_pairing (b2_abelianLattice X)).comp
      (LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)).toLinearMap) x y = 0
    rw [hpair]
    have hx' : x ∈ (abelianWeightOneHodgeStructure X).H (1, 0) := by
      change x ∈ cohomologyHodgePiece X 1 (1, 0)
      rw [spec_g4_cohomologyHodgePiece_one_eq X]
      simpa [latticeHodgePieces] using hx
    exact (Submodule.mem_dualCoannihilator _).1 hy _ (Submodule.mem_map_of_mem hx')
  · intro hz
    let e := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv X)
    have heqpair : b2b_pairing (b2_abelianLattice X) z =
        b2_abelianPairing X (e.symm z) := by
      rw [← hpair]
      change b2b_pairing (b2_abelianLattice X) z =
        b2b_pairing (b2_abelianLattice X) (e (e.symm z))
      rw [e.apply_symm_apply]
    have hz' : b2_abelianPairing X (e.symm z) ∈
        (b2_abelianHodgeF X).dualAnnihilator := by
      rw [← heqpair, b2_abelianHodgeF_eq X]
      exact (Submodule.mem_dualAnnihilator _).2 hz
    rw [b2_abelianHodgeF, Subspace.dualCoannihilator_dualAnnihilator_eq] at hz'
    obtain ⟨x, hx, hxeq⟩ := hz'
    have hPinj : Function.Injective (b2_abelianPairing X) := by
      rw [← hpair]
      exact (b2bpol_pairing_bijective (b2_abelianLattice X)).1.comp e.injective
    have hxval : x = e.symm z := hPinj hxeq
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rw [← hxval]
    have hx' : x ∈ cohomologyHodgePiece X 1 (1, 0) := hx
    rw [spec_g4_cohomologyHodgePiece_one_eq X] at hx'
    simpa [latticeHodgePieces] using hx'

theorem b60b_lattice_finrank : Module.finrank ℤ b60_Lattice = 12 := by
  simp [b60_Lattice]

theorem b60b_action_model (τ : g32m_Domain) (v : HQ (b60b_model τ) 1)
    (l : b60_Lattice) :
    abelianPeriodEquiv (b60b_model τ) (b60b_J τ v) (b60b_marking τ l) =
      abelianPeriodEquiv (b60b_model τ) v (b60b_marking τ (b60_omega l)) := by
  change abelianPeriodEquiv (b60b_model τ)
      (b4b_cohomologyAction b60_Lattice (b60b_model τ) (b60b_marking τ)
        b60_omega.toAddMonoidHom v) (b60b_marking τ l) = _
  simp only [b4b_cohomologyAction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  change abelianPeriodEquiv (b60b_model τ) v
      (b60b_marking τ (b60_omega ((b60b_marking τ).symm (b60b_marking τ l)))) = _
  rw [AddEquiv.symm_apply_apply]

theorem b60b_form_riemann (τ : g32m_Domain) :
    b2_IsRiemannForm (b2_abelianLattice (b60b_model τ)) (b2_abelianF (b60b_model τ))
      (b60b_form τ) := by
  apply b4b_transportForm_riemann_aux b60_Lattice (b60b_model τ) (b60b_marking τ)
    (b60_F τ)
  · exact b5_period_filtration _ _ (b60_weight_one τ) _
      ((b60_riemann_iff τ).2 τ.property)
  · exact (b60_riemann_iff τ).2 τ.property

theorem b60b_latticeClass_nondegenerate (τ : g32m_Domain) :
    IsNondegenerate (latticeClass (b2_bilinToAddHom (b60b_form τ))) := by
  obtain ⟨H, hH, hE⟩ := (b2_abelian_isRiemannForm_iff (b60b_model τ)
    (b60b_form τ)).1 (b60b_form_riemann τ)
  exact latticeClassHQ_latticeClass_nondegenerate
    (abelianPeriodLattice (b60b_model τ)) H hH _ hE

theorem b60b_marking_F (τ : g32m_Domain) :
    (b60_F τ).map (b2_cplxMap (b60b_marking τ).toAddMonoidHom) =
      b2_abelianF (b60b_model τ) := by
  exact b5_period_filtration _ _ (b60_weight_one τ) _
    ((b60_riemann_iff τ).2 τ.property)

noncomputable def b60b_homologyCohomologyEquiv (τ : g32m_Domain) :
    TensorProduct ℤ ℂ b60_Lattice ≃ₗ[ℂ]
      TensorProduct ℚ ℂ (HQ (b60b_model τ) 1) :=
  let em := LinearEquiv.baseChange ℤ ℂ _ _ (b60b_marking τ).toIntLinearEquiv
  let hflat := b2bpol_flat_bijective (b2_abelianLattice (b60b_model τ)) (b60b_form τ)
    (fun u hu ↦ b2_riemannForm_nondegenerate (b2_abelianF (b60b_model τ))
      (b60b_form τ) (b2_abelianF_isWeightOne (b60b_model τ))
      (b60b_form_riemann τ) u hu)
  let emus := LinearEquiv.ofBijective
    (b2bpol_musical (b2_abelianLattice (b60b_model τ)) (b60b_form τ))
    (b2bpol_musical_bijective (b2_abelianLattice (b60b_model τ)) (b60b_form τ) hflat)
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv (b60b_model τ))
  em.trans (emus.trans ep.symm)

def b60b_dualPrecomp {Λ : Type} [AddCommGroup Λ] (J : Λ →+ Λ) :
    b2b_dual Λ →ₗ[ℚ] b2b_dual Λ where
  toFun f :=
    { toFun := fun x ↦ f (J x)
      map_add' := by simp
      map_smul' := by intro n x; simp }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem b60b_musical_skew {Λ : Type} [AddCommGroup Λ]
    (Q : LinearMap.BilinForm ℤ Λ) (J : Λ →+ Λ)
    (hskew : ∀ x y, Q (J x) y = -Q x (J y))
    (x : TensorProduct ℤ ℂ Λ) :
    b2bpol_musical Λ Q (b2_cplxMap J x) =
      -(b60b_dualPrecomp J).baseChange ℂ (b2bpol_musical Λ Q x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | tmul c u =>
      rw [b2_cplxMap, LinearMap.baseChange_tmul]
      rw [b2bpol_musical_tmul, b2bpol_musical_tmul]
      rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_neg]
      congr 1
      ext v
      simp [b2b_flat, b60b_dualPrecomp, hskew]

theorem b60b_marking_intertwines_action (τ : g32m_Domain)
    (x : TensorProduct ℤ ℂ b60_Lattice) :
    (LinearEquiv.baseChange ℤ ℂ _ _ (b60b_marking τ).toIntLinearEquiv)
        (b60_omegaC x) =
      b2_cplxMap ((b60b_marking τ).toAddMonoidHom.comp
        (b60_omega.toAddMonoidHom.comp (b60b_marking τ).symm.toAddMonoidHom))
        ((LinearEquiv.baseChange ℤ ℂ _ _
          (b60b_marking τ).toIntLinearEquiv) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c u =>
      simp only [b60_omegaC, LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
        b2_cplxMap]
      congr 1
      change b60b_marking τ (b60_omega u) =
        b60b_marking τ (b60_omega ((b60b_marking τ).symm (b60b_marking τ u)))
      rw [(b60b_marking τ).symm_apply_apply]

theorem b60b_period_intertwines_action (τ : g32m_Domain)
    (x : TensorProduct ℚ ℂ (HQ (b60b_model τ) 1)) :
    (LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv (b60b_model τ)))
        ((b60b_J τ).baseChange ℂ x) =
      (b60b_dualPrecomp ((b60b_marking τ).toAddMonoidHom.comp
        (b60_omega.toAddMonoidHom.comp (b60b_marking τ).symm.toAddMonoidHom))).baseChange ℂ
        ((LinearEquiv.baseChange ℚ ℂ _ _
          (b60b_periodLinearEquiv (b60b_model τ))) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
      congr 1
      ext l
      change abelianPeriodEquiv (b60b_model τ) (b60b_J τ v) l =
        abelianPeriodEquiv (b60b_model τ) v
          (b60b_marking τ (b60_omega ((b60b_marking τ).symm l)))
      unfold b60b_J b4b_cohomologyAction
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      rfl

theorem b60b_homologyCohomology_intertwines (τ : g32m_Domain)
    (x : TensorProduct ℤ ℂ b60_Lattice) :
    b60b_homologyCohomologyEquiv τ (b60_omegaC x) =
      -(b60b_J τ).baseChange ℂ (b60b_homologyCohomologyEquiv τ x) := by
  let em := LinearEquiv.baseChange ℤ ℂ _ _ (b60b_marking τ).toIntLinearEquiv
  let hflat := b2bpol_flat_bijective (b2_abelianLattice (b60b_model τ)) (b60b_form τ)
    (fun u hu ↦ b2_riemannForm_nondegenerate (b2_abelianF (b60b_model τ))
      (b60b_form τ) (b2_abelianF_isWeightOne (b60b_model τ))
      (b60b_form_riemann τ) u hu)
  let emus := LinearEquiv.ofBijective
    (b2bpol_musical (b2_abelianLattice (b60b_model τ)) (b60b_form τ))
    (b2bpol_musical_bijective (b2_abelianLattice (b60b_model τ)) (b60b_form τ) hflat)
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv (b60b_model τ))
  let J := (b60b_marking τ).toAddMonoidHom.comp
    (b60_omega.toAddMonoidHom.comp (b60b_marking τ).symm.toAddMonoidHom)
  have hskew (u v : b2_abelianLattice (b60b_model τ)) :
      b60b_form τ (J u) v = -b60b_form τ u (J v) := by
    dsimp only [J, b60b_form, b4b_transportForm, LinearMap.compl₁₂_apply,
      AddMonoidHom.comp_apply]
    change b60_E ((b60b_marking τ).symm
        (b60b_marking τ (b60_omega ((b60b_marking τ).symm u))))
        ((b60b_marking τ).symm v) =
      -b60_E ((b60b_marking τ).symm u) ((b60b_marking τ).symm
        (b60b_marking τ (b60_omega ((b60b_marking τ).symm v))))
    rw [(b60b_marking τ).symm_apply_apply, (b60b_marking τ).symm_apply_apply]
    simp only [b60_E, b60_omega, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    fin_cases i <;> norm_num [b60_diag] <;> ring
  have hep (y : TensorProduct ℚ ℂ (b2b_dual (b2_abelianLattice (b60b_model τ)))) :
      ep.symm ((b60b_dualPrecomp J).baseChange ℂ y) =
        (b60b_J τ).baseChange ℂ (ep.symm y) := by
    dsimp only [J]
    have h := b60b_period_intertwines_action τ (ep.symm y)
    change ep ((b60b_J τ).baseChange ℂ (ep.symm y)) =
      (b60b_dualPrecomp _).baseChange ℂ (ep (ep.symm y)) at h
    rw [ep.apply_symm_apply] at h
    apply ep.injective
    rw [ep.apply_symm_apply]
    exact h.symm
  change ep.symm (b2bpol_musical _ _ (em (b60_omegaC x))) =
    -(b60b_J τ).baseChange ℂ (ep.symm (b2bpol_musical _ _ (em x)))
  rw [b60b_marking_intertwines_action τ]
  change ep.symm (b2bpol_musical _ _ (b2_cplxMap J (em x))) = _
  rw [b60b_musical_skew _ J hskew, map_neg, hep]

theorem b60b_map_eigenspace (τ : g32m_Domain) (r : ℂ) :
    (Module.End.eigenspace b60_omegaC (-r)).map
        (b60b_homologyCohomologyEquiv τ).toLinearMap =
      Module.End.eigenspace ((b60b_J τ).baseChange ℂ) r := by
  ext y
  simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hi := b60b_homologyCohomology_intertwines τ x
    rw [hx, map_smul] at hi
    apply neg_injective
    change -(b60b_J τ).baseChange ℂ (b60b_homologyCohomologyEquiv τ x) =
      -(r • b60b_homologyCohomologyEquiv τ x)
    simpa only [neg_smul, neg_neg] using hi.symm
  · intro hy
    refine ⟨(b60b_homologyCohomologyEquiv τ).symm y, ?_,
      (b60b_homologyCohomologyEquiv τ).apply_symm_apply y⟩
    apply (b60b_homologyCohomologyEquiv τ).injective
    have hi := b60b_homologyCohomology_intertwines τ
      ((b60b_homologyCohomologyEquiv τ).symm y)
    rw [(b60b_homologyCohomologyEquiv τ).apply_symm_apply] at hi
    rw [hi, map_smul, (b60b_homologyCohomologyEquiv τ).apply_symm_apply, hy]
    simp only [neg_smul, neg_neg]

set_option maxHeartbeats 400000 in
theorem b60b_homologyCohomology_F (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_model τ)).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
      (spec_bettiDeRhamIso_abelian (b60b_model τ))
      (hodgeDecomposition_of_abelian (b60b_model τ))
      (torusCohomology_cupProductOf (b60b_model τ))
    (b60_F τ).map (b60b_homologyCohomologyEquiv τ).toLinearMap = S.weight1.H (1, 0) := by
  letI := (torusCohomology_cupProductOf (b60b_model τ)).finite
  let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
    (spec_bettiDeRhamIso_abelian (b60b_model τ))
    (hodgeDecomposition_of_abelian (b60b_model τ))
    (torusCohomology_cupProductOf (b60b_model τ))
  let em := LinearEquiv.baseChange ℤ ℂ _ _ (b60b_marking τ).toIntLinearEquiv
  let hflat := b2bpol_flat_bijective (b2_abelianLattice (b60b_model τ)) (b60b_form τ)
    (fun u hu ↦ b2_riemannForm_nondegenerate (b2_abelianF (b60b_model τ))
      (b60b_form τ) (b2_abelianF_isWeightOne (b60b_model τ))
      (b60b_form_riemann τ) u hu)
  let emus := LinearEquiv.ofBijective
    (b2bpol_musical (b2_abelianLattice (b60b_model τ)) (b60b_form τ))
    (b2bpol_musical_bijective (b2_abelianLattice (b60b_model τ)) (b60b_form τ) hflat)
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv (b60b_model τ))
  dsimp only [S]
  rw [show b60b_homologyCohomologyEquiv τ = em.trans (emus.trans ep.symm) by rfl]
  change (b60_F τ).map
    (ep.symm.toLinearMap.comp (emus.toLinearMap.comp em.toLinearMap)) = _
  rw [Submodule.map_comp, Submodule.map_comp]
  change (((b60_F τ).map em.toLinearMap).map emus.toLinearMap).map
    ep.symm.toLinearMap = _
  have hmark : (b60_F τ).map em.toLinearMap = b2_abelianF (b60b_model τ) := by
    change (b60_F τ).map (b2_cplxMap (b60b_marking τ).toAddMonoidHom) = _
    exact b60b_marking_F τ
  rw [hmark]
  have hmus := b2bpol_hodgeOne_eq_map (b2_abelianLattice (b60b_model τ))
    (b2_abelianF (b60b_model τ)) (b60b_form τ)
    (b2_abelianF_isWeightOne (b60b_model τ)) (b60b_form_riemann τ) hflat
  change ((b2_abelianF (b60b_model τ)).map
    (b2bpol_musical (b2_abelianLattice (b60b_model τ)) (b60b_form τ))).map
      ep.symm.toLinearMap = _
  rw [← hmus]
  have hp := b60b_h10_period (b60b_model τ)
  change (S.weight1.H (1, 0)).map ep.toLinearMap = _ at hp
  rw [← hp, ← Submodule.map_comp]
  have hc : ep.symm.toLinearMap.comp ep.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact ep.symm_apply_apply x
  rw [hc, Submodule.map_id]

theorem b60b_polarization_vec_model (τ : g32m_Domain) :
    polarizationVec (torusCohomology_cupProductOf (b60b_model τ)) (b60b_pol τ) =
      exteriorPower.map 2 (abelianPeriodEquiv (b60b_model τ)).symm.toLinearMap
        (latticeClass (b2_bilinToAddHom (b60b_form τ))) := by
  exact ((torusCohomology_cupProductOf (b60b_model τ)).cupWedgeEquiv 2).symm_apply_apply _

theorem b60b_original_pairing_model (τ : g32m_Domain)
    (l m : b2_abelianLattice (b60b_model τ)) :
    b60b_form τ l m = b5_originalChernPairing b60_Lattice (b60_F τ)
      (b60_weight_one τ) b60_E ((b60_riemann_iff τ).2 τ.property) l m := by
  let x := (b60b_marking τ).symm l
  let y := (b60b_marking τ).symm m
  calc
    b60b_form τ l m = b60_E x y := rfl
    _ = b5_originalChernPairing b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
        ((b60_riemann_iff τ).2 τ.property) (b60b_marking τ x) (b60b_marking τ y) :=
      (b5_polarization_normalized _ _ (b60_weight_one τ) _
        ((b60_riemann_iff τ).2 τ.property) x y).symm
    _ = _ := by rw [(b60b_marking τ).apply_symm_apply, (b60b_marking τ).apply_symm_apply]

theorem b60_E_omega_skew (x y : b60_Lattice) :
    b60_E (b60_omega x) y = -b60_E x (b60_omega y) := by
  simp only [b60_E, b60_omega, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases i <;> norm_num [b60_diag] <;> ring

def b60b_rationalColumn {Λ : Type*} [AddCommGroup Λ]
    (E : Λ →+ Λ →+ ℤ) : Λ →ₗ[ℤ] (Λ →+ ℚ) where
  toFun x := (Int.castAddHom ℚ).comp
    { toFun := fun y ↦ E y x
      map_zero' := by simp
      map_add' := by simp }
  map_add' x y := by ext; simp
  map_smul' n x := by ext; simp

theorem b60b_contract_latticeClass_apply {Λ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : Λ →+ Λ →+ ℤ)
    (hE : ∀ x, E x x = 0) (ψ : Module.Dual ℚ (Λ →+ ℚ)) (x : Λ) :
    contract (latticeClass E) ψ x = ψ (b60b_rationalColumn E x) := by
  let b := Module.Free.chooseBasis ℤ Λ
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [contract_latticeClass_apply_of_alt E hE]
  conv_rhs => rw [← (latticeDualBasisQ (Λ := Λ)).sum_repr (b60b_rationalColumn E (b i))]
  rw [map_sum]
  simp [b, b60b_rationalColumn, latticeDualBasisQ, latticeDualEquiv, latticeDualBasisQ_apply,
    mul_comm]

def b60b_integralEvaluation (Λ : Type) [AddCommGroup Λ] :
    Λ →ₗ[ℤ] Module.Dual ℚ (Λ →+ ℚ) where
  toFun x :=
    { toFun := fun f => f x
      map_add' := by intro f g; simp
      map_smul' := by intro c f; simp }
  map_add' x y := by ext f; simp
  map_smul' n x := by ext f; simp

def b60b_rationalEvaluation (Λ : Type) [AddCommGroup Λ] :
    ℚ ⊗[ℤ] Λ →ₗ[ℚ] Module.Dual ℚ (Λ →+ ℚ) :=
  LinearMap.liftBaseChange ℚ (b60b_integralEvaluation Λ)

@[simp] theorem b60b_rationalEvaluation_tmul (Λ : Type) [AddCommGroup Λ]
    (q : ℚ) (x : Λ) (f : Λ →+ ℚ) :
    b60b_rationalEvaluation Λ (q ⊗ₜ[ℤ] x) f = q * f x := by
  simp [b60b_rationalEvaluation, b60b_integralEvaluation]

theorem b60b_dualForm_latticeClass (Λ : Type) [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : ∀ x, Q x x = 0)
    (hflat : Function.Bijective (b2b_flat Λ Q))
    (hlat : IsNondegenerate (latticeClass (b2_bilinToAddHom Q)))
    (φ ψ : Λ →+ ℚ) :
    dualForm hlat φ ψ = b2b_dualForm Λ Q
      (b60b_addHomLinearEquiv Λ φ) (b60b_addHomLinearEquiv Λ ψ) := by
  obtain ⟨a, ha⟩ := hflat.2 (b60b_addHomLinearEquiv Λ φ)
  obtain ⟨b, hb⟩ := hflat.2 (b60b_addHomLinearEquiv Λ ψ)
  have ha' : φ = (b60b_addHomLinearEquiv Λ).symm (b2b_flat Λ Q a) := by
    apply (b60b_addHomLinearEquiv Λ).injective
    simpa using ha.symm
  have hb' : ψ = (b60b_addHomLinearEquiv Λ).symm (b2b_flat Λ Q b) := by
    apply (b60b_addHomLinearEquiv Λ).injective
    simpa using hb.symm
  rw [ha', hb']
  have heval (u v : ℚ ⊗[ℤ] Λ) :
      b60b_rationalEvaluation Λ v
          ((b60b_addHomLinearEquiv Λ).symm (b2b_flat Λ Q u)) =
        Q.baseChange ℚ u v := by
    induction u using TensorProduct.inductionOn with
    | add u w hu hw => simp only [map_add, hu, hw, LinearMap.add_apply]
    | tmul q x =>
      induction v using TensorProduct.inductionOn with
      | add v w hv hw => simp only [map_add, hv, hw, LinearMap.add_apply]
      | tmul r y =>
        simp only [b60b_rationalEvaluation_tmul, LinearMap.BilinForm.baseChange_tmul,
          b2b_flat, LinearMap.liftBaseChange_tmul]
        rw [map_smul]
        rw [show (q • (b60b_addHomLinearEquiv Λ).symm
          ((LinearMap.compr₂ Q (Algebra.linearMap ℤ ℚ)) x)) y =
            q * ((b60b_addHomLinearEquiv Λ).symm
              ((LinearMap.compr₂ Q (Algebra.linearMap ℤ ℚ)) x)) y by rfl]
        change r * (q * ((b60b_addHomLinearEquiv Λ).symm
          ((LinearMap.compr₂ Q (Algebra.linearMap ℤ ℚ)) x)) y) = (Q x y : ℚ) * (q * r)
        have hv : ((b60b_addHomLinearEquiv Λ).symm
            ((LinearMap.compr₂ Q (Algebra.linearMap ℤ ℚ)) x)) y = (Q x y : ℚ) := rfl
        rw [hv]
        ring
  have hcontract (u : ℚ ⊗[ℤ] Λ) :
      contract (latticeClass (b2_bilinToAddHom Q)) (b60b_rationalEvaluation Λ u) =
        (b60b_addHomLinearEquiv Λ).symm (b2b_flat Λ Q u) := by
    apply AddMonoidHom.ext
    intro x
    induction u using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, AddMonoidHom.add_apply, hu, hv]
    | tmul q y =>
      rw [b60b_contract_latticeClass_apply (b2_bilinToAddHom Q) hQ]
      change q * (((Int.castAddHom ℚ).comp
        { toFun := fun z => Q z x, map_zero' := by simp, map_add' := by simp }) y) =
          q * (Q y x : ℚ)
      congr 1
  simp only [(b60b_addHomLinearEquiv Λ).apply_symm_apply]
  rw [← hcontract a, ← hcontract b, dualForm_contract_contract,
    b2bpol_dualForm_flat Λ Q hflat]
  rw [hcontract a]
  exact heval a b

theorem b60b_polarizationForm_period (τ : g32m_Domain) (x y : HQ (b60b_model τ) 1) :
    polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
        (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
          (b60b_form_riemann τ)) x y =
      b2b_dualForm (b2_abelianLattice (b60b_model τ)) (b60b_form τ)
        (b60b_periodLinearEquiv (b60b_model τ) x)
        (b60b_periodLinearEquiv (b60b_model τ) y) := by
  letI : FiniteDimensional ℚ (b2_abelianLattice (b60b_model τ) →+ ℚ) :=
    Module.Finite.of_basis latticeDualBasisQ
  let ep := (abelianPeriodEquiv (b60b_model τ)).symm
  have hmap := b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
    (b60b_form_riemann τ)
  change IsNondegenerate (polarizationVec
    (torusCohomology_cupProductOf (b60b_model τ)) (b60b_pol τ)) at hmap
  rw [b60b_polarization_vec_model] at hmap
  have hdual := b60b_dualForm_map_equiv ep (b60b_latticeClass_nondegenerate τ)
    hmap (abelianPeriodEquiv (b60b_model τ) x)
      (abelianPeriodEquiv (b60b_model τ) y)
  have hdual' : dualForm hmap x y = dualForm (b60b_latticeClass_nondegenerate τ)
      (abelianPeriodEquiv (b60b_model τ) x) (abelianPeriodEquiv (b60b_model τ) y) := by
    simpa [ep] using hdual
  change dualForm (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
    (b60b_form_riemann τ)) x y = _
  have heq : dualForm (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
      (b60b_form_riemann τ)) = dualForm hmap :=
    b60b_dualForm_congr (b60b_polarization_vec_model τ)
      (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ) (b60b_form_riemann τ)) hmap
  calc
    _ = dualForm hmap x y := by rw [heq]
    _ = _ := by
      rw [hdual']
      exact b60b_dualForm_latticeClass _ _ (b60b_form_riemann τ).alt
        (b2bpol_flat_bijective _ _ (fun u hu ↦ b2_riemannForm_nondegenerate
          (b2_abelianF (b60b_model τ)) (b60b_form τ)
          (b2_abelianF_isWeightOne (b60b_model τ)) (b60b_form_riemann τ) u hu))
        (b60b_latticeClass_nondegenerate τ) _ _

theorem b60b_polarizationForm_period_complex (τ : g32m_Domain)
    (x y : ℂ ⊗[ℚ] HQ (b60b_model τ) 1) :
    (polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
      (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
        (b60b_form_riemann τ))).baseChange ℂ x y =
    (b2b_dualForm (b2_abelianLattice (b60b_model τ)) (b60b_form τ)).baseChange ℂ
      ((LinearEquiv.baseChange ℚ ℂ _ _
        (b60b_periodLinearEquiv (b60b_model τ))) x)
      ((LinearEquiv.baseChange ℚ ℂ _ _
        (b60b_periodLinearEquiv (b60b_model τ))) y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul c x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul d y =>
      simp only [LinearMap.BilinForm.baseChange_tmul, LinearEquiv.baseChange_tmul]
      rw [b60b_polarizationForm_period]

theorem b60b_polarization_positive (τ : g32m_Domain) :
    PolarizationPositive (finiteBetti_abelian (b60b_model τ))
      (spec_bettiDeRhamIso_abelian (b60b_model τ))
      (hodgeDecomposition_of_abelian (b60b_model τ))
      (torusCohomology_cupProductOf (b60b_model τ))
      (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
        (b60b_form_riemann τ)) := by
  let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
    (spec_bettiDeRhamIso_abelian (b60b_model τ))
    (hodgeDecomposition_of_abelian (b60b_model τ))
    (torusCohomology_cupProductOf (b60b_model τ))
  let E := polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
    (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
      (b60b_form_riemann τ))
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv (b60b_model τ))
  have hpol := b2bpol_dualForm_isPolarized (b2_abelianLattice (b60b_model τ))
    (b2_abelianF (b60b_model τ)) (b60b_form τ)
    (b2_abelianF_isWeightOne (b60b_model τ)) (b60b_form_riemann τ)
  have hmem {x : ℂ ⊗[ℚ] HQ (b60b_model τ) 1} (hx : x ∈ S.weight1.H (1, 0)) :
      ep x ∈ b2b_hodgeOne (b2_abelianLattice (b60b_model τ))
        (b2_abelianF (b60b_model τ)) := by
    rw [← b60b_h10_period (b60b_model τ)]
    exact Submodule.mem_map_of_mem hx
  have hiso10 : ∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
      E.baseChange ℂ x y = 0 := by
    intro x hx y hy
    rw [b60b_polarizationForm_period_complex]
    exact hpol.riemann_first 1 _ (by simpa [b2bpol_filtration_one] using hmem hx)
      _ (by simpa [b2bpol_filtration_one] using hmem hy)
  have hiso01 : ∀ x ∈ S.weight1.H (0, 1), ∀ y ∈ S.weight1.H (0, 1),
      E.baseChange ℂ x y = 0 := by
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
  apply (pol1_polarisation_iff_h10_positive S.weight1 E
    (isAlt_polarizationForm _ _) (nondegenerate_polarizationForm _ _)
    (fun pq h10 h01 ↦ by
      dsimp only [S]
      exact cohomologyHodgePiece_one_eq_bot (b60b_model τ) pq h10 h01)
    hiso10 hiso01).2
  intro x hx hx0
  rw [b60b_polarizationForm_period_complex]
  have hepsigma : ep (HodgeBlocks.sigmaQ _ x) = HodgeBlocks.sigmaQ _ (ep x) := by
    exact HodgeBlocks.QHodgeStructure.complexificationCongr_sigmaQR
      (V := HQ (b60b_model τ) 1)
      (W := b2b_dual (b2_abelianLattice (b60b_model τ)))
      (b60b_periodLinearEquiv (b60b_model τ)) x
  rw [hepsigma]
  simpa only [HodgeBlocks.Iexp, sub_zero, zpow_one] using
    hpol.riemann_second 1 0 (by norm_num) (ep x) (by
      change ep x ∈ b2b_filtration _ (b2_abelianF (b60b_model τ)) 1 ⊓
        (b2b_filtration _ (b2_abelianF (b60b_model τ)) 0).map
          (HodgeBlocks.sigmaQ _)
      constructor
      · simpa [b2bpol_filtration_one] using hmem hx
      · refine ⟨HodgeBlocks.sigmaQ _ (ep x), ?_, ?_⟩
        · simp [b2bpol_filtration_of_le_zero]
        · exact HodgeBlocks.sigmaQR_involutive _ _) (ep.injective.ne hx0)

theorem b60b_latticeClass_action {Λ : Type} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : Λ →+ Λ →+ ℤ)
    (hE : ∀ x, E x x = 0) (J : Λ →+ Λ) (d : ℤ)
    (hJ : ∀ x, J (J x) = -d • x)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    exteriorPower.map 2 (b4b_periodPrecomp Λ J) (latticeClass E) =
      (d : ℚ) • latticeClass E := by
  letI : FiniteDimensional ℚ (Λ →+ ℚ) := Module.Finite.of_basis latticeDualBasisQ
  rw [← contract_injective.eq_iff, contract_map, map_smul]
  ext ψ x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
  change contract (latticeClass E) ((b4b_periodPrecomp Λ J).dualMap ψ) (J x) =
    (d : ℚ) * contract (latticeClass E) ψ x
  rw [b60b_contract_latticeClass_apply E hE,
    b60b_contract_latticeClass_apply E hE]
  simp only [LinearMap.dualMap_apply, b4b_periodPrecomp]
  calc
    ψ ((b4b_periodPrecomp Λ J) (b60b_rationalColumn E (J x))) =
        ψ ((d : ℚ) • b60b_rationalColumn E x) := by
      apply congrArg ψ
      ext y
      change ((E (J y) (J x) : ℤ) : ℚ) = (d : ℚ) * (E y x : ℤ)
      rw [hskew, hJ]
      simp only [map_zsmul, zsmul_eq_mul]
      exact_mod_cast (show -((-d) * E y x) = d * E y x by ring)
    _ = (d : ℚ) * ψ (b60b_rationalColumn E x) := by rw [map_smul]; rfl

theorem b60_latticeClass_action :
    exteriorPower.map 2
        (b4b_periodPrecomp b60_Lattice b60_omega.toAddMonoidHom)
        (latticeClass (b2_bilinToAddHom b60_E)) =
      (3 : ℚ) • latticeClass (b2_bilinToAddHom b60_E) := by
  apply b60b_latticeClass_action (b2_bilinToAddHom b60_E)
    (by
      intro x
      simp [b2_bilinToAddHom, b60_E]
      apply Finset.sum_eq_zero
      intro i hi
      ring) b60_omega.toAddMonoidHom 3
  · intro x
    exact LinearMap.congr_fun b60_omega_square x
  · exact b60_E_omega_skew

theorem b60b_transported_latticeClass_action (τ : g32m_Domain) :
    let J := (b60b_marking τ).toAddMonoidHom.comp
      (b60_omega.toAddMonoidHom.comp (b60b_marking τ).symm.toAddMonoidHom)
    exteriorPower.map 2 (b4b_periodPrecomp _ J)
        (latticeClass (b2_bilinToAddHom (b60b_form τ))) =
      (3 : ℚ) • latticeClass (b2_bilinToAddHom (b60b_form τ)) := by
  apply b60b_latticeClass_action (b2_bilinToAddHom (b60b_form τ))
    (b60b_form_riemann τ).alt _ 3
  · intro x
    simp only [AddMonoidHom.comp_apply]
    change b60b_marking τ
      (b60_omega ((b60b_marking τ).symm (b60b_marking τ
        (b60_omega ((b60b_marking τ).symm x))))) = -3 • x
    rw [(b60b_marking τ).symm_apply_apply]
    have h := LinearMap.congr_fun b60_omega_square ((b60b_marking τ).symm x)
    change b60_omega (b60_omega ((b60b_marking τ).symm x)) =
      -3 • (b60b_marking τ).symm x at h
    rw [h, map_zsmul, (b60b_marking τ).apply_symm_apply]
  · intro x y
    simp only [AddMonoidHom.comp_apply]
    change b60_E ((b60b_marking τ).symm (b60b_marking τ
        (b60_omega ((b60b_marking τ).symm x)))) ((b60b_marking τ).symm y) =
      -b60_E ((b60b_marking τ).symm x) ((b60b_marking τ).symm (b60b_marking τ
        (b60_omega ((b60b_marking τ).symm y))))
    rw [(b60b_marking τ).symm_apply_apply, (b60b_marking τ).symm_apply_apply]
    exact b60_E_omega_skew _ _

set_option maxHeartbeats 400000 in
theorem b60b_polarization_action (τ : g32m_Domain) :
    exteriorPower.map 2 (b60b_J τ)
        (polarizationVec (torusCohomology_cupProductOf (b60b_model τ)) (b60b_pol τ)) =
      (3 : ℚ) • polarizationVec
        (torusCohomology_cupProductOf (b60b_model τ)) (b60b_pol τ) := by
  rw [b60b_polarization_vec_model]
  unfold b60b_J b4b_cohomologyAction
  rw [exteriorPower.map_comp, LinearMap.comp_apply,
    exteriorPower.map_comp, LinearMap.comp_apply]
  have hcancel :
      exteriorPower.map 2 (abelianPeriodEquiv (b60b_model τ)).toLinearMap
          (exteriorPower.map 2 (abelianPeriodEquiv (b60b_model τ)).symm.toLinearMap
            (latticeClass (b2_bilinToAddHom (b60b_form τ)))) =
        latticeClass (b2_bilinToAddHom (b60b_form τ)) := by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    simp
  rw [hcancel]
  rw [b60b_transported_latticeClass_action, map_smul]

theorem b60b_rosati_model (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_model τ)).finite
    IsRosatiSkew
      (polarizationVec (torusCohomology_cupProductOf (b60b_model τ)) (b60b_pol τ))
      (b60b_J τ) := by
  let hω := b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ) (b60b_form_riemann τ)
  have hJ : b60b_J τ ∘ₗ b60b_J τ = (-3 : ℚ) • LinearMap.id := by
    apply b4b_action_sq_aux
    intro l
    exact LinearMap.congr_fun b60_omega_square l
  exact ((isRosatiSkew_iff (torusCohomology_cupProductOf (b60b_model τ)) hω
    (by norm_num : (3 : ℚ) ≠ 0) hJ).1).1
      (b60b_polarization_action τ)

theorem b60_frame_neg_leading (z : Fin 9 → ℂ) (p : Fin 2 × Fin 3) (i : Fin 3) :
    (b60_basis.repr (b60_frame z p) (Fin.castAdd 3 i, 0) -
      (Complex.I * (Real.sqrt 3 : ℂ)) *
        b60_basis.repr (b60_frame z p) (Fin.castAdd 3 i, 1)) / 2 =
      if p.1 = 0 ∧ p.2 = i then 1 else 0 := by
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [b60_frame, Fin.sum_univ_succ, b60_eigen_coord] <;>
    field_simp [hs, Complex.I_ne_zero] <;> ring_nf <;> simp [Complex.I_sq]

theorem b60_frame_neg_trailing (z : Fin 9 → ℂ) (p : Fin 2 × Fin 3) (j : Fin 3) :
    (b60_basis.repr (b60_frame z p) (Fin.natAdd 3 j, 0) -
      (Complex.I * (Real.sqrt 3 : ℂ)) *
        b60_basis.repr (b60_frame z p) (Fin.natAdd 3 j, 1)) / 2 =
      if p.1 = 0 then g32m_toMat z j p.2 *
        (if (Fin.natAdd 3 j : Fin 6) = 5 then (Real.sqrt 2 : ℂ)⁻¹ else 1) else 0 := by
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases j <;>
    simp [b60_frame, Fin.sum_univ_succ, b60_eigen_coord] <;>
    field_simp [hs, Complex.I_ne_zero] <;> ring_nf <;> simp [Complex.I_sq]

set_option maxHeartbeats 400000 in
theorem b60_F_injective : Function.Injective b60_F := by
  intro z w hzw
  have hmem (p : Fin 2 × Fin 3) : b60_frame z p ∈ b60_F w := by
    rw [← hzw]
    exact Submodule.subset_span ⟨p, rfl⟩
  funext k
  have hm := hmem (0, ⟨k % 3, Nat.mod_lt _ (by omega)⟩)
  rw [b60_F, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have hcoord (q : Fin 6 × Fin 2) := congrArg (fun v => b60_basis.repr v q) hc
  have hc0 (i : Fin 3) : c (0, i) = if i = ⟨k % 3, Nat.mod_lt _ (by omega)⟩ then 1 else 0 := by
    have h0 := hcoord (Fin.castAdd 3 i, 0)
    have h1 := hcoord (Fin.castAdd 3 i, 1)
    have hp := congrArg₂ (fun x y : ℂ ↦ (x, y)) h0 h1
    have h := congrArg (fun x ↦ (x.1 - (Complex.I * (Real.sqrt 3 : ℂ)) * x.2) / 2) hp
    have hsum :
        ((∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.castAdd 3 i, 0)) -
          (Complex.I * (Real.sqrt 3 : ℂ)) *
            ∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.castAdd 3 i, 1)) / 2 =
        ∑ x, c x * ((b60_basis.repr (b60_frame w x) (Fin.castAdd 3 i, 0) -
          (Complex.I * (Real.sqrt 3 : ℂ)) *
            b60_basis.repr (b60_frame w x) (Fin.castAdd 3 i, 1)) / 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    simp only [map_sum, map_smul] at h
    change ((∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.castAdd 3 i, 0)) -
      (Complex.I * (Real.sqrt 3 : ℂ)) *
        ∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.castAdd 3 i, 1)) / 2 = _ at h
    rw [hsum] at h
    simp_rw [b60_frame_neg_leading] at h
    rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
    simpa [Fin.sum_univ_succ, eq_comm] using h
  let j : Fin 3 := ⟨k / 3, by omega⟩
  have h0 := hcoord (Fin.natAdd 3 j, 0)
  have h1 := hcoord (Fin.natAdd 3 j, 1)
  have hp := congrArg₂ (fun x y : ℂ ↦ (x, y)) h0 h1
  have h := congrArg (fun x ↦ (x.1 - (Complex.I * (Real.sqrt 3 : ℂ)) * x.2) / 2) hp
  simp only [map_sum, map_smul] at h
  change ((∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.natAdd 3 j, 0)) -
    (Complex.I * (Real.sqrt 3 : ℂ)) *
      ∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.natAdd 3 j, 1)) / 2 = _ at h
  have hsum :
      ((∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.natAdd 3 j, 0)) -
        (Complex.I * (Real.sqrt 3 : ℂ)) *
          ∑ x, c x * b60_basis.repr (b60_frame w x) (Fin.natAdd 3 j, 1)) / 2 =
      ∑ x, c x * ((b60_basis.repr (b60_frame w x) (Fin.natAdd 3 j, 0) -
        (Complex.I * (Real.sqrt 3 : ℂ)) *
          b60_basis.repr (b60_frame w x) (Fin.natAdd 3 j, 1)) / 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsum] at h
  simp_rw [b60_frame_neg_trailing] at h
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [Fin.sum_univ_succ, hc0] at h
  fin_cases k <;> simp [j, g32m_toMat, finProdFinEquiv] at h ⊢ <;>
    (try field_simp [hs2] at h ⊢) <;> exact h.symm

theorem b60b_marked_filtration_injective (τ : g32m_Domain) :
    Function.Injective (fun z ↦ (b60_F z).map
      (b2_cplxMap (b60b_marking τ).toAddMonoidHom)) := by
  intro z w h
  apply b60_F_injective
  exact (Submodule.map_injective_of_injective
    (b2a_cplxMap_injective _ (b60b_marking τ).injective)) h

end HodgeLean.Foundations.Program
