import HodgeLean.Foundations.Program.MilneCentralizerDefs

/-! # Auxiliary statements for the Milne M0 specification -/

noncomputable section

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m0_centralizer_integral_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ m0_endCentralizer J ↔
      ∀ f : J ⟶ J, IsMonHom f → u ∘ₗ (homPullback f 1).baseChange ℂ =
        (homPullback f 1).baseChange ℂ ∘ₗ u := by
  rw [m0_endCentralizer, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h f hf
    have he := h _ ⟨(1 : ℚ) ⊗ₜ[ℤ] (⟨f, hf⟩ : AbelianEnd J), rfl⟩
    simpa only [spec_g4_abelianEnd0Action_tmul, one_smul,
      MulOpposite.unop_op, Module.End.mul_eq_comp, abelianEndAction, complexPointPullback, homPullback] using he.symm
  · intro h a ha
    obtain ⟨φ, rfl⟩ := ha
    change ((abelianEnd0Action J φ).unop).baseChange ℂ ∘ₗ u =
      u ∘ₗ ((abelianEnd0Action J φ).unop).baseChange ℂ
    induction φ using TensorProduct.inductionOn with
    | tmul q f =>
      simp only [spec_g4_abelianEnd0Action_tmul, MulOpposite.unop_op,
        LinearMap.baseChange_smul, LinearMap.smul_comp, LinearMap.comp_smul]
      exact congrArg (q • ·) (h f.hom f.isMonHom).symm
    | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add, LinearMap.baseChange_add,
        LinearMap.add_comp, LinearMap.comp_add, ha, hb]

theorem m0_bivector_form {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω)
    (u : Module.End K V) (hu : IsUnit u) :
    exteriorPower.map 2 u ω = ω ↔
      ∀ x y, dualForm hω (u x) (u y) = dualForm hω x y := by
  obtain ⟨a, rfl⟩ := hu
  have hinj : Function.Injective (a.val : Module.End K V) := by
    intro x y h
    have := congrArg (fun z => (a.inv : Module.End K V) z) h
    simpa only [← Module.End.mul_apply, a.inv_val, Module.End.one_apply] using this
  have hsurj : Function.Surjective (a.val : Module.End K V) := by
    intro x
    refine ⟨a.inv x, ?_⟩
    change (a.val * a.inv) x = x
    rw [a.val_inv, Module.End.one_apply]
  rw [← contract_injective.eq_iff, contract_map]
  constructor
  · intro hc x y
    have he : a.val.dualMap ((contractEquiv hω).symm (a.val y)) =
        (contractEquiv hω).symm y := by
      apply (contractEquiv hω).injective
      apply hinj
      have ht := LinearMap.congr_fun hc ((contractEquiv hω).symm (a.val y))
      simpa only [LinearMap.comp_apply, contract_contractEquiv_symm,
        contractEquiv_apply] using ht
    exact LinearMap.congr_fun he x
  · intro h
    ext φ
    apply sub_eq_zero.mp
    apply (nondegenerate_dualForm hω).2
    intro z
    obtain ⟨x, rfl⟩ := hsurj z
    rw [map_sub]
    change dualForm hω (a.val x) (a.val (contract ω (a.val.dualMap φ))) -
      dualForm hω (a.val x) (contract ω φ) = 0
    rw [h, dualForm_apply, contractEquiv_symm_contract,
      dualForm_apply, contractEquiv_symm_contract, LinearMap.dualMap_apply, sub_self]

theorem m0_bivector_iff_form_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : IsUnit u) :
    exteriorPower.map 2 u (HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf J) pol)) =
      HodgeBlocks.complexifyWedge 2 (polarizationVec (torusCohomology_cupProductOf J) pol) ↔
    ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y := by
  letI := (torusCohomology_cupProductOf J).finite
  simpa only [m0_form, polarizationForm, pol1_dualForm_complexify] using
    m0_bivector_form (pol1_complexify_nondegenerate hη) u hu

theorem m0_mem_lefschetz_iff_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ g32p_lefschetz J pol ↔
      IsUnit u ∧ u ∈ m0_endCentralizer J ∧
        ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y := by
  change (IsUnit u ∧ _ ∧ _) ↔ _
  rw [m0_centralizer_integral_aux]
  constructor
  · rintro ⟨hu, hc, hp⟩
    exact ⟨hu, hc, (m0_bivector_iff_form_aux J pol hη u hu).1 hp⟩
  · rintro ⟨hu, hc, hp⟩
    exact ⟨hu, hc, (m0_bivector_iff_form_aux J pol hη u hu).2 hp⟩

theorem m0_rosati_pairing_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (φ : AbelianEnd0 J) (x y : ℂ ⊗[ℚ] HQ J 1) :
    let hP : p1_IsPolarization J pol := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
    m0_form J pol hη (((abelianEnd0Action J φ).unop).baseChange ℂ x) y =
      m0_form J pol hη x
        (((abelianEnd0Action J (p1_rosati J pol (p1_isNondegenerate J hP)
          (p1_adjoint_mem_range J hP) φ)).unop).baseChange ℂ y) := by
  dsimp only
  rw [p1r_abelianEnd0Action_rosati]
  exact p1r_baseChange_adjoint _ _ _ (p1r_dualForm_adjoint hη _) x y

def m0_adjoint {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (u : Module.End K V) : Module.End K V :=
  (contractEquiv hω).toLinearMap ∘ₗ u.dualMap ∘ₗ (contractEquiv hω).symm.toLinearMap

theorem m0_adjoint_pair {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (u : Module.End K V) (x y : V) :
    dualForm hω (u x) y = dualForm hω x (m0_adjoint hω u y) := by
  simp only [m0_adjoint, LinearMap.comp_apply, dualForm_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, LinearMap.dualMap_apply]

theorem m0_form_nondegenerate (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    (m0_form J pol hη).Nondegenerate := by
  letI := (torusCohomology_cupProductOf J).finite
  exact WeilPower.nondegenerate_baseChange _
    (nondegenerate_polarizationForm (torusCohomology_cupProductOf J) hη)

theorem m0_centralizer_adjoint_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : u ∈ m0_endCentralizer J) :
    ∃! v : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1), v ∈ m0_endCentralizer J ∧
      ∀ x y, m0_form J pol hη (u x) y = m0_form J pol hη x (v y) := by
  letI := (torusCohomology_cupProductOf J).finite
  let v := m0_adjoint (pol1_complexify_nondegenerate hη) u
  have hpair : ∀ x y, m0_form J pol hη (u x) y = m0_form J pol hη x (v y) := by
    simpa only [m0_form, polarizationForm, pol1_dualForm_complexify] using
      m0_adjoint_pair (pol1_complexify_nondegenerate hη) u
  have hE := m0_form_nondegenerate J pol hη
  refine ⟨v, ⟨?_, hpair⟩, ?_⟩
  · rw [m0_endCentralizer, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨φ, rfl⟩
    let hP := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
    let ψ := p1_rosati J pol (p1_isNondegenerate J hP) (p1_adjoint_mem_range J hP) φ
    have hp : ∀ x y, m0_form J pol hη
        (((abelianEnd0Action J ψ).unop).baseChange ℂ x) y =
        m0_form J pol hη x (((abelianEnd0Action J φ).unop).baseChange ℂ y) := by
      intro x y
      have ht := m0_rosati_pairing_aux J pol hη hpos ψ x y
      simpa only [ψ, hP, p1r_rosati_rosati] using ht
    have hc := (Subalgebra.mem_centralizer_iff ℂ).mp hu _ ⟨ψ, rfl⟩
    apply LinearMap.ext
    intro y
    apply sub_eq_zero.mp
    apply hE.2
    intro x
    rw [map_sub]
    change m0_form J pol hη x
      (((abelianEnd0Action J φ).unop).baseChange ℂ (v y)) -
        m0_form J pol hη x (v (((abelianEnd0Action J φ).unop).baseChange ℂ y)) = 0
    have hcx := LinearMap.congr_fun hc x
    change ((abelianEnd0Action J ψ).unop).baseChange ℂ (u x) =
      u (((abelianEnd0Action J ψ).unop).baseChange ℂ x) at hcx
    rw [← hp, ← hpair, ← hcx, hp, hpair, sub_self]
  · intro w hw
    apply LinearMap.ext
    intro y
    apply sub_eq_zero.mp
    apply hE.2
    intro x
    rw [map_sub, ← hw.2, hpair, sub_self]

theorem m0_comparison_preserves {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E F : LinearMap.BilinForm ℂ M) (hE : E.Nondegenerate)
    (P Q : Submodule ℂ M) (hsplit : P ⊔ Q = ⊤)
    (hP : ∀ x ∈ P, ∀ y ∈ P, E x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, E x y = 0)
    (hF : ∀ x ∈ P, ∀ y ∈ P, F x y = 0)
    (T : Module.End ℂ M) (hT : ∀ x y, E x (T y) = F x y) :
    P.map T ≤ P := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨p, hp, q, hq, heq⟩ := Submodule.mem_sup.mp (hsplit ▸ Submodule.mem_top : T y ∈ P ⊔ Q)
  have hq0 : q = 0 := by
    apply hE.2
    intro w
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hsplit ▸ Submodule.mem_top : w ∈ P ⊔ Q)
    have h : E a q = 0 := by
      have ht := hT a y
      rw [← heq, map_add, hP _ ha _ hp, zero_add, hF _ ha _ hy] at ht
      exact ht
    rw [map_add, LinearMap.add_apply, h, hQ _ hb _ hq, add_zero]
  rw [← heq, hq0, add_zero]
  exact hp

theorem m0_isotropic (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    (∀ x ∈ complexHolomorphicH1 J, ∀ y ∈ complexHolomorphicH1 J, m0_form J pol hη x y = 0) ∧
    (∀ x ∈ complexAntiholomorphicH1 J, ∀ y ∈ complexAntiholomorphicH1 J, m0_form J pol hη x y = 0) := by
  have hP := (p1_isPolarization_iff J pol).2 ⟨hη, hpos⟩
  obtain ⟨⟨h10, h01⟩, -⟩ := (spec_firstRiemannRelation J (finiteBetti_abelian J)
    (spec_bettiDeRhamIso_abelian J) hη).1 (p1_mem_hdg J hP)
  have e10 : complexHolomorphicH1 J = cohomologyHodgePiece J 1 (1, 0) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  have e01 : complexAntiholomorphicH1 J = cohomologyHodgePiece J 1 (0, 1) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp [latticeHodgePieces]
  exact ⟨e10 ▸ h10, e01 ▸ h01⟩

theorem m0_baseChange_compare {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E F : LinearMap.BilinForm ℚ V) (T : Module.End ℚ V)
    (h : ∀ x y, E x (T y) = F x y) (x y : ℂ ⊗[ℚ] V) :
    E.baseChange ℂ x (T.baseChange ℂ y) = F.baseChange ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul b w => simp [LinearMap.BilinForm.baseChange_tmul, h]

theorem m0_preserves_other (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (pol' : HQ J 2)
    (hη' : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol'))
    (hpos' : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη')
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hc : u ∈ m0_endCentralizer J)
    (hu : ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y) :
    ∀ x y, m0_form J pol' hη' (u x) (u y) = m0_form J pol' hη' x y := by
  letI := (torusCohomology_cupProductOf J).finite
  let T : Module.End ℚ (HQ J 1) :=
    (contractEquiv hη).toLinearMap ∘ₗ (contractEquiv hη').symm.toLinearMap
  have ht : ∀ x y, polarizationForm (torusCohomology_cupProductOf J) hη x (T y) =
      polarizationForm (torusCohomology_cupProductOf J) hη' x y := by
    intro x y
    simp only [polarizationForm, dualForm_apply, T, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  have htc := m0_baseChange_compare _ _ T ht
  have hsplit := (spec_complexH1_split J).1
  obtain ⟨hP, hQ⟩ := m0_isotropic J pol hη hpos
  obtain ⟨hP', hQ'⟩ := m0_isotropic J pol' hη' hpos'
  have hT : T ∈ hodgeEndH1 J := by
    exact ⟨m0_comparison_preserves _ _ (m0_form_nondegenerate J pol hη)
        _ _ hsplit hP hQ hP' _ htc,
      m0_comparison_preserves _ _ (m0_form_nondegenerate J pol hη)
        _ _ (by rw [sup_comm]; exact hsplit) hQ hP hQ' _ htc⟩
  obtain ⟨φ, hφ⟩ := (p1r_mem_range_iff J T).2 hT
  have hcomm := (Subalgebra.mem_centralizer_iff ℂ).mp hc _ ⟨φ, rfl⟩
  change (abelianEnd0Action J φ).unop = T at hφ
  change ((abelianEnd0Action J φ).unop).baseChange ℂ ∘ₗ u =
    u ∘ₗ ((abelianEnd0Action J φ).unop).baseChange ℂ at hcomm
  rw [hφ] at hcomm
  intro x y
  change (polarizationForm _ hη').baseChange ℂ (u x) (u y) =
    (polarizationForm _ hη').baseChange ℂ x y
  have hcy := LinearMap.congr_fun hcomm y
  change T.baseChange ℂ (u y) = u (T.baseChange ℂ y) at hcy
  rw [← htc, ← htc, hcy]
  exact hu x (T.baseChange ℂ y)

theorem m0_polarization_independent_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη)
    (pol' : HQ J 2)
    (hη' : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol'))
    (hpos' : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη') :
    g32p_lefschetz J pol = g32p_lefschetz J pol' := by
  apply Set.ext
  intro u
  rw [m0_mem_lefschetz_iff_aux J pol hη, m0_mem_lefschetz_iff_aux J pol' hη']
  constructor
  · rintro ⟨hu, hc, hp⟩
    exact ⟨hu, hc, m0_preserves_other J pol hη hpos pol' hη' hpos' u hc hp⟩
  · rintro ⟨hu, hc, hp⟩
    exact ⟨hu, hc, m0_preserves_other J pol' hη' hpos' pol hη hpos u hc hp⟩

theorem m0_exterior_commutes_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1))
    (hu : u ∈ g32p_lefschetz J pol) (φ : AbelianEnd0 J) (r n : ℕ) :
    exteriorPower.map n (g32p_diag J u r) ∘ₗ
        exteriorPower.map n (g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r) =
      exteriorPower.map n (g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r) ∘ₗ
        exteriorPower.map n (g32p_diag J u r) := by
  have hc := (m0_centralizer_integral_aux J u).2 hu.2.1
  have he := (((Subalgebra.mem_centralizer_iff ℂ).mp (show u ∈ Subalgebra.centralizer ℂ _ from hc))) _
    ⟨φ, rfl⟩
  have hd : g32p_diag J u r ∘ₗ
      g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r =
      g32p_diag J (((abelianEnd0Action J φ).unop).baseChange ℂ) r ∘ₗ
        g32p_diag J u r := by
    apply LinearMap.ext
    intro x
    funext i
    exact (LinearMap.congr_fun he (x i)).symm
  rw [← exteriorPower.map_comp, hd, exteriorPower.map_comp]

theorem m0_tensor_natural {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (n : ℕ) (f : Module.End K M) :
    (PiTensorProduct.map (fun _ : Fin n => f)) ∘ₗ exteriorPower.toTensorPower K M n =
      exteriorPower.toTensorPower K M n ∘ₗ exteriorPower.map n f := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, InvariantsExterior.toTensorPower_ιMulti,
    SchurWeyl.antisymTensor_apply, map_sum, map_zsmul, PiTensorProduct.map_tprod]
  rfl

theorem m0_tensor_lift_fixed_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    (∀ u ∈ g32p_lefschetz J pol, exteriorPower.map n (g32p_diag J u r) v = v) ↔
      ∀ u ∈ g32p_lefschetz J pol,
        PiTensorProduct.map (fun _ : Fin n => g32p_diag J u r) (m0_tensorLift J r n v) =
          m0_tensorLift J r n v := by
  have hnatur (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
      PiTensorProduct.map (fun _ : Fin n => g32p_diag J u r) (m0_tensorLift J r n v) =
        m0_tensorLift J r n (exteriorPower.map n (g32p_diag J u r) v) := by
    unfold m0_tensorLift
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
    exact congrArg ((n.factorial : ℂ)⁻¹ • ·)
      (LinearMap.congr_fun (m0_tensor_natural n (g32p_diag J u r)) v)
  constructor
  · intro h u hu
    rw [hnatur, h u hu]
  · intro h u hu
    have he := h u hu
    rw [hnatur] at he
    have hinj : Function.Injective (m0_tensorLift J r n) := by
      intro a b hab
      apply InvariantsExterior.toTensorPower_injective n
      exact (smul_right_injective _ (inv_ne_zero
        (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)))
          (show (n.factorial : ℂ)⁻¹ • _ = (n.factorial : ℂ)⁻¹ • _ from hab)
    exact hinj he

theorem m0_map_neg_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) :
    exteriorPower.map n (-1 : Module.End K V) = (-1 : K) ^ n • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_apply]
  have hv : (⇑(-1 : Module.End K V) ∘ v) = fun i => (-1 : K) • v i := by
    funext i
    simp
  rw [hv, AlternatingMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem m0_neg_mem (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) :
    (-1 : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) ∈ g32p_lefschetz J pol := by
  refine ⟨isUnit_one.neg, fun f _ => LinearMap.ext fun x => by simp, ?_⟩
  rw [m0_map_neg_one]
  simp only [even_two.neg_one_pow, one_smul, LinearMap.id_apply]

theorem m0_odd_invariants_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2) (r n : ℕ) (hn : Odd n) :
    g32p_invariants J pol r n = ⊥ := by
  apply le_antisymm _ bot_le
  rintro z ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hv
  have hf := hv (-1) (m0_neg_mem J pol)
  have hd : g32p_diag J (-1) r = (-1 : Module.End ℂ (Fin r → ℂ ⊗[ℚ] HQ J 1)) := by
    ext x i
    rfl
  change exteriorPower.map n (g32p_diag J (-1) r) v = v at hf
  rw [hd, m0_map_neg_one, hn.neg_one_pow, LinearMap.smul_apply, LinearMap.id_apply,
    neg_one_smul] at hf
  have hv0 : v = 0 := by
    have htwo : (2 : ℂ) • v = 0 := by
      rw [two_smul]
      calc
        v + v = -v + v := congrArg (· + v) hf.symm
        _ = 0 := neg_add_cancel v
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [hv0, map_zero]
  exact Submodule.zero_mem _

theorem m0_mem_lefschetz_norm_one_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    u ∈ g32p_lefschetz J pol ↔
      u ∈ m0_endCentralizer J ∧ ∃ v : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1),
        (∀ x y, m0_form J pol hη (u x) y = m0_form J pol hη x (v y)) ∧
        v ∘ₗ u = 1 := by
  letI := (torusCohomology_cupProductOf J).finite
  have hE := m0_form_nondegenerate J pol hη
  rw [m0_mem_lefschetz_iff_aux J pol hη u]
  constructor
  · rintro ⟨⟨a, ha⟩, hc, hp⟩
    subst u
    refine ⟨hc, a.inv, ?_, ?_⟩
    · intro x y
      have ht := hp x (a.inv y)
      have hy : a.val (a.inv y) = y := by
        change (a.val * a.inv) y = y
        rw [a.val_inv, Module.End.one_apply]
      rwa [hy] at ht
    · exact a.inv_val
  · rintro ⟨hc, v, hp, hv⟩
    have hf : ∀ x y, m0_form J pol hη (u x) (u y) = m0_form J pol hη x y := by
      intro x y
      rw [hp]
      have hy := LinearMap.congr_fun hv y
      change v (u y) = y at hy
      rw [hy]
    refine ⟨?_, hc, hf⟩
    apply (LinearMap.isUnit_iff_ker_eq_bot u).2
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply hE.1
    intro y
    rw [← hf, hx, map_zero, LinearMap.zero_apply]

end HodgeLean.Foundations.Program
