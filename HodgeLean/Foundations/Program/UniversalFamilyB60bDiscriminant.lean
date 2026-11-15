import HodgeLean.Foundations.Program.UniversalFamilyB60bTransport
import HodgeLean.RealDefs.Compare.MarkmanTransport

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.WeilHermitian HodgeLean.RealDefs.Compare.Markman
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

def b60_dualAction : {J : Module.End ℚ (b2b_dual b60_Lattice) //
    J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
  ⟨b60b_dualPrecomp b60_omega.toAddMonoidHom, by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    change f (b60_omega (b60_omega x)) = -3 * f x
    calc
      _ = f ((-3 : ℤ) • x) := congrArg f (LinearMap.congr_fun b60_omega_square x)
      _ = _ := by rw [map_zsmul]; norm_num⟩

def b60_dualVector (i : Fin 6) : b2b_dual b60_Lattice :=
  b2b_flat b60_Lattice b60_E
    ((1 : ℚ) ⊗ₜ[ℤ] Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 0))

theorem b60_dualAction_vector (i : Fin 6) :
    b60_dualAction.1 (b60_dualVector i) =
      -b2b_flat b60_Lattice b60_E
        ((1 : ℚ) ⊗ₜ[ℤ] Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 1)) := by
  apply LinearMap.ext
  intro x
  simp only [b60_dualAction, b60_dualVector, b60b_dualPrecomp,
    b2bpol_flat_apply, LinearMap.BilinForm.baseChange_tmul, one_mul,
    LinearMap.neg_apply, LinearMap.coe_mk, AddHom.coe_mk, Int.smul_one_eq_cast]
  have homega : b60_omega (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 0)) =
      Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 1) := by
    ext p
    rcases p with ⟨j, k⟩
    fin_cases k <;> simp [b60_omega, Pi.basisFun_apply, Pi.single_apply] <;>
      split_ifs <;> simp_all
  have hs := b60_E_omega_skew (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 0)) x
  rw [homega] at hs
  have hz : b60_E (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 0)) (b60_omega x) =
      -b60_E (Pi.basisFun ℤ (Fin 6 × Fin 2) (i, 1)) x := by linarith
  exact_mod_cast hz

theorem b60_dualVector_linearIndependent (τ : g32m_Domain) :
    LinearIndependent (QuadraticAlgebra ℚ (-3) 0)
      (fun i ↦ (WithJ.equiv b60_dualAction).symm (b60_dualVector i)) := by
  classical
  apply (linearIndependent_double_iff b60_dualAction b60_dualVector).1
  let br := (Pi.basisFun ℤ (Fin 6 × Fin 2)).baseChange ℚ
  let u : Fin 6 ⊕ Fin 6 → ℚ ⊗[ℤ] b60_Lattice := fun p ↦ match p with
    | Sum.inl i => br (i, 0)
    | Sum.inr i => -br (i, 1)
  have hlu : LinearIndependent ℚ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    cases p with
    | inl i =>
      have h := congrArg (fun z ↦ br.repr z (i, 0)) hc
      simpa [u, br, Fintype.sum_sum_type, Pi.single_apply] using h
    | inr i =>
      have h := congrArg (fun z ↦ br.repr z (i, 1)) hc
      simpa [u, br, Fintype.sum_sum_type, Pi.single_apply] using h
  have hflat : Function.Injective (b2b_flat b60_Lattice b60_E) := by
    apply (b2bpol_flat_bijective b60_Lattice b60_E _).1
    intro x hx
    exact b2_riemannForm_nondegenerate (b60_F τ) b60_E (b60_weight_one τ)
      ((b60_riemann_iff τ).2 τ.property) x hx
  have hm := hlu.map' (b2b_flat b60_Lattice b60_E) (LinearMap.ker_eq_bot.mpr hflat)
  rw [show Sum.elim b60_dualVector (fun i ↦ b60_dualAction.1 (b60_dualVector i)) =
      (b2b_flat b60_Lattice b60_E) ∘ u by
    funext p
    cases p with
    | inl i => simp [u, br, b60_dualVector]
    | inr i => simpa [u, br] using b60_dualAction_vector i]
  exact hm

theorem b60_dual_finrank :
    Module.finrank (QuadraticAlgebra ℚ (-3) 0)
      (WithJ (b2b_dual b60_Lattice) b60_dualAction) = 6 := by
  have h := finrank_withJ b60_dualAction
  rw [← (b60b_addHomLinearEquiv b60_Lattice).finrank_eq,
    Module.finrank_eq_card_basis (latticeDualBasisQ (Λ := b60_Lattice)),
    ← Module.finrank_eq_card_chooseBasisIndex, b60b_lattice_finrank] at h
  omega

noncomputable def b60_dualBasis (τ : g32m_Domain) :
    Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0)
      (WithJ (b2b_dual b60_Lattice) b60_dualAction) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i ↦ (WithJ.equiv b60_dualAction).symm (b60_dualVector i))
    (b60_dualVector_linearIndependent τ) (by rw [b60_dual_finrank]; simp)

@[simp] theorem b60_dualBasis_equiv (τ : g32m_Domain) (i : Fin 6) :
    WithJ.equiv b60_dualAction (b60_dualBasis τ i) = b60_dualVector i := by
  simp [b60_dualBasis]

theorem b60_flat_bijective (τ : g32m_Domain) :
    Function.Bijective (b2b_flat b60_Lattice b60_E) := by
  apply b2bpol_flat_bijective b60_Lattice b60_E
  intro x hx
  exact b2_riemannForm_nondegenerate (b60_F τ) b60_E (b60_weight_one τ)
    ((b60_riemann_iff τ).2 τ.property) x hx

theorem b60_E_alt (x : b60_Lattice) : b60_E x x = 0 := by
  simp only [b60_E, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_eq_zero
  intro i hi
  ring

theorem b60_dualAction_flat (a : ℚ ⊗[ℤ] b60_Lattice) :
    b60_dualAction.1 (b2b_flat b60_Lattice b60_E a) =
      -b2b_flat b60_Lattice b60_E
        (b60_omega.baseChange ℚ a) := by
  apply LinearMap.ext
  intro x
  simp only [b60_dualAction, b60b_dualPrecomp, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.neg_apply, b2bpol_flat_apply]
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb, LinearMap.add_apply, neg_add]
  | tmul q y =>
    simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
      zsmul_eq_mul, Int.cast_id, mul_one, neg_smul]
    have hcast : ((-b60_E y (b60_omega x) : ℤ) : ℚ) =
        -(b60_E y (b60_omega x) : ℚ) := by norm_num
    rw [b60_E_omega_skew]
    rw [hcast]
    have hto : b60_omega.toAddMonoidHom x = b60_omega x := rfl
    rw [hto]
    ring

theorem b60_dualForm_action_skew (τ : g32m_Domain) (x y : b2b_dual b60_Lattice) :
    b2b_dualForm b60_Lattice b60_E (b60_dualAction.1 x) y =
      -b2b_dualForm b60_Lattice b60_E x (b60_dualAction.1 y) := by
  obtain ⟨a, rfl⟩ := (b60_flat_bijective τ).2 x
  obtain ⟨b, rfl⟩ := (b60_flat_bijective τ).2 y
  rw [b60_dualAction_flat, b60_dualAction_flat]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [b2bpol_dualForm_flat _ _ (b60_flat_bijective τ),
    b2bpol_dualForm_flat _ _ (b60_flat_bijective τ)]
  induction a using TensorProduct.inductionOn with
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc, neg_add]
  | tmul q a =>
    induction b using TensorProduct.inductionOn with
    | add b c hb hc => simp only [map_add, hb, hc, LinearMap.add_apply, neg_add]
    | tmul r b =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        zsmul_eq_mul, Int.cast_id, mul_one]
      have hcast : ((-b60_E a (b60_omega b) : ℤ) : ℚ) =
          -(b60_E a (b60_omega b) : ℚ) := by norm_num
      rw [b60_E_omega_skew]
      rw [hcast]
      ring

theorem b60_dualForm_alt (τ : g32m_Domain) :
    (b2b_dualForm b60_Lattice b60_E).IsAlt := by
  intro x
  have hx := b2bpol_dualForm_skew b60_Lattice b60_E b60_E_alt
    (b60_flat_bijective τ) x x
  linarith

theorem b60_dualForm_nondegenerate (τ : g32m_Domain) :
    (b2b_dualForm b60_Lattice b60_E).Nondegenerate :=
  b2bpol_dualForm_nondegenerate b60_Lattice b60_E b60_E_alt (b60_flat_bijective τ)

theorem b60_weilHermitian_basis (τ : g32m_Domain) (i j : Fin 6) :
    weilHermitian (b2b_dualForm b60_Lattice b60_E) b60_dualAction
        (b60_dualForm_action_skew τ) (b60_dualBasis τ i) (b60_dualBasis τ j) =
      if i = j then (-b60_diag i : ℚ) else 0 := by
  ext
  · simp only [re_weilHermitian, b60_dualBasis_equiv, b60_dualAction_vector,
      map_neg, LinearMap.neg_apply]
    simp only [b60_dualVector]
    rw [b2bpol_dualForm_flat _ _ (b60_flat_bijective τ)]
    simp [b60_E, Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · simp only [im_weilHermitian, b60_dualBasis_equiv]
    simp only [b60_dualVector]
    rw [b2bpol_dualForm_flat _ _ (b60_flat_bijective τ)]
    simp [b60_E, Pi.basisFun_apply, Pi.single_apply]

theorem b60_weilHermitian_gramDet (τ : g32m_Domain) :
    gramDetℚ (weilHermitian (b2b_dualForm b60_Lattice b60_E) b60_dualAction
      (b60_dualForm_action_skew τ)) (b60_dualBasis τ) = -2 := by
  rw [gramDetℚ, gramDet]
  rw [show LinearMap.toMatrix₂ (b60_dualBasis τ) (b60_dualBasis τ)
      (weilHermitian (b2b_dualForm b60_Lattice b60_E) b60_dualAction
        (b60_dualForm_action_skew τ)) =
      Matrix.diagonal (fun i ↦ (-b60_diag i : QuadraticAlgebra ℚ (-3) 0)) by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix₂_apply, b60_weilHermitian_basis]
    simp [Matrix.diagonal_apply]
    split_ifs <;> simp_all]
  rw [Matrix.det_diagonal]
  norm_num [b60_diag, Fin.prod_univ_succ, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.re_neg, QuadraticAlgebra.re_intCast]

set_option maxHeartbeats 400000 in
theorem b60_weilDetClass (τ : g32m_Domain) :
    weilDetClass (b2b_dualForm b60_Lattice b60_E) b60_dualAction
      (b60_dualForm_action_skew τ)
      (b60_dualForm_alt τ) (b60_dualForm_nondegenerate τ) = classNegTwo := by
  unfold weilDetClass
  rw [detClass_eq _ _ (b60_dualBasis τ)]
  change (((Units.mk0 (gramDetℚ
    (weilHermitian (b2b_dualForm b60_Lattice b60_E) b60_dualAction
      (b60_dualForm_action_skew τ)) (b60_dualBasis τ)) _ : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))) = classNegTwo
  unfold classNegTwo
  apply congrArg (fun u : ℚˣ ↦
    (u : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)))
  apply Units.ext
  exact b60_weilHermitian_gramDet τ

section TransportDet

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {a : ℚ}
  (J : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id})
  (J' : {J : Module.End ℚ W // J ∘ₗ J = a • LinearMap.id})

noncomputable def withJEquiv (e : V ≃ₗ[ℚ] W) (hJ : ∀ x, e (J.1 x) = J'.1 (e x)) :
    WithJ V J ≃ₗ[QuadraticAlgebra ℚ a 0] WithJ W J' where
  toFun x := (WithJ.equiv J').symm (e (WithJ.equiv J x))
  invFun x := (WithJ.equiv J).symm (e.symm (WithJ.equiv J' x))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by apply (WithJ.equiv J').injective; simp
  map_smul' z x := by
    apply (WithJ.equiv J').injective
    simp only [equiv_smul, LinearEquiv.apply_symm_apply, map_add, map_smul]
    rw [hJ]
    rfl

theorem weilHermitian_equiv (E : LinearMap.BilinForm ℚ V)
    (E' : LinearMap.BilinForm ℚ W) (e : V ≃ₗ[ℚ] W)
    (hJ : ∀ x, e (J.1 x) = J'.1 (e x)) (hE : ∀ x y, E' (e x) (e y) = E x y)
    (hs : ∀ x y, E (J.1 x) y = -E x (J.1 y))
    (hs' : ∀ x y, E' (J'.1 x) y = -E' x (J'.1 y)) (x y : WithJ V J) :
    weilHermitian E' J' hs' (withJEquiv J J' e hJ x) (withJEquiv J J' e hJ y) =
      weilHermitian E J hs x y := by
  ext
  · simp only [re_weilHermitian]
    change E' (e (WithJ.equiv J x)) (J'.1 (e (WithJ.equiv J y))) = _
    rw [← hJ, hE]
  · simp only [im_weilHermitian]
    change E' (e (WithJ.equiv J x)) (e (WithJ.equiv J y)) = _
    rw [hE]

set_option maxHeartbeats 400000 in
theorem weilDetClass_equiv [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]
    [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
    (E : LinearMap.BilinForm ℚ V) (E' : LinearMap.BilinForm ℚ W)
    (e : V ≃ₗ[ℚ] W) (hJ : ∀ x, e (J.1 x) = J'.1 (e x))
    (hE : ∀ x y, E' (e x) (e y) = E x y)
    (hs : ∀ x y, E (J.1 x) y = -E x (J.1 y))
    (hs' : ∀ x y, E' (J'.1 x) y = -E' x (J'.1 y))
    (ha : E.IsAlt) (ha' : E'.IsAlt) (hn : E.Nondegenerate) (hn' : E'.Nondegenerate) :
    weilDetClass E' J' hs' ha' hn' = weilDetClass E J hs ha hn := by
  let ek := withJEquiv J J' e hJ
  let b := (Module.finBasis (QuadraticAlgebra ℚ a 0) (WithJ V J)).map ek
  have hm : LinearMap.toMatrix₂ b b (weilHermitian E' J' hs') =
      LinearMap.toMatrix₂ (Module.finBasis (QuadraticAlgebra ℚ a 0) (WithJ V J))
        (Module.finBasis (QuadraticAlgebra ℚ a 0) (WithJ V J)) (weilHermitian E J hs) := by
    apply Matrix.ext
    intro i j
    simp only [LinearMap.toMatrix₂_apply, b, Module.Basis.map_apply]
    exact weilHermitian_equiv J J' E E' e hJ hE hs hs' _ _
  have hg : gramDetℚ (weilHermitian E' J' hs') b =
      gramDetℚ (weilHermitian E J hs)
        (Module.finBasis (QuadraticAlgebra ℚ a 0) (WithJ V J)) := by
    unfold gramDetℚ gramDet
    rw [hm]
  unfold weilDetClass
  rw [detClass_eq _ _ b,
    detClass_eq _ _ (Module.finBasis (QuadraticAlgebra ℚ a 0) (WithJ V J))]
  apply congrArg (fun u : ℚˣ ↦
    (u : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a 0)))
  apply Units.ext
  exact hg

end TransportDet

def b60_markedDualEquiv (τ : g32m_Domain) :
    b2b_dual b60_Lattice ≃ₗ[ℚ] b2b_dual (b2_abelianLattice (b60b_model τ)) where
  toFun f := f ∘ₗ (b60b_marking τ).symm.toIntLinearEquiv.toLinearMap
  invFun f := f ∘ₗ (b60b_marking τ).toIntLinearEquiv.toLinearMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def b60_cohomologyEquiv (τ : g32m_Domain) :
    b2b_dual b60_Lattice ≃ₗ[ℚ] HQ (b60b_model τ) 1 :=
  (b60_markedDualEquiv τ).trans (b60b_periodLinearEquiv (b60b_model τ)).symm

def b60_cohomAction (τ : g32m_Domain) :
    {J : Module.End ℚ (HQ (b60b_model τ) 1) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
  ⟨b60b_J τ, b4b_action_sq_aux b60_Lattice (b60b_model τ) (b60b_marking τ)
    b60_omega.toAddMonoidHom (fun l ↦ LinearMap.congr_fun b60_omega_square l)⟩

theorem b60_cohomologyEquiv_action (τ : g32m_Domain) (x : b2b_dual b60_Lattice) :
    b60_cohomologyEquiv τ (b60_dualAction.1 x) =
      (b60_cohomAction τ).1 (b60_cohomologyEquiv τ x) := by
  apply (b60b_periodLinearEquiv (b60b_model τ)).injective
  simp only [b60_cohomologyEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, b60_cohomAction]
  ext l
  change x (b60_omega ((b60b_marking τ).symm l)) =
    abelianPeriodEquiv (b60b_model τ)
      (b60b_J τ ((b60b_periodLinearEquiv (b60b_model τ)).symm
        (b60_markedDualEquiv τ x))) l
  unfold b60b_J b4b_cohomologyAction
  simp [b60_markedDualEquiv, b60b_periodLinearEquiv, b60b_addHomLinearEquiv,
    b4b_periodPrecomp]
  change x (b60_omega ((b60b_marking τ).symm l)) =
    x ((b60b_marking τ).symm (b60b_marking τ
      (b60_omega ((b60b_marking τ).symm l))))
  rw [(b60b_marking τ).symm_apply_apply]

theorem b60_cohomologyEquiv_form (τ : g32m_Domain) (x y : b2b_dual b60_Lattice) :
    polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
        (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
          (b60b_form_riemann τ))
        (b60_cohomologyEquiv τ x) (b60_cohomologyEquiv τ y) =
      b2b_dualForm b60_Lattice b60_E x y := by
  rw [b60b_polarizationForm_period]
  have he (z : b2b_dual b60_Lattice) :
      b60b_periodLinearEquiv (b60b_model τ) (b60_cohomologyEquiv τ z) =
        b60_markedDualEquiv τ z := by
    exact (b60b_periodLinearEquiv (b60b_model τ)).apply_symm_apply _
  rw [he x, he y]
  exact b2bpol_dualForm_comp (Λ := b60_Lattice)
    (Λ' := b2_abelianLattice (b60b_model τ)) b60_E (b60b_form τ) (b60b_marking τ)
    (fun x y ↦ by simp [b60b_form, b4b_transportForm]) x y

set_option maxHeartbeats 400000 in
theorem b60_cohomology_weilDetClass (τ : g32m_Domain) :
    weilDetClass
      (polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
        (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
          (b60b_form_riemann τ)))
      (b60_cohomAction τ)
      ((isRosatiSkew_iff_dualForm
        (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
          (b60b_form_riemann τ)) (b60b_J τ)).1 (b60b_rosati_model τ))
      (isAlt_polarizationForm _ _)
      (nondegenerate_polarizationForm _ _) = classNegTwo := by
  let E := polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
    (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
      (b60b_form_riemann τ))
  have hs' : ∀ x y, E ((b60_cohomAction τ).1 x) y =
      -E x ((b60_cohomAction τ).1 y) := by
    exact (isRosatiSkew_iff_dualForm
      (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
        (b60b_form_riemann τ)) (b60b_J τ)).1 (b60b_rosati_model τ)
  have h := weilDetClass_equiv b60_dualAction (b60_cohomAction τ)
    (b2b_dualForm b60_Lattice b60_E) E (b60_cohomologyEquiv τ)
    (b60_cohomologyEquiv_action τ) (b60_cohomologyEquiv_form τ)
    (b60_dualForm_action_skew τ) hs' (b60_dualForm_alt τ)
    (isAlt_polarizationForm _ _) (b60_dualForm_nondegenerate τ)
    (nondegenerate_polarizationForm _ _)
  exact h.trans (b60_weilDetClass τ)

end HodgeLean.Foundations.Program
