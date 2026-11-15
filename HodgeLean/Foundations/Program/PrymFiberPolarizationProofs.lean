import HodgeLean.Foundations.Program.PrymFiberPolarizationDefs

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- A skew lattice endomorphism becomes the negative dual operator under the rational row
comparison of a B5 model.
Source: Birkenhake–Lange, §1.2; `b64e_model_rational_column`, `b63g_modelOperator`. -/
theorem b63hp_model_rational_action (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hskew : ∀ x y, Q (φ x) y = -Q x (φ y)) (x : ℚ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64e_model_rational Λ F hF Q hQ (φ.toIntLinearMap.baseChange ℚ x) =
      -b63g_modelOperator Λ F hF Q hQ φ (b64e_model_rational Λ F hF Q hQ x) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, hx, hz, neg_add]
  | tmul q l =>
    rw [show q ⊗ₜ[ℤ] l = q • ((1 : ℚ) ⊗ₜ[ℤ] l) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    rw [map_smul, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, ← smul_neg]
    congr 1
    rw [b64e_model_rational_column, b64e_model_rational_column]
    apply (abelianPeriodEquiv (b5_model Λ F hF Q)).injective
    ext k
    obtain ⟨k, rfl⟩ := (b5_periodEquiv Λ F hF Q hQ).surjective k
    rw [map_neg, AddMonoidHom.neg_apply]
    change abelianPeriodEquiv _ (b63g4_column _ _ _) _ =
      -(abelianPeriodEquiv _ (b63g_modelOperator Λ F hF Q hQ φ (b63g4_column _ _ _)) _)
    have hop : ∀ (y : HQ (b5_model Λ F hF Q) 1) (m : Λ),
        abelianPeriodEquiv _ (b63g_modelOperator Λ F hF Q hQ φ y) (b5_periodEquiv Λ F hF Q hQ m) =
          abelianPeriodEquiv _ y (b5_periodEquiv Λ F hF Q hQ (φ m)) := by
      intro y m
      simp [b63g_modelOperator, b63g_dualOperator, b63g_precomp, b63g_modelMap]
    have hcol : ∀ a m : Λ, abelianPeriodEquiv _ (b63g4_column _ (b63g_modelForm Λ F hF Q hQ)
        (b5_periodEquiv Λ F hF Q hQ a)) (b5_periodEquiv Λ F hF Q hQ m) = (Q a m : ℚ) := by
      intro a m
      simp [b63g4_column, b2_bilinToAddHom, b63g_modelForm]
    rw [hop, hcol, hcol]
    exact (congrArg (fun z : ℤ ↦ (z : ℚ)) (hskew l k)).trans (Int.cast_neg _)

/-- On the sixfold of B5 data, the polarization form of the model class on the rational row
comparison is the rationalized original form.
Source: Birkenhake–Lange, §§4.1–4.2; `b64e_model_rational_form`, `b63g2_sixfold`. -/
theorem b63hp_sixfold_form (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ))
    (hnd : IsNondegenerate (polarizationVec
      (torusCohomology_cupProductOf (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).X)
      (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).pol)) (x y : ℚ ⊗[ℤ] Λ) :
    polarizationForm (torusCohomology_cupProductOf (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).X) hnd
        (b64e_model_rational Λ F hF Q hQ x) (b64e_model_rational Λ F hF Q hQ y) =
      Q.baseChange ℚ x y := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  have hn := b60b_dualForm_congr (rfl : polarizationVec
      (torusCohomology_cupProductOf (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).X)
      (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).pol = _) hnd
    (b2_abelian_nondegenerate (b5_model Λ F hF Q) (b63g_modelForm Λ F hF Q hQ)
      (b63g_modelForm_riemann Λ F hF Q hQ))
  exact (congrArg (fun B : LinearMap.BilinForm ℚ (HQ (b5_model Λ F hF Q) 1) ↦
    B (b64e_model_rational Λ F hF Q hQ x) (b64e_model_rational Λ F hF Q hQ y)) hn).trans
    (b64e_model_rational_form Λ F hF Q hQ x y)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b63hp_normalization_aux (D : rf8_SharedFamily) (s : b6t_polydisc mr_base) :
    let Λ := b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
    let E := b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s (D.P s) (D.Q s)
    let X := ((b63gR_family D).fiber s).X
    let h := g32h_fiber_polarized (b63gR_family D) s
    letI := (torusCohomology_cupProductOf X).finite
    ∃ e : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] HQ X 1,
      (∀ x, e ((D.A s).baseChange ℚ x) = -((b63gR_family D).fiber s).W.J (e x)) ∧
      ∃ c : ℚ, c = 1 ∧ 0 < c ∧
        ∀ x y, polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
          (e x) (e y) = c * E.baseChange ℚ x y := by
  intro Λ E X h
  letI := Module.Free.of_basis (b63gR_basis D)
  letI := Module.Finite.of_basis (b63gR_basis D)
  let L₀ := b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀
  let E₀ := b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀
    (D.P b63gP_s₀) (D.Q b63gP_s₀)
  let A₀ := b63g2_operator mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀
  let G := b63e_transportedF mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) D.P
    b63gP_s₀ s
  have hW := b63e_weight_one_riemann mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
    D.hG mr_base_mem_chart D.atlas.f D.atlas.hf D.atlas.hsurj D.hk
    D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP b63gP_s₀ s
  obtain ⟨-, T, hT, -⟩ := b63l_fibre_image_transport mr_base D.C D.hC s b63gP_s₀
  let er : (ℚ ⊗[ℤ] L₀) ≃ₗ[ℚ] HQ X 1 := b64e_model_rational L₀ G hW.1 E₀ hW.2
  have hTA : ∀ x, T (D.A s x) = A₀ (T x) := by
    intro x
    apply Subtype.val_injective
    rw [hT, D.hA s x]
    change _ = (A₀ (T x)).val
    rw [b63g2_operator_val, hT]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
      map_add, map_nsmul]
    rw [b63d_centre_transport mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
      b63gP_s₀ s x.val]
  have hTE : ∀ x y, E₀ (T x) (T y) = E x y := by
    intro x y
    change D.Q b63gP_s₀ (D.P b63gP_s₀ (T x).val) (D.P b63gP_s₀ (T y).val) =
      D.Q s (D.P s x.val) (D.P s y.val)
    rw [hT, hT]
    exact b63e_pairing_constant mr_base D.C (b6t_polydisc mr_base) (Subset.refl _)
      mr_base_mem_chart D.atlas.f D.atlas.hf D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP
      s b63gP_s₀ x.val y.val
  have hJeq : ((b63gR_family D).fiber s).W.J =
      b63g_modelOperator L₀ G hW.1 E₀ hW.2 A₀.toAddMonoidHom := rfl
  have hrJ : ∀ v, er (A₀.baseChange ℚ v) = -((b63gR_family D).fiber s).W.J (er v) := by
    intro v
    rw [hJeq]
    exact b63hp_model_rational_action L₀ G hW.1 E₀ hW.2 A₀.toAddMonoidHom
      (b63g2_operator_skew mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.hG _) (D.P _) (D.hP _) (D.Q _) (D.hQ _)) v
  have hsix := b63hp_sixfold_form L₀ G hW.1 E₀ hW.2 A₀.toAddMonoidHom
      (b63g2_operator_sq mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀
        (D.hG b63gP_s₀))
      (b63g2_operator_filtration mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        D.hG D.P D.hP b63gP_s₀ s)
  have hrE : ∀ v w, polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
      (er v) (er w) = E₀.baseChange ℚ v w := by
    intro v w
    exact hsix h.nondegenerate v w
  refine ⟨(LinearEquiv.baseChange ℤ ℚ _ _ T).trans er, ?_, 1, rfl, one_pos, ?_⟩
  · intro x
    change er (T.toLinearMap.baseChange ℚ ((D.A s).baseChange ℚ x)) =
      -((b63gR_family D).fiber s).W.J (er (T.toLinearMap.baseChange ℚ x))
    have hc : T.toLinearMap.baseChange ℚ ∘ₗ (D.A s).baseChange ℚ =
        A₀.baseChange ℚ ∘ₗ T.toLinearMap.baseChange ℚ := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      exact LinearMap.ext hTA
    rw [← LinearMap.comp_apply, hc, LinearMap.comp_apply, hrJ]
  · intro x y
    rw [one_mul]
    change polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
      (er (T.toLinearMap.baseChange ℚ x)) (er (T.toLinearMap.baseChange ℚ y)) = _
    rw [hrE]
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
    | tmul q l =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul r k =>
        simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
          LinearEquiv.coe_coe, hTE]

theorem b63hp_singular_discriminant_aux (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (s : b6t_polydisc mr_base) :
    let Λ := b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
    let E := b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
      (D.P s) (D.Q s)
    letI : Module.Finite ℤ Λ := Module.Finite.of_basis (b63hp_basis D s)
    ∃ hJ : (D.A s).baseChange ℚ ∘ₗ (D.A s).baseChange ℚ =
        (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ ((D.A s).baseChange ℚ x) y =
        -E.baseChange ℚ x ((D.A s).baseChange ℚ y),
    ∃ hh : (b64b_latticeH Λ E ⟨(D.A s).baseChange ℚ, hJ⟩ hskew).IsSymm,
    ∃ hn : (b64b_latticeH Λ E ⟨(D.A s).baseChange ℚ, hJ⟩ hskew).Nondegenerate,
      detClass (b64b_latticeH Λ E ⟨(D.A s).baseChange ℚ, hJ⟩ hskew) hh hn =
        classNegTwo := by
  intro Λ E
  have hs := rf8_filling_stabilizers mr_base D.atlas.U D.C D.atlas.π D.atlas.hπ u₀.val D.atlas.f
    D.atlas.ι D.atlas.hι.injective D.atlas.hrange D.atlas.hequiv
  have : FaithfulSMul b4b_Group D.C := hs.1
  have hγ : ∀ i, mr_IsLoop mr_base b63gP_basePoint i (b63gP_loops i) := fun i ↦
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  have hrot := rf8_cover_roots mr_base b63gP_s₀.property b63gP_basePoint b63gP_loops hγ
    D.atlas.U D.atlas.π D.atlas.hπ u₀ hroot D.C D.atlas.f D.atlas.ι
    D.atlas.hact D.atlas.hf D.atlas.hgal D.atlas.hι.continuous
    D.atlas.hproj D.atlas.hequiv hs.2
  have hstab : ∀ j, ∃ c : D.C, D.atlas.f c = b6_branch mr_base j ∧
      Nat.card (MulAction.stabilizer b4b_Group c) = orderOf (b4b_root j) := fun j ↦ by
    obtain ⟨c, hc, hr⟩ := hrot j
    exact ⟨c, hc, hr.2.1.symm⟩
  have hL := fun τ ↦ (hg5_lift_existsUnique D.atlas.U D.atlas.π D.atlas.hπ b63gP_basePoint rfl u₀
    D.C D.atlas.f D.atlas.hf.continuous D.atlas.hgal.2 D.atlas.ι D.atlas.hι D.atlas.hrange
    D.atlas.hproj τ).exists.choose_spec
  obtain ⟨A, hA, hJ, hskew, hfin, hh, hn, hd⟩ := hg7g_parameter_discriminant D.atlas.U
    D.atlas.π D.atlas.hπ b63gP_basePoint rfl u₀ b63gP_loops hγ hroot D.C D.hC D.atlas.f
    D.atlas.hf.continuous D.atlas.hgal.1 D.atlas.hgal.2 hstab D.atlas.ι D.atlas.hι D.atlas.hrange
    D.atlas.hproj D.atlas.hequiv _ hL (b6t_polydisc mr_base) (Subset.refl _) s
    (D.hk s) (D.P s) (D.hP s) (D.Q s) (D.hQ s)
  have hAeq : A = D.A s :=
    LinearMap.ext fun x ↦ Subtype.ext ((hA x).trans (D.hA s x).symm)
  subst hAeq
  exact ⟨hJ, hskew, hh, hn, hd⟩

/-- Replacing the quadratic action by its negative keeps the Weil–Hermitian class in even
`K`-dimension: the same vectors give a basis for the conjugate structure, whose Gram matrix is
`−conj G`, and `det (−conj G) = (−1)ⁿ det G` since `det G` is rational.
Source: Bourbaki, *Algebra*, Ch. IX, §1; `HermitianForm.star_gramDet`, `detClass_eq`. -/
theorem b63hp_neg_class {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E : LinearMap.BilinForm ℚ V)
    (J J' : {J : V →ₗ[ℚ] V // J ∘ₗ J = (-3 : ℚ) • LinearMap.id}) (hJ' : J'.1 = -J.1)
    (hskew : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hskew' : ∀ x y, E (J'.1 x) y = -E x (J'.1 y))
    (hE : E.IsAlt) (hnd : E.Nondegenerate)
    (hev : Even (Module.finrank hp_K (WithJ V J))) :
    weilDetClass E J' hskew' hE hnd = weilDetClass E J hskew hE hnd := by
  classical
  let e := Module.finBasis hp_K (WithJ V J)
  have hσ : ∀ (z : hp_K) (x : WithJ V J'),
      (WithJ.equiv J).symm (WithJ.equiv J' (z • x)) =
        star z • (WithJ.equiv J).symm (WithJ.equiv J' x) := by
    intro z x
    apply (WithJ.equiv J).injective
    rw [LinearEquiv.apply_symm_apply, equiv_smul, equiv_smul, LinearEquiv.apply_symm_apply, hJ']
    simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  let f : WithJ V J' ≃ₗ[hp_K] (Fin (Module.finrank hp_K (WithJ V J)) → hp_K) :=
    { toFun := fun x i ↦ star (e.equivFun ((WithJ.equiv J).symm (WithJ.equiv J' x)) i)
      invFun := fun c ↦ (WithJ.equiv J').symm (WithJ.equiv J (e.equivFun.symm (fun i ↦ star (c i))))
      map_add' := fun x y ↦ by funext i; simp
      map_smul' := fun z x ↦ by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [hσ, map_smul, Pi.smul_apply, smul_eq_mul, star_mul', star_star, mul_comm]
      left_inv := fun x ↦ by
        simp only [star_star]
        change (WithJ.equiv J').symm (WithJ.equiv J (e.equivFun.symm
          (e.equivFun ((WithJ.equiv J).symm (WithJ.equiv J' x))))) = x
        rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.symm_apply_apply]
      right_inv := fun c ↦ by
        funext i
        change star (e.equivFun ((WithJ.equiv J).symm (WithJ.equiv J'
          ((WithJ.equiv J').symm (WithJ.equiv J (e.equivFun.symm (fun i ↦ star (c i))))))) i) = c i
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
          LinearEquiv.apply_symm_apply, star_star] }
  let e' := Module.Basis.ofEquivFun f
  have he' : ∀ i, WithJ.equiv J' (e' i) = WithJ.equiv J (e i) := by
    intro i
    have hs : (fun j ↦ star ((Pi.single i (1 : hp_K) : _ → hp_K) j)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [Module.Basis.coe_ofEquivFun]
    change WithJ.equiv J' ((WithJ.equiv J').symm (WithJ.equiv J
      (e.equivFun.symm (fun j ↦ star ((Pi.single i (1 : hp_K) : _ → hp_K) j))))) = _
    rw [LinearEquiv.apply_symm_apply, hs, Module.Basis.equivFun_symm_apply]
    simp [Pi.single_apply]
  have hgram : LinearMap.toMatrix₂ e' e' (weilHermitian E J' hskew') =
      -(LinearMap.toMatrix₂ e e (weilHermitian E J hskew)).map star := by
    refine Matrix.ext fun i j ↦ ?_
    rw [LinearMap.toMatrix₂_apply, Matrix.neg_apply, Matrix.map_apply, LinearMap.toMatrix₂_apply]
    refine QuadraticAlgebra.ext ?_ ?_
    · simp [he', hJ', QuadraticAlgebra.re_star]
    · simp [he', QuadraticAlgebra.im_star]
  have hdet : gramDet (weilHermitian E J' hskew') e' = gramDet (weilHermitian E J hskew) e := by
    rw [gramDet, hgram, Matrix.det_neg, Fintype.card_fin, hev.neg_one_pow, one_mul]
    have hm := (starRingEnd hp_K).map_det (LinearMap.toMatrix₂ e e (weilHermitian E J hskew))
    rw [starRingEnd_apply] at hm
    change (Matrix.map _ (starRingEnd hp_K)).det = _
    rw [← RingHom.mapMatrix_apply, ← hm]
    exact star_gramDet (isSymm_weilHermitian hE) e
  rw [weilDetClass, weilDetClass, detClass_eq _ _ e', detClass_eq _ _ e]
  congr 2
  simp only [gramDetℚ, hdet]

theorem b63hp_model_discriminant_aux (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (s : b6t_polydisc mr_base) :
    g32t_disc (g32h_fiber_polarized (b63gR_family D) s) = classNegTwo := by
  obtain ⟨e, he, c, hc, -, hform⟩ := b63hp_normalization_aux D s
  obtain ⟨hJ, hskew, hh, hn, hd⟩ := b63hp_singular_discriminant_aux D u₀ hroot s
  subst hc
  let P := (b63gR_family D).fiber s
  let hP := g32h_fiber_polarized (b63gR_family D) s
  let Λ := b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
  let E := (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
    (D.P s) (D.Q s)).baseChange ℚ
  letI : Module.Finite ℤ Λ := Module.Finite.of_basis (b63hp_basis D s)
  letI : Module.Free ℤ Λ := Module.Free.of_basis (b63hp_basis D s)
  letI := (torusCohomology_cupProductOf P.X).finite
  let Em := polarizationForm (torusCohomology_cupProductOf P.X) hP.nondegenerate
  have hform' : ∀ x y, Em (e x) (e y) = E x y := fun x y ↦ (hform x y).trans (one_mul _)
  have hEalt : E.IsAlt := fun x ↦
    (hform' x x).symm.trans (isAlt_polarizationForm _ hP.nondegenerate (e x))
  have hEm := nondegenerate_polarizationForm _ hP.nondegenerate
  have hEnd : E.Nondegenerate := by
    refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · apply e.injective
      rw [map_zero]
      refine hEm.1 _ fun z ↦ ?_
      obtain ⟨y, rfl⟩ := e.surjective z
      exact (hform' x y).trans (hx y)
    · apply e.injective
      rw [map_zero]
      refine hEm.2 _ fun z ↦ ?_
      obtain ⟨x, rfl⟩ := e.surjective z
      exact (hform' x y).trans (hy x)
  let A := (D.A s).baseChange ℚ
  let Jn : {J : Module.End ℚ (ℚ ⊗[ℤ] Λ) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
    ⟨-A, by rw [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]; exact hJ⟩
  have hskewn : ∀ x y, E (Jn.1 x) y = -E x (Jn.1 y) := fun x y ↦ by
    simp only [Jn, LinearMap.neg_apply, map_neg, LinearMap.neg_apply, neg_neg]
    rw [hskew, neg_neg]
  let Jm : {J : HQ P.X 1 →ₗ[ℚ] HQ P.X 1 // J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
    ⟨P.W.J, P.W.J_sq⟩
  have hskm : ∀ x y, Em (Jm.1 x) y = -Em x (Jm.1 y) :=
    (isRosatiSkew_iff_dualForm hP.nondegenerate P.W.J).1 hP.rosati
  have heJ : ∀ x, e (Jn.1 x) = Jm.1 (e x) := fun x ↦ by
    change e (-A x) = P.W.J (e x)
    rw [map_neg, he, neg_neg]
  let eK : WithJ (ℚ ⊗[ℤ] Λ) Jn ≃ₗ[hp_K] WithJ (HQ P.X 1) Jm :=
    { toFun := fun x ↦ (WithJ.equiv Jm).symm (e (WithJ.equiv Jn x))
      invFun := fun y ↦ (WithJ.equiv Jn).symm (e.symm (WithJ.equiv Jm y))
      map_add' := fun x y ↦ by simp
      map_smul' := fun z x ↦ by
        apply (WithJ.equiv Jm).injective
        simp only [RingHom.id_apply, LinearEquiv.apply_symm_apply]
        rw [equiv_smul, equiv_smul, LinearEquiv.apply_symm_apply, map_add, map_smul, map_smul,
          heJ]
      left_inv := fun x ↦ by simp
      right_inv := fun y ↦ by simp }
  have hiso : ∀ x y, weilHermitian Em Jm hskm (eK x) (eK y) = weilHermitian E Jn hskewn x y := by
    intro x y
    ext
    · change Em (e (WithJ.equiv Jn x)) (Jm.1 (e (WithJ.equiv Jn y))) =
        E (WithJ.equiv Jn x) (Jn.1 (WithJ.equiv Jn y))
      rw [← heJ, hform']
    · exact hform' _ _
  have hev : Even (Module.finrank hp_K (WithJ (ℚ ⊗[ℤ] Λ) ⟨A, hJ⟩)) :=
    ⟨3, by rw [b64b_rank_six _ (b63hp_basis D s)]⟩
  rw [g32t_disc, weilDatumClass]
  change weilDetClass Em Jm hskm (isAlt_polarizationForm _ hP.nondegenerate)
    (nondegenerate_polarizationForm _ hP.nondegenerate) = _
  rw [weilDetClass, ← HermitianClass.detClass_eq_of_equiv _ _ (weilHermitian E Jn hskewn) _
    (isSymm_weilHermitian hEalt) (nondegenerate_weilHermitian hEnd) _ _ eK hiso]
  change weilDetClass E Jn hskewn hEalt hEnd = _
  rw [b63hp_neg_class E ⟨A, hJ⟩ Jn rfl hskew hskewn hEalt hEnd hev]
  exact hd

theorem b63hp_parabolicPolarization_aux (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s) := fun s ↦
  hp_parabolicPolarization_of_disc _ _ (b63hp_model_discriminant_aux D u₀ hroot s)

end HodgeLean.Foundations.Program
