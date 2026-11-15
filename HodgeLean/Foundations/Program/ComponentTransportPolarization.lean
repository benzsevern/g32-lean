import HodgeLean.Foundations.Program.ComponentTransportDefs
import HodgeLean.Foundations.Program.PeriodMarkingHermitianTransport
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
set_option backward.isDefEq.respectTransparency false
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful


open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
set_option maxHeartbeats 400000 in
theorem b65y_normalization {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice c D.C D.hC
      (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))) (s : b6t_polydisc c)
    (Z : g32t_Sixfold) (hZ : Z = b65z_fiber D B s)
    (hn : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Z.X) Z.pol)) :
    let Λ := b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s
    let E := b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) s (D.P s) (D.Q s)
    let X := Z.X
    letI := (torusCohomology_cupProductOf X).finite
    ∃ e : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] HQ X 1,
      (∀ y, e ((D.A s).baseChange ℚ y) = -Z.W.J (e y)) ∧
      ∃ r : ℚ, r = 1 ∧ 0 < r ∧
        ∀ y z, polarizationForm (torusCohomology_cupProductOf X) hn
          (e y) (e z) = r * E.baseChange ℚ y z := by
  subst Z
  intro Λ E X
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let L₀ := b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
  let E₀ := b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
    (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))
  let A₀ := b63g2_operator c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
  let G := b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P
    (b65z_s₀ c) s
  have hW := b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c) (Subset.refl _)
    D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk
    D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) s
  obtain ⟨-, T, hT, -⟩ := b63l_fibre_image_transport c D.C D.hC s (b65z_s₀ c)
  let er : (ℚ ⊗[ℤ] L₀) ≃ₗ[ℚ] HQ X 1 := b64e_model_rational L₀ G hW.1 E₀ hW.2
  have hTA : ∀ x, T (D.A s x) = A₀ (T x) := by
    intro x
    apply Subtype.val_injective
    rw [hT, D.hA s x]
    change _ = (A₀ (T x)).val
    rw [b63g2_operator_val, hT]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
      map_add, map_nsmul]
    rw [b63d_centre_transport c D.C D.hC (b6t_polydisc c) (Subset.refl _)
      (b65z_s₀ c) s x.val]
  have hTE : ∀ x y, E₀ (T x) (T y) = E x y := by
    intro x y
    change D.Q (b65z_s₀ c) (D.P (b65z_s₀ c) (T x).val) (D.P (b65z_s₀ c) (T y).val) =
      D.Q s (D.P s x.val) (D.P s y.val)
    rw [hT, hT]
    exact b63e_pairing_constant c D.C (b6t_polydisc c) (Subset.refl _)
      D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP
      s (b65z_s₀ c) x.val y.val
  have hJeq : (b65z_fiber D B s).W.J =
      b63g_modelOperator L₀ G hW.1 E₀ hW.2 A₀.toAddMonoidHom := rfl
  have hrJ : ∀ v, er (A₀.baseChange ℚ v) = -(b65z_fiber D B s).W.J (er v) := by
    intro v
    rw [hJeq]
    exact b63hp_model_rational_action L₀ G hW.1 E₀ hW.2 A₀.toAddMonoidHom
      (b63g2_operator_skew c D.C D.hC (b6t_polydisc c) (Subset.refl _)
        (b65z_s₀ c) (D.hG _) (D.P _) (D.hP _) (D.Q _) (D.hQ _)) v
  have hsix := b63hp_sixfold_form L₀ G hW.1 E₀ hW.2 A₀.toAddMonoidHom
      (b63g2_operator_sq c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
        (D.hG (b65z_s₀ c)))
      (b63g2_operator_filtration c D.C D.hC (b6t_polydisc c) (Subset.refl _)
        D.hG D.P D.hP (b65z_s₀ c) s)
  have hrE : ∀ v w, polarizationForm (torusCohomology_cupProductOf X) hn
      (er v) (er w) = E₀.baseChange ℚ v w := by
    intro v w
    exact hsix hn v w
  refine ⟨(LinearEquiv.baseChange ℤ ℚ _ _ T).trans er, ?_, 1, rfl, one_pos, ?_⟩
  · intro x
    change er (T.toLinearMap.baseChange ℚ ((D.A s).baseChange ℚ x)) =
      -(b65z_fiber D B s).W.J (er (T.toLinearMap.baseChange ℚ x))
    have hc : T.toLinearMap.baseChange ℚ ∘ₗ (D.A s).baseChange ℚ =
        A₀.baseChange ℚ ∘ₗ T.toLinearMap.baseChange ℚ := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      exact LinearMap.ext hTA
    rw [← LinearMap.comp_apply, hc, LinearMap.comp_apply, hrJ]
  · intro x y
    rw [one_mul]
    change polarizationForm (torusCohomology_cupProductOf X) hn
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

set_option maxHeartbeats 400000 in
theorem b65y_polarized_disc_eq (Z Z' : g32t_Sixfold)
    (h : g32t_PolarizedWeil Z) (h' : g32t_PolarizedWeil Z')
    (e : HQ Z.X 1 ≃ₗ[ℚ] HQ Z'.X 1)
    (heJ : ∀ x, e (Z.W.J x) = Z'.W.J (e x))
    (heE : ∀ x y, polarizationForm (torusCohomology_cupProductOf Z'.X) h'.nondegenerate
      (e x) (e y) = polarizationForm (torusCohomology_cupProductOf Z.X) h.nondegenerate x y) :
    g32t_disc h = g32t_disc h' := by
  letI := (torusCohomology_cupProductOf Z.X).finite
  letI := (torusCohomology_cupProductOf Z'.X).finite
  let E := polarizationForm (torusCohomology_cupProductOf Z.X) h.nondegenerate
  let E' := polarizationForm (torusCohomology_cupProductOf Z'.X) h'.nondegenerate
  let J := (⟨Z.W.J, Z.W.J_sq⟩ :
    {J : Module.End ℚ (HQ Z.X 1) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
  let J' := (⟨Z'.W.J, Z'.W.J_sq⟩ :
    {J : Module.End ℚ (HQ Z'.X 1) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
  exact (weilDetClass_equiv J J' E E' e heJ heE
    ((isRosatiSkew_iff_dualForm h.nondegenerate Z.W.J).1 h.rosati)
    ((isRosatiSkew_iff_dualForm h'.nondegenerate Z'.W.J).1 h'.rosati)
    (isAlt_polarizationForm _ h.nondegenerate) (isAlt_polarizationForm _ h'.nondegenerate)
    (nondegenerate_polarizationForm _ h.nondegenerate)
    (nondegenerate_polarizationForm _ h'.nondegenerate)).symm

set_option maxHeartbeats 400000 in
theorem b65y_disc_of_comparisons {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W] (A : V →ₗ[ℚ] V) (B : W →ₗ[ℚ] W)
    (Q : LinearMap.BilinForm ℚ V) (R : LinearMap.BilinForm ℚ W)
    (f : V ≃ₗ[ℚ] W) (hfA : ∀ x, f (A x) = B (f x))
    (hfE : ∀ x y, R (f x) (f y) = Q x y)
    (Z Z' : g32t_Sixfold) (h : g32t_PolarizedWeil Z) (h' : g32t_PolarizedWeil Z')
    (e : V ≃ₗ[ℚ] HQ Z.X 1) (e' : W ≃ₗ[ℚ] HQ Z'.X 1)
    (heA : ∀ x, e (A x) = -Z.W.J (e x))
    (heA' : ∀ x, e' (B x) = -Z'.W.J (e' x))
    (heE : ∀ x y, polarizationForm (torusCohomology_cupProductOf Z.X) h.nondegenerate
      (e x) (e y) = Q x y)
    (heE' : ∀ x y, polarizationForm (torusCohomology_cupProductOf Z'.X) h'.nondegenerate
      (e' x) (e' y) = R x y) : g32t_disc h = g32t_disc h' := by
  let u := e.symm.trans (f.trans e')
  apply b65y_polarized_disc_eq Z Z' h h' u
  · intro x
    obtain ⟨v, rfl⟩ := e.surjective x
    have hJ : Z.W.J (e v) = -e (A v) := by rw [heA, neg_neg]
    rw [hJ, map_neg]
    dsimp only [u, LinearEquiv.trans_apply]
    rw [e.symm_apply_apply, e.symm_apply_apply, hfA, heA', neg_neg]
  · intro x y
    obtain ⟨v, rfl⟩ := e.surjective x
    obtain ⟨w, rfl⟩ := e.surjective y
    dsimp only [u, LinearEquiv.trans_apply]
    rw [e.symm_apply_apply, e.symm_apply_apply, heE', heE, hfE]

end HodgeLean.Foundations.Program
