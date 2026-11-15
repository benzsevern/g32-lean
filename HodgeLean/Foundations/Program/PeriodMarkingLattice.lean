import HodgeLean.Foundations.Program.PeriodMarkingDefs

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

theorem b64b_rational_nondegenerate (M : Type) [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (Q : LinearMap.BilinForm ℤ M)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M)) (hW : b2_IsWeightOne M F)
    (hR : b2_IsRiemannForm M F Q) : (Q.baseChange ℚ).Nondegenerate := by
  have hi := (b2bpol_flat_bijective M Q
    (b2_riemannForm_nondegenerate F Q hW hR)).1
  have hl (x : ℚ ⊗[ℤ] M) (hx : ∀ y, Q.baseChange ℚ x y = 0) : x = 0 := by
    apply hi
    ext v
    rw [b2bpol_flat_apply, hx]
    rfl
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [b2bpol_baseChange_skew M Q hR.alt, hy, neg_zero]

theorem b64b_baseChange_quadratic (M : Type*) [AddCommGroup M] (A : M →ₗ[ℤ] M)
    (hA : ∀ x, A (A x) = (-3 : ℤ) • x) :
    A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [LinearMap.comp_apply, map_add, LinearMap.smul_apply,
      LinearMap.id_apply] at hx hy ⊢
    exact congrArg₂ (· + ·) hx hy
  | tmul q x =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, hA,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [← TensorProduct.smul_tmul]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, zsmul_eq_mul,
      Int.cast_neg, Int.cast_ofNat, mul_comm]

theorem b64b_baseChange_skew (M : Type*) [AddCommGroup M]
    (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (hA : ∀ x y, Q (A x) y = -Q x (A y))
    (x y : ℚ ⊗[ℤ] M) :
    Q.baseChange ℚ (A.baseChange ℚ x) y = -Q.baseChange ℚ x (A.baseChange ℚ y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, neg_add]
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz, neg_add]
    | tmul r y =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        hA, neg_smul]

theorem b64b_period_centre_skew (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (x y : b63l_periodLattice C) :
    Q (b63d_periodOperator C hG x.val) y.val =
      -Q x.val (b63d_periodOperator C hG y.val) := by
  classical
  let T := b4_latticeAct ℂ (C := C) b63d_scalarElement
  have hc (z : b3_periodLattice ℂ C) : b4b_centreAct C hG z = T z := by
    simp only [b4b_centreAct, AddMonoidHom.finsetSum_apply]
    simp_rw [b63d_scalarElement_unique]
    calc
      (∑ g : b4b_Group, (if g = b63d_scalarElement then
          b4_latticeAct ℂ g else 0) z) =
          ∑ g : b4b_Group, if g = b63d_scalarElement then
            b4_latticeAct ℂ g z else 0 := by
              apply Finset.sum_congr rfl
              intro g _
              split <;> rfl
      _ = T z := by rw [Fintype.sum_ite_eq']
  have hpol : T (T y.val) + T y.val + y.val = 0 :=
    b63d_period_saturation_polynomial C hG y.val y.property
  have hinv (u v : b3_periodLattice ℂ C) : Q (T u) (T v) = Q u v :=
    b4_intersectionForm_invariant (by simp) hG Q hQ _ u v
  have he := congrArg (fun z => Q (T x.val) z) hpol
  simp only [map_add, map_zero, hinv] at he
  simp only [b63d_periodOperator, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply]
  change Q (x.val + 2 • b4b_centreAct C hG x.val) y.val =
    -Q x.val (y.val + 2 • b4b_centreAct C hG y.val)
  rw [hc, hc]
  simp only [map_add, LinearMap.add_apply, map_nsmul,
    LinearMap.smul_apply, nsmul_eq_mul]
  omega

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b64b_period_hermitian (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (e : M ≃ₗ[ℤ] b63l_periodLattice C) (A : M →ₗ[ℤ] M)
    (hsq : ∀ x, A (A x) = (-3 : ℤ) • x)
    (hA : ∀ x, (e (A x)).val = b63d_periodOperator C hG (e x).val) :
    let E : LinearMap.BilinForm ℤ M := (b63l_periodQ C Q).compl₁₂ e.toLinearMap e.toLinearMap
    ∃ hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ (A.baseChange ℚ x) y =
        -E.baseChange ℚ x (A.baseChange ℚ y),
      (b64b_latticeH M E ⟨A.baseChange ℚ, hJ⟩ hskew).IsSymm ∧
      (b64b_latticeH M E ⟨A.baseChange ℚ, hJ⟩ hskew).Nondegenerate := by
  let E : LinearMap.BilinForm ℤ M := (b63l_periodQ C Q).compl₁₂ e.toLinearMap e.toLinearMap
  obtain ⟨_, hW, hR⟩ := b63l_image_riemann C hG Q hQ
  have hW' := b63e_weightOne_comap e _ hW
  have hR' := b63e_riemann_comap e _ _ hR
  have hJ := b64b_baseChange_quadratic M A hsq
  have hz (x y : M) : E (A x) y = -E x (A y) := by
    change Q (e (A x)).val (e y).val = -Q (e x).val (e (A y)).val
    rw [hA x, hA y]
    exact b64b_period_centre_skew C hG Q hQ (e x) (e y)
  have hskew := b64b_baseChange_skew M E A hz
  refine ⟨hJ, hskew, ?_, ?_⟩
  · apply HodgeLean.Foundations.WeilHermitian.isSymm_weilHermitian
    intro x
    have hx := b2bpol_baseChange_skew M E hR'.alt x x
    linarith
  · exact HodgeLean.Foundations.WeilHermitian.nondegenerate_weilHermitian
      (b64b_rational_nondegenerate M E _ hW' hR')

end HodgeLean.Foundations.Program
