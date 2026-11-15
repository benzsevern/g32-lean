import HodgeLean.Foundations.Program.PeriodMarkingComparison

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.WeilHermitian
namespace HodgeLean.Foundations.Program

def b64b_withJEquiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W]
    (J : {J : Module.End ℚ V // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (K : {K : Module.End ℚ W // K ∘ₗ K = (-3 : ℚ) • LinearMap.id})
    (e : V ≃ₗ[ℚ] W) (he : ∀ x, e (J.1 x) = K.1 (e x)) :
    WithJ V J ≃ₗ[QuadraticAlgebra ℚ (-3) 0] WithJ W K :=
  { ((WithJ.equiv J).trans (e.trans (WithJ.equiv K).symm)).toAddEquiv with
    map_smul' := by
      intro z x
      apply (WithJ.equiv K).injective
      change e (WithJ.equiv J (z • x)) =
        WithJ.equiv K (z • ((WithJ.equiv K).symm (e (WithJ.equiv J x))))
      rw [equiv_smul, equiv_smul, LinearEquiv.apply_symm_apply,
        map_add, map_smul, map_smul, he] }

theorem b64b_weilHermitian_transport {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W]
    (Q : LinearMap.BilinForm ℚ V) (R : LinearMap.BilinForm ℚ W)
    (J : {J : Module.End ℚ V // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (K : {K : Module.End ℚ W // K ∘ₗ K = (-3 : ℚ) • LinearMap.id})
    (sQ : ∀ x y, Q (J.1 x) y = -Q x (J.1 y))
    (sR : ∀ x y, R (K.1 x) y = -R x (K.1 y))
    (e : V ≃ₗ[ℚ] W) (he : ∀ x, e (J.1 x) = K.1 (e x))
    (hQ : ∀ x y, R (e x) (e y) = Q x y)
    (x y : WithJ V J) :
    weilHermitian R K sR (b64b_withJEquiv J K e he x) (b64b_withJEquiv J K e he y) =
      weilHermitian Q J sQ x y := by
  apply QuadraticAlgebra.ext
  · change R (e (WithJ.equiv J x)) (K.1 (e (WithJ.equiv J y))) =
      Q (WithJ.equiv J x) (J.1 (WithJ.equiv J y))
    rw [← he, hQ]
  · exact hQ (WithJ.equiv J x) (WithJ.equiv J y)

theorem b64b_integral_pairing_transport
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Q : LinearMap.BilinForm ℤ M) (R : LinearMap.BilinForm ℤ N)
    (e : M ≃ₗ[ℤ] N) (he : ∀ x y, R (e x) (e y) = Q x y)
    (x y : ℚ ⊗[ℤ] M) :
    R.baseChange ℚ ((e.baseChange ℤ ℚ _ _) x) ((e.baseChange ℤ ℚ _ _) y) =
      Q.baseChange ℚ x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul r y =>
      simp only [LinearEquiv.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, he]

theorem b64b_integral_intertwines
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (e : M ≃ₗ[ℤ] N) (he : ∀ x, e (A x) = B (e x)) (x : ℚ ⊗[ℤ] M) :
    (e.baseChange ℤ ℚ _ _) (A.baseChange ℚ x) =
      B.baseChange ℚ ((e.baseChange ℤ ℚ _ _) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q x => simp only [LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, he]

theorem b64b_integral_hermitian_isometry
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Q : LinearMap.BilinForm ℤ M) (R : LinearMap.BilinForm ℤ N)
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (hA : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id)
    (hB : B.baseChange ℚ ∘ₗ B.baseChange ℚ = (-3 : ℚ) • LinearMap.id)
    (sA : ∀ x y, Q.baseChange ℚ (A.baseChange ℚ x) y =
      -Q.baseChange ℚ x (A.baseChange ℚ y))
    (sB : ∀ x y, R.baseChange ℚ (B.baseChange ℚ x) y =
      -R.baseChange ℚ x (B.baseChange ℚ y))
    (e : M ≃ₗ[ℤ] N) (he : ∀ x, e (A x) = B (e x))
    (hQ : ∀ x y, R (e x) (e y) = Q x y) :
    ∃ f : WithJ (ℚ ⊗[ℤ] M) ⟨A.baseChange ℚ, hA⟩ ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      WithJ (ℚ ⊗[ℤ] N) ⟨B.baseChange ℚ, hB⟩,
      ∀ x y, b64b_latticeH N R ⟨B.baseChange ℚ, hB⟩ sB (f x) (f y) =
        b64b_latticeH M Q ⟨A.baseChange ℚ, hA⟩ sA x y := by
  let eQ := e.baseChange ℤ ℚ M N
  have heQ (x : ℚ ⊗[ℤ] M) : eQ (A.baseChange ℚ x) = B.baseChange ℚ (eQ x) :=
    b64b_integral_intertwines A B e he x
  refine ⟨b64b_withJEquiv ⟨A.baseChange ℚ, hA⟩ ⟨B.baseChange ℚ, hB⟩ eQ heQ, ?_⟩
  intro x y
  exact b64b_weilHermitian_transport (Q.baseChange ℚ) (R.baseChange ℚ)
    ⟨A.baseChange ℚ, hA⟩ ⟨B.baseChange ℚ, hB⟩ sA sB eQ heQ
    (b64b_integral_pairing_transport Q R e hQ) x y

end HodgeLean.Foundations.Program
