import HodgeLean.Foundations.PositivePolarizationRosati

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The adjoint between two spaces with specified nondegenerate exterior two-vectors. -/
def s4_selected_cross_adjoint
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {ωV : ⋀[ℚ]^2 V} {ωW : ⋀[ℚ]^2 W}
    (hV : IsNondegenerate ωV) (hW : IsNondegenerate ωW) (F : V →ₗ[ℚ] W) :
    W →ₗ[ℚ] V :=
  (contractEquiv hV).toLinearMap.comp
    (F.dualMap.comp (contractEquiv hW).symm.toLinearMap)

/-- The cross adjoint satisfies the two specified rational alternating forms' adjunction equation. -/
theorem s4_selected_cross_adjoint_pairing
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {ωV : ⋀[ℚ]^2 V} {ωW : ⋀[ℚ]^2 W}
    (hV : IsNondegenerate ωV) (hW : IsNondegenerate ωW) (F : V →ₗ[ℚ] W)
    (x : V) (y : W) :
    dualForm hW (F x) y = dualForm hV x (s4_selected_cross_adjoint hV hW F y) := by
  simp [s4_selected_cross_adjoint, dualForm_apply, LinearMap.dualMap_apply]

/-- Extension to complex scalars preserves the adjunction equation between two rational forms. -/
theorem s4_selected_cross_adjoint_baseChange_pairing
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (E : LinearMap.BilinForm ℚ V) (D : LinearMap.BilinForm ℚ W)
    (F : V →ₗ[ℚ] W) (G : W →ₗ[ℚ] V)
    (h : ∀ x y, D (F x) y = E x (G y))
    (x : ℂ ⊗[ℚ] V) (y : ℂ ⊗[ℚ] W) :
    D.baseChange ℂ (F.baseChange ℂ x) y = E.baseChange ℂ x (G.baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul b w => simp [LinearMap.BilinForm.baseChange_tmul, h]

/-- An adjoint into a nondegenerate isotropic splitting preserves the corresponding isotropic subspace. -/
theorem s4_selected_cross_adjoint_map_isotropic
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (E : LinearMap.BilinForm ℂ V) (D : LinearMap.BilinForm ℂ W) (hE : E.Nondegenerate)
    (P Q : Submodule ℂ V) (R : Submodule ℂ W) (hPQ : P ⊔ Q = ⊤)
    (hP : ∀ x ∈ P, ∀ y ∈ P, E x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, E x y = 0)
    (hR : ∀ x ∈ R, ∀ y ∈ R, D x y = 0)
    (F : V →ₗ[ℂ] W) (G : W →ₗ[ℂ] V)
    (hFG : ∀ x y, D (F x) y = E x (G y)) (hF : P.map F ≤ R) :
    R.map G ≤ P := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Submodule.mem_sup.mp (hPQ ▸ Submodule.mem_top : G y ∈ P ⊔ Q)
  have hq0 : q = 0 := by
    apply hE.2
    intro w
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
      Submodule.mem_sup.mp (hPQ ▸ Submodule.mem_top : w ∈ P ⊔ Q)
    have h1 : E w₁ q = 0 := by
      have h := hFG w₁ y
      rw [hR _ (hF ⟨w₁, hw₁, rfl⟩) _ hy, ← hpq, map_add, hP _ hw₁ _ hp, zero_add] at h
      exact h.symm
    rw [map_add, LinearMap.add_apply, h1, hQ _ hw₂ _ hq, add_zero]
  rw [← hpq, hq0, add_zero]
  exact hp

#print axioms s4_selected_cross_adjoint
#print axioms s4_selected_cross_adjoint_pairing
#print axioms s4_selected_cross_adjoint_baseChange_pairing
#print axioms s4_selected_cross_adjoint_map_isotropic
end HodgeLean.Foundations.Program
