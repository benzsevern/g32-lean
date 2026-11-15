import HodgeLean.Foundations.Program.MilneCentralizerProofs

noncomputable section

open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m1_adjoint_eq_of {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (f g : Module.End K V)
    (h : ∀ x y, dualForm hω (f x) y = dualForm hω x (g y)) :
    m0_adjoint hω f = g := by
  ext y
  refine sub_eq_zero.1 ((nondegenerate_dualForm hω).2 _ fun x => ?_)
  rw [map_sub, ← m0_adjoint_pair, h, sub_self]

theorem m1_adjoint_involutive {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) : Function.Involutive (m0_adjoint hω) := by
  intro f
  have hs : ∀ x y, dualForm hω x y = -dualForm hω y x := fun x y =>
    ((isAlt_dualForm hω).neg_eq y x).symm
  apply m1_adjoint_eq_of
  intro x y
  rw [hs, ← m0_adjoint_pair, hs, neg_neg]

def m1_adjointLinear {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) :
    Module.End K V →ₗ[K] Module.End K V where
  toFun := m0_adjoint hω
  map_add' f g := m1_adjoint_eq_of hω _ _ fun x y => by
    simp only [LinearMap.add_apply, map_add, m0_adjoint_pair]
  map_smul' c f := m1_adjoint_eq_of hω _ _ fun x y => by
    simp only [LinearMap.smul_apply, map_smul, m0_adjoint_pair, RingHom.id_apply]

theorem m1_adjoint_mul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ω : ⋀[K]^2 V} (hω : IsNondegenerate ω) (f g : Module.End K V) :
    m0_adjoint hω (f * g) = m0_adjoint hω g * m0_adjoint hω f := by
  apply m1_adjoint_eq_of
  intro x y
  simp only [Module.End.mul_apply, m0_adjoint_pair]

end HodgeLean.Foundations.Program
