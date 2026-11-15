module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Track B2, idempotents of a lattice: proofs

One `_aux` theorem per statement of the frozen `RelativeTorusIdempotent.lean`: the kernel of an
idempotent is the image of `1 - e`, and a symmetric idempotent splits a form orthogonally.
Mathlib only. HC no distance; AV milestone no distance.
-/

public section

namespace HodgeLean.Foundations.Program

variable {Λ : Type*} [AddCommGroup Λ]

theorem b2_ker_eq_range_aux (e : Λ →+ Λ) (he : e.comp e = e) :
    e.ker = (AddMonoidHom.id Λ - e).range := by
  have hee : ∀ x, e (e x) = e x := fun x ↦ DFunLike.congr_fun he x
  ext x
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, AddMonoidHom.sub_apply,
    AddMonoidHom.id_apply]
  constructor
  · intro h
    exact ⟨x, by rw [h, sub_zero]⟩
  · rintro ⟨y, rfl⟩
    rw [map_sub, hee, sub_self]

theorem b2_orthogonal_of_symm_aux (Q : LinearMap.BilinForm ℤ Λ) (e : Λ →+ Λ)
    (he : e.comp e = e) (hQ : ∀ x y, Q (e x) y = Q x (e y)) :
    ∀ x ∈ e.range, ∀ y ∈ (AddMonoidHom.id Λ - e).range, Q x y = 0 := by
  have hee : ∀ x, e (e x) = e x := fun x ↦ DFunLike.congr_fun he x
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [hQ, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub, hee, sub_self, map_zero]

end HodgeLean.Foundations.Program

end
