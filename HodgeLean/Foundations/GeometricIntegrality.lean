import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Integrality over algebraically closed fields

HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations

open scoped TensorProduct

noncomputable section

private theorem exists_specialization
    (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (a : A) (ha : a ≠ 0) :
    ∃ f : A →ₐ[k] k, f a ≠ 0 := by
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isRadical_bot
  obtain ⟨m, ⟨_, hm⟩, ham⟩ := Ideal.eq_jacobson_iff_notMem.mp hj a ha
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let g : A ⧸ m →ₐ[k] k := IsAlgClosed.lift
  refine ⟨g.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  intro hzero
  apply ham
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply g.injective
  simpa using hzero

private def specializeTensor {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] k) : A ⊗[k] B →ₐ[k] B :=
  Algebra.TensorProduct.lift ((Algebra.ofId k B).comp f) (AlgHom.id k B)
    (fun _ _ ↦ Commute.all _ _)

private theorem specializeTensor_coord {k A B ι : Type*} [Field k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (b : Module.Basis ι k B) (f : A →ₐ[k] k) (t : A ⊗[k] B) (i : ι) :
    b.repr (specializeTensor f t) i = f ((b.baseChange A).repr t i) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
      simp only [specializeTensor, Algebra.TensorProduct.lift_tmul,
        AlgHom.comp_apply, AlgHom.id_apply, Algebra.ofId_apply,
        Module.Basis.baseChange_repr_tmul]
      rw [← Algebra.smul_def]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_comm _ _
  | add x y hx hy => simp [map_add, hx, hy]

/-- Tensor products of domains over an algebraically closed field are domains when
the first algebra is finitely generated. No finite generation of the second is needed.

Source: Stacks Project, Tag 05P3, proof of Lemma 33.3.3 (specialization of coefficients).
HC no distance; AV milestone no distance. -/
theorem isDomain_tensorProduct_of_isAlgClosed
    (k A B : Type*) [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsDomain B]
    [Algebra.FiniteType k A] : IsDomain (A ⊗[k] B) := by
  classical
  let b := Module.Free.chooseBasis k B
  let e := (b.baseChange A).repr
  have hc (t : A ⊗[k] B) (ht : t ≠ 0) : ∃ i, e t i ≠ 0 := by
    by_contra! h
    apply ht
    apply e.injective
    ext i
    simpa using h i
  let : NoZeroDivisors (A ⊗[k] B) := ⟨by
    intro x y hxy
    by_contra! h
    obtain ⟨i, hi⟩ := hc x h.1
    obtain ⟨j, hj⟩ := hc y h.2
    obtain ⟨f, hf⟩ := exists_specialization k A (e x i * e y j) (mul_ne_zero hi hj)
    have hfx : specializeTensor (B := B) f x ≠ 0 := by
      intro hx
      have := specializeTensor_coord b f x i
      rw [hx, map_zero, Finsupp.zero_apply] at this
      exact hf (by simp [map_mul, ← this, e])
    have hfy : specializeTensor (B := B) f y ≠ 0 := by
      intro hy
      have := specializeTensor_coord b f y j
      rw [hy, map_zero, Finsupp.zero_apply] at this
      exact hf (by simp [map_mul, ← this, e])
    exact mul_ne_zero hfx hfy (by rw [← map_mul, hxy, map_zero])⟩
  exact NoZeroDivisors.to_isDomain _

example (k A B : Type*) [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsDomain B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] : IsDomain (A ⊗[k] B) :=
  isDomain_tensorProduct_of_isAlgClosed k A B

end

end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.isDomain_tensorProduct_of_isAlgClosed
