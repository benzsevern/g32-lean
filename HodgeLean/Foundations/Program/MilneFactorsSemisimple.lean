import HodgeLean.Foundations.LieReductiveProofs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace HodgeLean.Foundations.Program

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

 def m1_commutantEndEquiv (B : Subalgebra K (Module.End K V)) :
    Subalgebra.centralizer K (B : Set (Module.End K V)) ≃+* Module.End B V where
  toFun f :=
    { f.val with
      map_smul' := by
        intro b x
        change f.val (b.val x) = b.val (f.val x)
        exact (LinearMap.congr_fun ((Subalgebra.mem_centralizer_iff K).mp f.property
          b.val b.property) x).symm }
  invFun g := ⟨g.restrictScalars K, by
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    ext x
    exact (g.map_smul (⟨b, hb⟩ : B) x).symm⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv g := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_mul' f g := by ext x; rfl


theorem m1_commutant_semisimple (B : Subalgebra K (Module.End K V))
    [FiniteDimensional K V] [IsSemisimpleModule B V] :
    IsSemisimpleRing (Subalgebra.centralizer K (B : Set (Module.End K V))) := by
  letI : Module.Finite B V := Module.Finite.of_restrictScalars_finite K B V
  letI := IsSemisimpleRing.moduleEnd B V
  exact (m1_commutantEndEquiv B).symm.isSemisimpleRing


theorem m1_baseChange_image_semisimple {A : Type*} [Field A] [Algebra K A]
    [CharZero K] [FiniteDimensional K V] (B : Subalgebra K (Module.End K V))
    [IsSemisimpleRing B] :
    IsSemisimpleRing (HodgeLean.Foundations.pol2_baseChangeRepresentation
      (A := A) B.val).range := by
  let ρ := HodgeLean.Foundations.pol2_baseChangeRepresentation (A := A) B.val
  letI : IsSemisimpleRing (TensorProduct K A B) :=
    HodgeLean.Foundations.pol2_semisimple_of_trace_separates ρ
      (HodgeLean.Foundations.pol2_trace_separates_baseChange B.val
        (HodgeLean.Foundations.pol2_trace_separates B.val Subtype.val_injective))
  exact ρ.rangeRestrict.toRingHom.isSemisimpleRing_of_surjective
    (AlgHom.rangeRestrict_surjective ρ)


theorem m1_baseChange_commutant_eq {A : Type*} [Field A] [Algebra K A]
    (B : Subalgebra K (Module.End K V)) :
    Subalgebra.centralizer A (Set.range fun b : B => b.val.baseChange A) =
      Subalgebra.centralizer A
        ((HodgeLean.Foundations.pol2_baseChangeRepresentation (A := A) B.val).range :
          Set (Module.End A (TensorProduct K A V))) := by
  let ρ := HodgeLean.Foundations.pol2_baseChangeRepresentation (A := A) B.val
  ext f
  rw [Subalgebra.mem_centralizer_iff, Subalgebra.mem_centralizer_iff]
  constructor
  · intro hf r hr
    obtain ⟨x, rfl⟩ := hr
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, add_mul, mul_add, hx, hy]
    | tmul a b =>
      change (a • b.val.baseChange A) * f = f * (a • b.val.baseChange A)
      rw [smul_mul_assoc, mul_smul_comm, hf _ ⟨b, rfl⟩]
  · intro hf r hr
    obtain ⟨b, rfl⟩ := hr
    have h := hf (ρ (TensorProduct.tmul K (1 : A) b)) ⟨TensorProduct.tmul K 1 b, rfl⟩
    simp only [ρ, HodgeLean.Foundations.pol2_baseChangeRepresentation,
      AlgHom.liftEquiv_tmul, AlgHom.comp_apply, one_smul] at h
    exact h


theorem m1_baseChange_commutant_semisimple {A : Type*} [Field A] [Algebra K A]
    [CharZero K] [FiniteDimensional K V] (B : Subalgebra K (Module.End K V))
    [IsSemisimpleRing B] :
    IsSemisimpleRing (Subalgebra.centralizer A
      (Set.range fun b : B => b.val.baseChange A)) := by
  rw [m1_baseChange_commutant_eq B]
  letI := m1_baseChange_image_semisimple (A := A) B
  exact m1_commutant_semisimple _

end HodgeLean.Foundations.Program
