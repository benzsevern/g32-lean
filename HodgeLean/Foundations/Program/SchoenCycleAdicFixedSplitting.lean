import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.FixedSubmodule

/-! # Adic comparison for split invariant coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open LinearMap
namespace HodgeLean.Foundations.Program

/-- Adic completion identifies a split fixed submodule with the fixed submodule of the induced projection.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1, averaging projections. -/
def s2e_adic_fixed_submodule_equiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (p : M →ₗ[R] M) (hp : p.comp p = p) :
    AdicCompletion I p.fixedSubmodule ≃ₗ[AdicCompletion I R]
      (AdicCompletion.map I p).fixedSubmodule := by
  let F := p.fixedSubmodule
  let i : F →ₗ[R] M := F.subtype
  let r : M →ₗ[R] F := p.codRestrict F (fun x => by
    change p (p x) = p x
    exact DFunLike.congr_fun hp x)
  have hri : r.comp i = LinearMap.id := by
    ext x
    change p x.val = x.val
    exact x.property
  have hir : i.comp r = p := rfl
  have hpi : p.comp i = i := by
    ext x
    exact x.property
  let ihat := AdicCompletion.map I i
  let rhat := AdicCompletion.map I r
  have himem (x : AdicCompletion I F) :
      ihat x ∈ (AdicCompletion.map I p).fixedSubmodule := by
    change AdicCompletion.map I p (AdicCompletion.map I i x) = AdicCompletion.map I i x
    rw [AdicCompletion.map_comp_apply, hpi]
  let f : AdicCompletion I F →ₗ[AdicCompletion I R]
      (AdicCompletion.map I p).fixedSubmodule := ihat.codRestrict _ himem
  let g : (AdicCompletion.map I p).fixedSubmodule →ₗ[AdicCompletion I R]
      AdicCompletion I F := rhat.comp (AdicCompletion.map I p).fixedSubmodule.subtype
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    change AdicCompletion.map I r (AdicCompletion.map I i x) = x
    rw [AdicCompletion.map_comp_apply, hri, AdicCompletion.map_id]
    rfl
  · intro x
    apply Subtype.ext
    change AdicCompletion.map I i (AdicCompletion.map I r x.val) = x.val
    rw [AdicCompletion.map_comp_apply, hir]
    exact x.property

#print axioms s2e_adic_fixed_submodule_equiv
end HodgeLean.Foundations.Program
