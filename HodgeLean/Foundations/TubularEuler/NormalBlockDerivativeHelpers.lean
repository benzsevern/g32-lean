import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Invertible block derivatives along the zero section

A real tangential shear and an invertible normal block determine an actual linear equivalence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.TubularEuler

def normalBlockContinuousLinearEquiv
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (T : N →L[ℝ] B) (A : N ≃L[ℝ] N) : (B × N) ≃L[ℝ] (B × N) := by
  let F : (B × N) →L[ℝ] (B × N) :=
    ((ContinuousLinearMap.fst ℝ B N) + T.comp (ContinuousLinearMap.snd ℝ B N)).prod
      (A.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ B N))
  let G : (B × N) →L[ℝ] (B × N) :=
    ((ContinuousLinearMap.fst ℝ B N) -
      T.comp (A.symm.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ B N))).prod
      (A.symm.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ B N))
  refine {
    toLinearEquiv := {
      toLinearMap := F.toLinearMap
      invFun := G
      left_inv := ?_
      right_inv := ?_ }
    continuous_toFun := F.continuous
    continuous_invFun := G.continuous }
  · rintro ⟨b, n⟩
    change (b + T n - T (A.symm (A n)), A.symm (A n)) = (b, n)
    rw [A.symm_apply_apply, add_sub_cancel_right]
  · rintro ⟨b, n⟩
    change (b - T (A.symm n) + T (A.symm n), A (A.symm n)) = (b, n)
    rw [A.apply_symm_apply, sub_add_cancel]

theorem normalDerivative_eq_block
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (D : (B × N) →L[ℝ] (B × N)) (A : N ≃L[ℝ] N)
    (ht : ∀ b, D (b, 0) = (b, 0))
    (hn : ∀ n, (D (0, n)).2 = A n) :
    D = (normalBlockContinuousLinearEquiv
      ((ContinuousLinearMap.fst ℝ B N).comp (D.comp (ContinuousLinearMap.inr ℝ B N)))
      A).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro p
  change D p = (p.1 + (D (0, p.2)).1, A p.2)
  have hs : p = (p.1, 0) + (0, p.2) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, zero_add, add_zero]
  calc
    D p = D (p.1, 0) + D (0, p.2) := (congrArg D hs).trans (D.map_add _ _)
    _ = (p.1 + (D (0, p.2)).1, A p.2) := by
      rw [ht p.1]
      apply Prod.ext
      · rfl
      · change 0 + (D (0, p.2)).2 = A p.2
        rw [zero_add]
        exact hn p.2

theorem derivative_on_zero_section
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : B × N → B × N) (D : Set (B × N)) (hD : IsOpen D)
    (hfix : ∀ b, (b, (0 : N)) ∈ D → f (b, 0) = (b, 0))
    (x : B) (hx : (x, (0 : N)) ∈ D)
    (F : (B × N) →L[ℝ] (B × N)) (hF : HasFDerivAt f F (x, 0)) :
    ∀ b, F (b, 0) = (b, 0) := by
  have hc : HasFDerivAt (fun b : B => f (b, (0 : N)))
      (F.comp (ContinuousLinearMap.inl ℝ B N)) x :=
    hF.comp x (ContinuousLinearMap.inl ℝ B N).hasFDerivAt
  have hevent : (fun b : B => f (b, (0 : N))) =ᶠ[𝓝 x]
      (ContinuousLinearMap.inl ℝ B N) := by
    have hbD : ∀ᶠ b in 𝓝 x, (b, (0 : N)) ∈ D :=
      ((ContinuousLinearMap.inl ℝ B N).continuous.tendsto x).eventually (hD.mem_nhds hx)
    filter_upwards [hbD] with b hb
    exact hfix b hb
  have heq : F.comp (ContinuousLinearMap.inl ℝ B N) = ContinuousLinearMap.inl ℝ B N :=
    (hc.congr_of_eventuallyEq hevent.symm).unique
      (ContinuousLinearMap.inl ℝ B N).hasFDerivAt
  intro b
  exact congrArg (fun T : B →L[ℝ] (B × N) => T b) heq

theorem hasFDerivAt_normalBlock
    {B N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : B × N → B × N) (D : Set (B × N)) (hD : IsOpen D)
    (hfix : ∀ b, (b, (0 : N)) ∈ D → f (b, 0) = (b, 0))
    (x : B) (hx : (x, (0 : N)) ∈ D)
    (F : (B × N) →L[ℝ] (B × N)) (hF : HasFDerivAt f F (x, 0))
    (A : N ≃L[ℝ] N) (hA : HasFDerivAt (fun n : N => (f (x, n)).2)
      A.toContinuousLinearMap 0) :
    HasFDerivAt f (normalBlockContinuousLinearEquiv
      ((ContinuousLinearMap.fst ℝ B N).comp (F.comp (ContinuousLinearMap.inr ℝ B N)))
      A).toContinuousLinearMap (x, 0) := by
  have hiN : HasFDerivAt (fun n : N => (x, n)) (ContinuousLinearMap.inr ℝ B N) 0 :=
    (hasFDerivAt_const x (0 : N)).prodMk (hasFDerivAt_id (0 : N))
  have hc : HasFDerivAt (fun n : N => (f (x, n)).2)
      ((ContinuousLinearMap.snd ℝ B N).comp (F.comp (ContinuousLinearMap.inr ℝ B N))) 0 :=
    (ContinuousLinearMap.snd ℝ B N).hasFDerivAt.comp 0 (hF.comp 0 hiN)
  have hn : ∀ n, (F (0, n)).2 = A n := by
    intro n
    exact congrArg (fun T : N →L[ℝ] N => T n) (hc.unique hA)
  rw [← normalDerivative_eq_block F A (derivative_on_zero_section f D hD hfix x hx F hF) hn]
  exact hF

#print axioms normalBlockContinuousLinearEquiv
#print axioms normalDerivative_eq_block
#print axioms derivative_on_zero_section
#print axioms hasFDerivAt_normalBlock

end HodgeLean.Foundations.TubularEuler
