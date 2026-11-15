import HodgeLean.Foundations.Program.G32WeilLineAssemblyCupSpan
import HodgeLean.Foundations.Program.G32ContractionClassMultiply
import HodgeLean.Foundations.Program.G32ContractionScalar
import HodgeLean.Foundations.Program.CycleFoundationsPullbackSpan
import HodgeLean.Adapters.DegreeZeroUnconditional
import HodgeLean.Adapters.KleimanProduct

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf algebraicCycleClassSpan

theorem g32c_finite_wedge_span (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    letI := (torusCohomology_cupProductOf Y).finite
    ∀ (r : ℕ) (n : Fin r → ℕ)
      (x : ∀ j, ⋀[ℂ]^(2 * n j) (ℂ ⊗[ℚ] HQ Y 1)),
      (∀ j, f1575ExteriorCohomology (torusCohomology_cupProductOf Y) _ (x j) ∈
        (algebraicCycleClassSpan Y (n j)).baseChange ℂ) →
      ∀ (p : ℕ), 2 * p = ∑ j, 2 * n j →
      ∀ z : ⋀[ℂ]^(2 * p) (ℂ ⊗[ℚ] HQ Y 1),
      (z : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)) = (List.ofFn fun j => (x j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1))).prod →
      f1575ExteriorCohomology (torusCohomology_cupProductOf Y) _ z ∈
        (algebraicCycleClassSpan Y p).baseChange ℂ := by
  letI := (torusCohomology_cupProductOf Y).finite
  intro r
  induction r with
  | zero =>
    intro n x hx p hp z hz
    have hp0 : p = 0 := by simpa only [Finset.univ_eq_empty, Finset.sum_empty,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using hp
    subst p
    rw [algebraicCycleClassSpan_zero_eq_top_unconditional Y,
      Submodule.baseChange_top]
    trivial
  | succ r ih =>
    intro n x hx p hp z hz
    let q := ∑ j : Fin r, n j.succ
    have hq : ∑ j : Fin r, 2 * n j.succ = 2 * q := (Finset.mul_sum _ _ _).symm
    have hd : 2 * n 0 + 2 * q = 2 * p := by
      rw [Fin.sum_univ_succ, hq] at hp
      exact hp.symm
    let w : ⋀[ℂ]^(2 * q) (ℂ ⊗[ℚ] HQ Y 1) := ⟨_, by
      rw [← hq]
      simpa only [List.sum_ofFn] using SetLike.list_prod_ofFn_mem_graded (A := fun i : ℕ => ⋀[ℂ]^i (ℂ ⊗[ℚ] HQ Y 1))
        (fun j : Fin r => 2 * n j.succ) (fun j => (x j.succ : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)))
        (fun j => (x j.succ).property)⟩
    have hw := ih (fun j => n j.succ) (fun j => x j.succ) (fun j => hx j.succ)
      q hq.symm w rfl
    have hz' : z = ⟨(x 0 : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)) * (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ Y 1)),
        hd ▸ SetLike.mul_mem_graded (x 0).property w.property⟩ := by
      apply Subtype.ext
      rw [hz, List.ofFn_succ, List.prod_cons]
    rw [hz', f1575ExteriorCohomology_eq_baseChange, g32c_cupExterior_wedge Y _ _ _ hd]
    apply g32c_cupC_span Y (n 0) q p hd
    · simpa only [f1575ExteriorCohomology_eq_baseChange] using hx 0
    · simpa only [f1575ExteriorCohomology_eq_baseChange] using hw

theorem g32c_finite_projection_hom : ∀ (r : ℕ) (Y : Fin r → Over (Spec ↧ℂ))
    [∀ i, GrpObj (Y i)] [∀ i, IsCommMonObj (Y i)] (j : Fin r),
    IsMonHom (cfd_proj r Y j)
  | 0, _, _, _, j => j.elim0
  | r + 1, Y, _, _, j => by
    refine Fin.cases ?_ (fun i => ?_) j
    · change IsMonHom (fst (Y 0) (cfd_product r (fun i => Y i.succ)))
      infer_instance
    · letI := g32c_finite_projection_hom r (fun j => Y j.succ) i
      change IsMonHom (snd (Y 0) (cfd_product r (fun i => Y i.succ)) ≫
        cfd_proj r (fun i => Y i.succ) i)
      infer_instance


end HodgeLean.Foundations.Program
