import HodgeLean.Foundations.Program.SchoenCycleC2TowerDimensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

/-! # Conormal frames for the supplied projective slice in the Cartier tower -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Every supplied projective immersion into the retained tower has the expected conormal rank. -/
theorem paired_retained_slice_conormal_frames
    (Z B₀ : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom]
    [IsIntegral B₀.left] [LocallyOfFiniteType B₀.hom]
    (k r : ℕ) (γ : g3_power Z (2 * k) ⟶ B₀) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (i : Fin (r + 1))
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B i)
    [IsClosedImmersion ℓ.left] (x : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ))) :
    ∃ U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal ℓ.left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) := by
  have hdim := s2e_retained_tower_dimension Z B₀
    (SmoothOfRelativeDimension.dim_eq (f := Z.hom) 1) (2 * k) r γ hsurj
    B e₀ b D hcartier hblowup i
  letI : SmoothOfRelativeDimension (k + k) (B i).hom := by
    have h := (inferInstance : SmoothOfRelativeDimension
      (TopologicalSpace.dim (B i).left) (B i).hom)
    simpa only [hdim, two_mul] using h
  letI : SmoothOfRelativeDimension k
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension k
  exact s2e_smooth_closedImmersion_conormal_frames _ _ k k ℓ x

#print axioms paired_retained_slice_conormal_frames

end HodgeLean.Foundations.Program.G32Native
