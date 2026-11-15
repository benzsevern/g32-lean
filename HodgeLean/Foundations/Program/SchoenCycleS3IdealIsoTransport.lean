import HodgeLean.Foundations.Program.SchoenCycleS3AdaptedPoints
import HodgeLean.Foundations.Program.SchoenCycleResidueProjectivePoints

/-! # Transport of reduced projective loci through scheme isomorphisms -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program

/-- Pulling an ideal back through an isomorphism is its image through the inverse. -/
theorem s2e_ideal_comap_iso {X Y : Scheme} (e : X ≅ Y) (I : Y.IdealSheafData) :
    I.comap e.hom = I.map e.inv := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le,
      ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  · calc
      I.map e.inv = ((I.map e.inv).comap e.inv).comap e.hom := by
        rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
          Scheme.IdealSheafData.comap_id]
      _ ≤ I.comap e.hom := Scheme.IdealSheafData.comap_mono _
        (Scheme.IdealSheafData.comap_map_le I e.inv)

/-- Isomorphism pullback transports the reduced ideal of a closure by the inverse point map. -/
theorem s2e_vanishing_closure_comap_iso {X Y : Scheme} (e : X ≅ Y) (S : Set Y) :
    (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure S)).comap e.hom =
      Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (e.inv '' S)) := by
  rw [s2e_ideal_comap_iso, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  exact closure_image_closure e.inv.continuous

/-- The point action of a projective basis change determines its pullback on reduced coefficient ideals. -/
theorem s2e_coefficient_ideal_transport {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1)
    (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] V) (L : V →ₗ[ℂ] ℂ)
    (j : Fin (k + 1)) (hb : ∀ v, L (b v) = v j)
    (e : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (he : ∀ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
      e.hom.left (vectorToComplexPoint v hv).underlying =
        (vectorToComplexPoint ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun) v)
          ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun).map_ne_zero_iff.mpr hv)).underlying) :
    (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
      (Point.underlying ''
        {R : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) |
          ∃ (v : V) (hv : v ≠ 0),
            (s2e_finiteDimensionalProjectivePointEquiv k hd).symm R =
              Projectivization.mk ℂ v hv ∧ L v = 0}))).comap e.hom.left =
      s2e_s2b_residueIdeal k j := by
  let es : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ≅
      ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) :=
    ⟨e.hom.left, e.inv.left, congrArg (fun f => f.left) e.hom_inv_id,
      congrArg (fun f => f.left) e.inv_hom_id⟩
  have hinv (v : Fin (k + 1) → ℂ) (hv : v ≠ 0) :
      e.inv.left
        (vectorToComplexPoint ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun) v)
          ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun).map_ne_zero_iff.mpr hv)).underlying =
        (vectorToComplexPoint v hv).underlying := by
    rw [← he v hv]
    exact (Scheme.homeoOfIso es).symm_apply_apply _
  rw [s2e_vanishing_closure_comap_iso es,
    s2e_coefficient_locus_change_basis k hd b L]
  have hset : e.inv.left ''
      {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0), L (b v) = 0 ∧
        p = (vectorToComplexPoint
          ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun) v)
          ((b.trans (Module.finBasisOfFinrankEq ℂ V hd).equivFun).map_ne_zero_iff.mpr hv)).underlying} =
      {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0), v j = 0 ∧
        p = (vectorToComplexPoint v hv).underlying} := by
    ext p
    constructor
    · rintro ⟨q, ⟨v, hv, hz, rfl⟩, rfl⟩
      exact ⟨v, hv, (hb v).symm.trans hz, hinv v hv⟩
    · rintro ⟨v, hv, hz, rfl⟩
      exact ⟨_, ⟨v, hv, (hb v).trans hz, rfl⟩, hinv v hv⟩
  change Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
    (e.inv.left '' _)) = _
  rw [hset]
  unfold s2e_s2b_residueIdeal
  congr 1
  apply TopologicalSpace.Closeds.ext
  exact s2e_coordinate_hyperplane_closure k j

end HodgeLean.Foundations.Program
