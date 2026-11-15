import HodgeLean.Foundations.Program.PrymFamilyB4Defs
import HodgeLean.Foundations.Program.RelativeTorusAbelian
import HodgeLean.Foundations.Program.RelativeTorusVHSPol

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

def b4b_addHomLinearEquiv (Λ : Type) [AddCommGroup Λ] :
    (Λ →+ ℚ) ≃ₗ[ℚ] b2b_dual Λ where
  toFun f := f.toIntLinearMap
  invFun f := f.toAddMonoidHom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def b4b_periodLinearEquiv
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : HQ X 1 ≃ₗ[ℚ] b2b_dual (b2_abelianLattice X) :=
  (abelianPeriodEquiv X).trans (b4b_addHomLinearEquiv (b2_abelianLattice X))

theorem b4b_h10_period
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    letI := (torusCohomology_cupProductOf X).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian X)
      (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
      (torusCohomology_cupProductOf X)
    (S.weight1.H (1, 0)).map
        (LinearEquiv.baseChange ℚ ℂ _ _ (b4b_periodLinearEquiv X)).toLinearMap =
      b2b_hodgeOne (b2_abelianLattice X) (b2_abelianF X) := by
  letI := (torusCohomology_cupProductOf X).finite
  let S := abelianVarietyCohomologyOf (finiteBetti_abelian X)
    (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
    (torusCohomology_cupProductOf X)
  dsimp only [S]
  change (cohomologyHodgePiece X 1 (1, 0)).map
      (LinearEquiv.baseChange ℚ ℂ _ _ (b4b_periodLinearEquiv X)).toLinearMap = _
  rw [spec_g4_cohomologyHodgePiece_one_eq X]
  simp only [latticeHodgePieces, if_pos (by norm_num : (1 : ℤ) = 1)]
  have hpair : (b2b_pairing (b2_abelianLattice X)).comp
      (LinearEquiv.baseChange ℚ ℂ _ _ (b4b_periodLinearEquiv X)).toLinearMap =
      b2_abelianPairing X := by
    apply LinearMap.ext
    intro u
    induction u using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul c x =>
      apply LinearMap.ext
      intro v
      induction v using TensorProduct.inductionOn with
      | add y z hy hz => rw [map_add, map_add, hy, hz]
      | tmul d l => rfl
  ext z
  simp only [Submodule.mem_map, b2b_hodgeOne, Submodule.mem_comap,
    Submodule.mem_dualAnnihilator]
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    simp only [if_true] at hx
    rw [← b2_abelianHodgeF_eq X] at hy
    change ((b2b_pairing (b2_abelianLattice X)).comp
      (LinearEquiv.baseChange ℚ ℂ _ _ (b4b_periodLinearEquiv X)).toLinearMap) x y = 0
    rw [hpair]
    have hx' : x ∈ (abelianWeightOneHodgeStructure X).H (1, 0) := by
      change x ∈ cohomologyHodgePiece X 1 (1, 0)
      rw [spec_g4_cohomologyHodgePiece_one_eq X]
      simpa [latticeHodgePieces] using hx
    exact (Submodule.mem_dualCoannihilator _).1 hy _ (Submodule.mem_map_of_mem hx')
  · intro hz
    let e := LinearEquiv.baseChange ℚ ℂ _ _ (b4b_periodLinearEquiv X)
    have heqpair : b2b_pairing (b2_abelianLattice X) z =
        b2_abelianPairing X (e.symm z) := by
      rw [← hpair]
      change b2b_pairing (b2_abelianLattice X) z =
        b2b_pairing (b2_abelianLattice X) (e (e.symm z))
      rw [e.apply_symm_apply]
    have hz' : b2_abelianPairing X (e.symm z) ∈
        (b2_abelianHodgeF X).dualAnnihilator := by
      rw [← heqpair, b2_abelianHodgeF_eq X]
      exact (Submodule.mem_dualAnnihilator _).2 hz
    rw [b2_abelianHodgeF, Subspace.dualCoannihilator_dualAnnihilator_eq] at hz'
    obtain ⟨x, hx, hxeq⟩ := hz'
    have hPinj : Function.Injective (b2_abelianPairing X) := by
      rw [← hpair]
      exact (b2bpol_pairing_bijective (b2_abelianLattice X)).1.comp e.injective
    have hxval : x = e.symm z := hPinj hxeq
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    rw [← hxval]
    have hx' : x ∈ cohomologyHodgePiece X 1 (1, 0) := hx
    rw [spec_g4_cohomologyHodgePiece_one_eq X] at hx'
    simpa [latticeHodgePieces] using hx'

end HodgeLean.Foundations.Program
