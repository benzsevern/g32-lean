import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import HodgeLean.Foundations.Program.SchoenTransferR2GenericFactor
import HodgeLean.Foundations.Program.SchoenTowerChecks

/-! # Component factors through the actual exceptional preimage

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A component generically mapping into a blowup centre factors through the
actual exceptional preimage in the specified cover.
Source: Hartshorne, Algebraic Geometry, II.7; Schoen (1988), Lemma 2.6, p. 18.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_generic_exceptional_factor
    {Q W B' B : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData) (β : W ⟶ B') (f : Q ⟶ W)
    [QuasiCompact (f ≫ β ≫ b).left]
    (h : (f ≫ β ≫ b).left (genericPoint Q.left) ∈ I.support) :
    ∃ ρ : Q ⟶ s2b_preimage β
        (pullback.fst b (s2c_subschemeι B I)),
      ρ ≫ s2b_toCover β (pullback.fst b (s2c_subschemeι B I)) = f := by
  obtain ⟨g, hg⟩ := s4_assembly_generic_subscheme_factor (f ≫ β ≫ b).left I h
  let K := s2c_subscheme B I
  let kι := s2c_subschemeι B I
  let gO : Q ⟶ K := Over.homMk g (by
    change g ≫ I.subschemeι ≫ B.hom = Q.hom
    rw [← Category.assoc, hg, Over.w])
  have hgO : gO ≫ kι = f ≫ β ≫ b := Over.OverMorphism.ext hg
  let e : Q ⟶ pullback b kι := pullback.lift (f ≫ β) gO (by
    simpa only [Category.assoc] using hgO.symm)
  let ρ : Q ⟶ s2b_preimage β (pullback.fst b kι) :=
    pullback.lift f e (by
      exact (pullback.lift_fst (f ≫ β) gO (by
        simpa only [Category.assoc] using hgO.symm)).symm)
  exact ⟨ρ, pullback.lift_fst _ _ _⟩

#print axioms s4_assembly_generic_exceptional_factor
end HodgeLean.Foundations.Program
