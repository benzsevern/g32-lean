import HodgeLean.Foundations.Abdulali.DefiniteQuaternion
import HodgeLean.Foundations.Program.G32Native.TypeIIIPaperDefs
import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitUnit

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option Elab.async false
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Abdulali

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {r : ℕ}

/-- Restriction of an actual sum morphism to one factor recovers its coefficient.
Source: Mac Lane, Categories for the Working Mathematician, §VIII.2, biproduct identities. -/
theorem incl_sumMap (power : AbelianPowerData A Y r)
    (f : Fin r → AbelianEnd A) (i : Fin r) :
    power.incl i ≫ power.sumMap f = (f i).hom := by
  classical
  rw [AbelianPowerData.sumMap]
  have hcomp (s : Finset (Fin r)) :
      power.incl i ≫ ∏ j ∈ s, (power.proj j ≫ (f j).hom) =
        ∏ j ∈ s, power.incl i ≫ (power.proj j ≫ (f j).hom) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, Finset.prod_insert hj, MonObj.comp_mul, ih]
  rw [hcomp Finset.univ]
  simp only [← Category.assoc, power.incl_proj]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    rw [ite_eq_right (Ne.symm hji), MonObj.one_comp]
  · simp

/-- A sum morphism with a rationally invertible coefficient is smooth.
Source: Mumford, Abelian Varieties, §19, rational inverses of isogenies;
smoothness of surjective homomorphisms in characteristic zero. -/
theorem sumMap_smooth_of_isUnit (power : AbelianPowerData A Y r)
    (f : Fin r → AbelianEnd A) (i : Fin r)
    (hi : IsUnit ((1 : ℚ) ⊗ₜ[ℤ] f i : AbelianEnd0 A)) :
    Smooth (power.sumMap f).left := by
  obtain ⟨u, hu⟩ := hi
  have hinj := unit_integral_multiple_injective A u 1 (f i) (by norm_num)
    (by simpa only [one_smul] using hu)
  let V : AbelianQuotient.Variety :=
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hsurj := AbelianQuotient.surjective_of_injective_h1
    (A := V) (B := V) ⟨(f i).hom, inferInstance⟩ hinj
  letI := spec_g4_isMonHom_sumMap power f
  apply ccm3_smooth_surjective_group_hom (power.sumMap f)
  intro x
  obtain ⟨z, hz⟩ := hsurj x
  refine ⟨Point.map (power.incl i) z, ?_⟩
  change Point.map (f i).hom z = x at hz
  rw [← hz]
  change (z ≫ power.incl i) ≫ power.sumMap f = z ≫ (f i).hom
  rw [Category.assoc, incl_sumMap]

/-- Scalar extension into the rational endomorphism algebra is faithful.
Source: Mumford, Abelian Varieties, §19; faithfulness of the degree-one action. -/
theorem end_integral_injective : Function.Injective
    (fun f : AbelianEnd A => ((1 : ℚ) ⊗ₜ[ℤ] f : AbelianEnd0 A)) := by
  intro f g h
  have hh := congrArg (abelianEnd0Action A) h
  rw [spec_g4_abelianEnd0Action_tmul, spec_g4_abelianEnd0Action_tmul,
    one_smul, one_smul] at hh
  exact spec_abelianEndAction_injective A (MulOpposite.op_injective hh)

variable (A)
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- In the definite quaternion endomorphism algebra every nonzero integral
endomorphism is rationally invertible.
Source: Mumford, Abelian Varieties, §19, definite quaternion algebras. -/
theorem typeIII_integral_isUnit (P : GeneralPELMember A W pol hM)
    (f : AbelianEnd A) (hf : f ≠ 0) :
    IsUnit ((1 : ℚ) ⊗ₜ[ℤ] f : AbelianEnd0 A) := by
  have hj : ((1 : ℚ) ⊗ₜ[ℤ] f : AbelianEnd0 A) ≠ 0 := by
    intro h
    apply hf
    apply end_integral_injective
    simpa only [TensorProduct.tmul_zero] using h
  have hq : P.end0.symm ((1 : ℚ) ⊗ₜ[ℤ] f) ≠ 0 := by
    intro h
    apply hj
    have hh := congrArg P.end0 h
    simpa only [P.end0.apply_symm_apply, map_zero] using hh
  have h := (definiteQuaternion_isUnit P.b P.b_neg _ hq).map P.end0.toMonoidHom
  change IsUnit (P.end0 (P.end0.symm ((1 : ℚ) ⊗ₜ[ℤ] f))) at h
  rwa [P.end0.apply_symm_apply] at h

/-- Nonzero quaternionic sum maps on arbitrary power data are smooth.
Source: Mumford, Abelian Varieties, §19; surjective homomorphisms in characteristic zero. -/
theorem typeIII_sumMap_smooth (P : GeneralPELMember A W pol hM)
    (power : AbelianPowerData A Y r) (f : Fin r → AbelianEnd A) (hf : f ≠ 0) :
    Smooth (power.sumMap f).left := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra h
    apply hf
    funext i
    exact not_not.mp (not_exists.mp h i)
  exact sumMap_smooth_of_isUnit power f i (typeIII_integral_isUnit A W pol hM P _ hi)

/-- Every integral quaternionic sum morphism preserves the algebraic cycle span,
including the zero map and codimension zero.
Source: Fulton, Intersection Theory, §1.7, flat pullback; Mumford, Abelian Varieties, §19. -/
theorem typeIII_sumMap_algebraic (P : GeneralPELMember A W pol hM)
    (power : AbelianPowerData A Y r) (f : Fin r → AbelianEnd A) (p : ℕ) :
    (algebraicCycleClassSpan A p).map (homPullback (power.sumMap f) (2*p)) ≤
      algebraicCycleClassSpan Y p := by
  classical
  by_cases hf : f = 0
  · subst f
    have hz : power.sumMap (0 : Fin r → AbelianEnd A) = 1 := by
      simp [AbelianPowerData.sumMap]
    rw [hz]
    exact ccm2_homPullback_one_span p
  · letI := typeIII_sumMap_smooth A W pol hM P power f hf
    exact smoothPullback_span _ p

#print axioms incl_sumMap
#print axioms sumMap_smooth_of_isUnit
#print axioms end_integral_injective
#print axioms typeIII_integral_isUnit
#print axioms typeIII_sumMap_smooth
#print axioms typeIII_sumMap_algebraic
end HodgeLean.Foundations.Abdulali
