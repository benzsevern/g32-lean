import HodgeLean.Foundations.Program.SchoenCycleU1SectionFiniteType
import HodgeLean.Foundations.Program.SchoenCycleU1AffineDualLifts
import HodgeLean.Foundations.Program.SchoenCycleU1DualTangentCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Nullstellensatz

/-! # Formal unramifiedness from the complex dual-number test -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The complex dual-number test detects formal unramifiedness of a finite map
between complex schemes of finite type.
Source: Hartshorne, Algebraic Geometry, II.8; Stacks Project, Tag 00UM;
Mathlib, `IsAlgClosed.algebraMap_bijective_of_isIntegral`. -/
theorem s2e_u1_formallyUnramified_of_dual_separation
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (hsep : Function.Injective (fun u : s2e_u1_specOver (DualNumber ℂ) ⟶ X => u ≫ f)) :
    FormallyUnramified f.left := by
  constructor
  intro U hU V hV hVU
  let R := Γ(Y.left, U)
  let S := Γ(X.left, V)
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X V
  let a := s2e_u1_appLE_algHom X Y f U V hVU
  letI : Algebra R S := a.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun r => (a.commutes r).symm)
  letI : Algebra.FiniteType ℂ S := s2e_u1_section_finiteType X V hV
  letI : Algebra.FiniteType R S := by
    rw [← RingHom.finiteType_algebraMap]
    exact f.left.finiteType_appLE hU hV hVU
  change Algebra.FormallyUnramified R S
  apply s2e_u1_unramified_of_unique_local_dual_lifts R S
  intro q hq
  let T := Localization.AtPrime q
  let K := q.ResidueField
  letI : Algebra.FiniteType ℂ K :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom ℂ S K)
      q.algebraMap_residueField_surjective
  letI : Module.Finite ℂ K := finite_of_finite_type_of_isJacobsonRing ℂ K
  let e : K ≃ₐ[ℂ] ℂ :=
    (AlgEquiv.ofBijective (Algebra.ofId ℂ K)
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
  let c := s2e_u1_specOverMap ((Algebra.ofId S T).restrictScalars ℂ)
  let i : s2e_u1_specOver T ⟶ X := c ≫ s2e_u1_fromSpecOver X V hV
  let j := s2e_u1_fromSpecOver Y U hU
  letI : IsPreimmersion c.left :=
    IsPreimmersion.of_isLocalization (R := S) (S := T) q.primeCompl
  letI : Mono i := by
    letI : Mono i.left := by dsimp [i, c, s2e_u1_fromSpecOver]; infer_instance
    exact Over.mono_of_mono_left i
  have hcomm : i ≫ f = s2e_u1_specOverMap ((Algebra.ofId R T).restrictScalars ℂ) ≫ j := by
    apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ hV.fromSpec) ≫ f.left =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ hU.fromSpec
    rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f.left hV hVU, ← Spec.map_comp_assoc]
    congr 1
  exact s2e_u1_affine_dual_lifts_unique X Y f hsep R T K e i j hcomm

end HodgeLean.Foundations.Program
