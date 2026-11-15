import HodgeLean.Foundations.Program.G32Native.PairedC3ConstantCocycle
import HodgeLean.Foundations.Program.G32Native.PairedC3EndCoefficient
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateDualGenerators
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms

/-! # Scalar endomorphisms of the actual negative line on projective space -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original base action on the unit section is the structural coefficient map. -/
theorem paired_c3_unit_base_scalar {R : Type} [CommRing R] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of R)) (U : X.Opens) (r : R) :
    letI : Module R Γ(X, U) :=
      (sectionModuleOverBase p (SheafOfModules.unit X.ringCatSheaf) U).isModule
    r • (1 : Γ(X, U)) = (p.constToPresheaf.app (op U)).hom r := by
  change (p.constToPresheaf.app (op U)).hom r * (1 : Γ(X, U)) = _
  exact mul_one _

/-- The original base morphism used by the native twisting-section complex. -/
abbrev pairedC3ProjBase (k : ℕ) := (𝟙 (pairedC3Proj k)) ≫ ProjSpace.π ℂ k

/-- Every actual global regular function is an original structural complex scalar.
Source: Hartshorne, Algebraic Geometry, III.5.1, degree-zero computation. -/
theorem paired_c3_projective_global_function_scalar (k : ℕ) (hk : 0 < k)
    (c : Γ(pairedC3Proj k, ⊤)) :
    ∃ μ : ℂ, c = ((pairedC3ProjBase k).constToPresheaf.app (op ⊤)).hom μ := by
  obtain ⟨μ, hμ⟩ := paired_c3_global_unit_section_span ℂ k hk
    (show (ProjSpace.twistingSectionPresheaf ℂ k 0).obj ⊤ from c)
  refine ⟨μ, ?_⟩
  simp only [tensorPowSection_zero] at hμ
  exact hμ.trans (paired_c3_unit_base_scalar (pairedC3ProjBase k) ⊤ μ)

/-- Every nonzero endomorphism of the actual negative line is invertible.
Source: Hartshorne, Algebraic Geometry, II.5 and III.5.1, endomorphisms of a line bundle. -/
theorem paired_c3_negative_end_zero_or_isIso (k : ℕ) (hk : 0 < k)
    (f : pairedC3NegativeLine k ⟶ pairedC3NegativeLine k) : f = 0 ∨ IsIso f := by
  obtain ⟨c, hc⟩ := paired_c3_end_coefficient_global f
    (fun i : ULift (Fin (k + 1)) => ProjSpace.standardOpen ℂ k i.down)
    (by change (⨆ i, (ProjSpace.stdCover ℂ k).U i) = ⊤
        exact (ProjSpace.stdCover ℂ k).iSup_eq_top)
    (fun i => pairedC3CoordinateDualGenerator k i.down)
    (fun i => paired_c3_coordinate_dual_generator_frame k i.down)
  obtain ⟨μ, hμ⟩ := paired_c3_projective_global_function_scalar k hk c
  by_cases hm : μ = 0
  · left
    have hc0 : c = 0 := by rw [hμ, hm, map_zero]
    apply Scheme.Modules.hom_ext (X := pairedC3Proj k) f 0
    intro U
    ext z
    change Scheme.Modules.Hom.app (X := pairedC3Proj k) f U z = 0
    have h := hc U z
    rw [hc0, map_zero, zero_smul] at h
    exact h
  · right
    apply (Scheme.Modules.Hom.isIso_iff_isIso_app (φ := f)).mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hcoef : (pairedC3Proj k).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op c =
        ((pairedC3ProjBase k).constToPresheaf.app (op U)).hom μ := by
      rw [hμ]
      exact (congrArg (fun g : CommRingCat.of ℂ ⟶ Γ(pairedC3Proj k, U) => g μ)
        ((pairedC3ProjBase k).constToPresheaf.naturality
          (homOfLE (le_top : U ≤ ⊤)).op)).symm
    have hf (z : Γ(pairedC3NegativeLine k, U)) :
        Scheme.Modules.Hom.app (X := pairedC3Proj k) f U z =
          ((pairedC3ProjBase k).constToPresheaf.app (op U)).hom μ • z :=
      (hc U z).trans (congrArg (fun a : Γ(pairedC3Proj k, U) => a • z) hcoef)
    change Function.Bijective (fun z : Γ(pairedC3NegativeLine k, U) =>
      Scheme.Modules.Hom.app (X := pairedC3Proj k) f U z)
    simp only [hf]
    exact ((Units.mk0 μ hm).isUnit.map
      ((pairedC3ProjBase k).constToPresheaf.app (op U)).hom).smul_bijective

end HodgeLean.Foundations.Program.G32Native
