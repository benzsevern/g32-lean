import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneRatios

/-! # Transition equations for sections of the actual hyperplane ideal -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
open Scheme.Modules.GlueOfCocycle
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The categorical ideal inclusion detects sections on every open. -/
theorem paired_ideal_inclusion_injective {X : Scheme} (I : X.IdealSheafData)
    (U : X.Opens) : Function.Injective
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        I.subschemeι.toRingCatSheafHom)).val.app (Opposite.op U)) := by
  intro s t h
  apply (idealKernelSectionsEquiv I U).injective
  apply Subtype.ext
  simpa only [idealKernelSectionsEquiv_val] using h

/-- Ideal inclusion commutes with the original restriction of sections. -/
theorem paired_ideal_inclusion_restrict {X : Scheme} (I : X.IdealSheafData)
    {U V : X.Opens} (h : V ≤ U) (s : Γ(Conormal.idealModule I.subschemeι, U)) :
    (show Γ(X, V) from (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom)).val.app (Opposite.op V)
        ((Conormal.idealModule I.subschemeι).presheaf.map (homOfLE h).op s)) =
      X.presheaf.map (homOfLE h).op
        (show Γ(X, U) from (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          I.subschemeι.toRingCatSheafHom)).val.app (Opposite.op U) s) :=
  PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom)).val (homOfLE h).op s

/-- A scalar identity in the structure sheaf detects the corresponding ideal identity. -/
theorem paired_ideal_section_smul_eq_of_inclusion {X : Scheme} (I : X.IdealSheafData)
    (U : X.Opens) (a : Γ(X, U)) (s t : Γ(Conormal.idealModule I.subschemeι, U))
    (h : a * (show Γ(X, U) from (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom)).val.app (Opposite.op U) s) =
        (show Γ(X, U) from (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          I.subschemeι.toRingCatSheafHom)).val.app (Opposite.op U) t)) :
    a • s = t := by
  apply paired_ideal_inclusion_injective I U
  exact ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    I.subschemeι.toRingCatSheafHom)).val.app (Opposite.op U)).hom.map_smul a s |>.trans h

/-- The original ratio gives a section of the ideal on the original standard open. -/
def paired_nativeHyperplaneStandardGenerator (k : ℕ) (i : Fin (k + 1)) :
    Γ(Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι,
      ProjSpace.standardOpen ℂ k i) :=
  (Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι).presheaf.map
    (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).ge).op
    (paired_nativeHyperplaneGeneratorSection k i)

/-- The section retains the scale of the specified homogeneous ratio. -/
theorem paired_nativeHyperplaneStandardGenerator_inclusion (k : ℕ) (i : Fin (k + 1)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (paired_nativeHyperplaneIdeal k).subschemeι.toRingCatSheafHom)).val.app
        (Opposite.op (ProjSpace.standardOpen ℂ k i))
        (paired_nativeHyperplaneStandardGenerator k i) =
      ProjSpace.coordinateRatioSection ℂ k i 0 := by
  unfold paired_nativeHyperplaneStandardGenerator
  erw [PresheafOfModules.naturality_apply,
    paired_nativeHyperplaneGeneratorSection_inclusion,
    paired_nativeHyperplaneChartEquiv_symm]
  let X := Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
  change X.presheaf.map (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).ge).op
    (X.presheaf.map (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).le).op
      (ProjSpace.coordinateRatioSection ℂ k i 0)) = _
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun f => f (ProjSpace.coordinateRatioSection ℂ k i 0))
    (X.presheaf.map_id _)

/-- Actual ideal generators transform contravariantly to coordinate frames. -/
theorem paired_nativeHyperplaneStandardGenerator_transition
    (k : ℕ) (i j : Fin (k + 1))
    (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).Opens)
    (hi : U ≤ ProjSpace.standardOpen ℂ k i)
    (hj : U ≤ ProjSpace.standardOpen ℂ k j) :
    rO hi (ProjSpace.coordinateRatioSection ℂ k i j) •
      (Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι).presheaf.map
        (homOfLE hj).op (paired_nativeHyperplaneStandardGenerator k j) =
      (Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι).presheaf.map
        (homOfLE hi).op (paired_nativeHyperplaneStandardGenerator k i) := by
  apply paired_ideal_section_smul_eq_of_inclusion (paired_nativeHyperplaneIdeal k) U
  let X := Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)
  have hi' := (paired_ideal_inclusion_restrict (paired_nativeHyperplaneIdeal k) hi
      (paired_nativeHyperplaneStandardGenerator k i)).trans
    (congrArg (fun t => X.presheaf.map (homOfLE hi).op t)
      (paired_nativeHyperplaneStandardGenerator_inclusion k i))
  have hj' := (paired_ideal_inclusion_restrict (paired_nativeHyperplaneIdeal k) hj
      (paired_nativeHyperplaneStandardGenerator k j)).trans
    (congrArg (fun t => X.presheaf.map (homOfLE hj).op t)
      (paired_nativeHyperplaneStandardGenerator_inclusion k j))
  exact (congrArg (fun t => rO hi (ProjSpace.coordinateRatioSection ℂ k i j) * t) hj').trans
    ((ProjSpace.coordinateRatioSection_mul ℂ k i j 0 hi hj).trans hi'.symm)

end HodgeLean.Foundations.Program.G32Native
