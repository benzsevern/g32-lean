import HodgeLean.Foundations.Curves.Picard.LineBundles.Transport
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Sections of the Cartier kernel ideal

The categorical kernel defining the divisor ideal agrees with the kernel
of the restriction map on every open set.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Evaluation identifies the sheaf kernel with the module kernel. -/
def idealKernelSectionsEquiv {X : Scheme} (I : X.IdealSheafData) (U : X.Opens) :
    Γ(idealModule I, U) ≃ₗ[Γ(X, U)]
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)).map
        (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).hom.ker :=
  ((PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U))
      (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≪≫
    ModuleCat.kernelIsoKer _).toLinearEquiv

theorem idealKernelSectionsEquiv_val {X : Scheme} (I : X.IdealSheafData)
    (U : X.Opens) (s : Γ(idealModule I, U)) :
    ((idealKernelSectionsEquiv I U) s).val =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
        (Opposite.op U) s := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)
  let f := SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom
  letI : E.Additive := { map_add := by intros; rfl }
  have h : (PreservesKernel.iso E f).hom ≫ (ModuleCat.kernelIsoKer (E.map f)).hom ≫
      ModuleCat.ofHom (E.map f).hom.ker.subtype = E.map (kernel.ι f) := by
    simp only [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom]
    simp
  exact congrArg (fun g => g s) h

/-- On an affine open, the module kernel is the specified ideal. -/
def idealAffineSectionsEquiv {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens) :
    Γ(idealModule I, U.1) ≃ₗ[Γ(X, U.1)] I.ideal U := by
  refine (idealKernelSectionsEquiv I U.1).trans (LinearEquiv.ofEq _ _ ?_)
  ext a
  change (I.subschemeι.app U.1).hom a = 0 ↔ a ∈ I.ideal U
  exact Set.ext_iff.mp (congrArg (fun J : Ideal Γ(X, U.1) => (J : Set Γ(X, U.1)))
    (I.ker_subschemeι_app U)) a

theorem idealAffineSectionsEquiv_val {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (s : Γ(idealModule I, U.1)) :
    ((idealAffineSectionsEquiv I U) s).val =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
        (Opposite.op U.1) s :=
  idealKernelSectionsEquiv_val I U.1 s

/-- A regular generator gives a linear frame for affine ideal sections. -/
def idealAffineGeneratorEquiv {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens)
    (a : Γ(X, U.1)) (ha : IsRegular a) (hI : I.ideal U = Ideal.span {a}) :
    Γ(X, U.1) ≃ₗ[Γ(X, U.1)] Γ(idealModule I, U.1) := by
  let f : Γ(X, U.1) →ₗ[Γ(X, U.1)] I.ideal U := {
    toFun r := ⟨r * a, by rw [hI]; exact Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩⟩
    map_add' r s := Subtype.ext (add_mul r s a)
    map_smul' r s := Subtype.ext (mul_assoc r s a) }
  refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).trans (idealAffineSectionsEquiv I U).symm
  · intro r s hrs
    exact ha.right (congrArg Subtype.val hrs)
  · intro s
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (show (s : Γ(X, U.1)) ∈ Ideal.span {a} by simpa only [hI] using s.property)
    exact ⟨r, Subtype.ext hr⟩

/-- Restriction between affine opens preserves a regular equation. -/
theorem regular_restrict_affine {X : Scheme} (U V : X.affineOpens) (hVU : V ≤ U)
    (a : Γ(X, U.1)) (ha : IsRegular a) :
    IsRegular (X.presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op a) := by
  let φ := (X.presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op).hom
  have hf : φ.Flat := by
    simpa [φ, Scheme.Hom.appLE] using
      (𝟙 X : X ⟶ X).flat_appLE U.2 V.2 (show V.1 ≤ (𝟙 X) ⁻¹ᵁ U.1 from hVU)
  letI := φ.toAlgebra
  letI : Module.Flat Γ(X, U.1) Γ(X, V.1) := hf
  have hr := Module.Flat.isSMulRegular_of_isRegular (M := Γ(X, V.1)) ha
  apply (Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr
  intro r s hrs
  apply hr
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hrs

/-- Affine ideal coordinates commute with restriction of actual sheaf sections. -/
theorem idealAffineSectionsEquiv_restrict {X : Scheme} (I : X.IdealSheafData)
    (U V : X.affineOpens) (hVU : V ≤ U) (s : Γ(idealModule I, U.1)) :
    ((idealAffineSectionsEquiv I V)
      ((idealModule I).presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op s)).val =
      X.presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op
        (((idealAffineSectionsEquiv I U) s).val) := by
  rw [idealAffineSectionsEquiv_val, idealAffineSectionsEquiv_val]
  exact PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val
    (homOfLE (show V.1 ≤ U.1 from hVU)).op s

theorem idealAffineGeneratorEquiv_coordinate {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : IsRegular a)
    (hI : I.ideal U = Ideal.span {a}) (r : Γ(X, U.1)) :
    ((idealAffineSectionsEquiv I U) (idealAffineGeneratorEquiv I U a ha hI r)).val = r * a := by
  change ((idealAffineSectionsEquiv I U)
    ((idealAffineSectionsEquiv I U).symm ⟨r * a, _⟩)).val = r * a
  rw [LinearEquiv.apply_symm_apply]

end HodgeLean.Foundations.Curves.Picard.LineBundles
