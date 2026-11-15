import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.LocalRing.Module

/-!
# Smoothness along the generic fibre

For a tower `R → K → S` with `K` a field of characteristic zero, `S` local, essentially of finite
type and formally smooth over `R`, the Jacobi–Zariski sequence shows that `S` is formally smooth
over `K`. Applied to stalks, every point of the source lying over the generic point of an
integral target belongs to the smooth locus, once the source is smooth over a field of
characteristic zero.
-/

open TensorProduct KaehlerDifferential IsLocalRing
namespace Algebra

variable (R K S : Type*) [CommRing R] [Field K] [CommRing S] [IsLocalRing S]
  [Algebra R K] [Algebra K S] [Algebra R S] [IsScalarTower R K S]

/-- After base change to the residue field of `S`, the map `S ⊗[K] Ω[K⁄R] → Ω[S⁄R]` is
injective, because it factors the injection `κ ⊗[K] Ω[K⁄R] → Ω[κ⁄R]`. -/
lemma gfs_lTensor_mapBaseChange_injective [FormallySmooth K (ResidueField S)] :
    Function.Injective ((mapBaseChange R K S).lTensor (ResidueField S)) := by
  let κ := ResidueField S
  have hinj : Function.Injective (mapBaseChange R K κ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (H1Cotangent.exact_δ_mapBaseChange R K κ x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  let φ : κ ⊗[S] Ω[S⁄R] →ₗ[S] Ω[κ⁄R] :=
    ((map R R S κ).liftBaseChange κ).restrictScalars S
  let e : κ ⊗[S] (S ⊗[K] Ω[K⁄R]) ≃ₗ[S] κ ⊗[K] Ω[K⁄R] :=
    (AlgebraTensorModule.cancelBaseChange K S κ κ Ω[K⁄R]).restrictScalars S
  have hcomm : φ ∘ₗ (mapBaseChange R K S).lTensor κ =
      (mapBaseChange R K κ).restrictScalars S ∘ₗ e.toLinearMap := by
    ext a s
    simp [φ, e, mapBaseChange_tmul, map_D, ← IsScalarTower.algebraMap_apply]
  intro a b hab
  apply e.injective
  apply hinj
  have := congr($hcomm a)
  have h2 := congr($hcomm b)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe] at this h2
  rw [← this, ← h2, hab]

/-- If `S` is local and formally smooth over `R`, and the residue field of `S` is formally smooth
over the intermediate field `K`, then `S` is formally smooth over `K`. -/
lemma gfs_formallySmooth_of_tower [FormallySmooth R S] [EssFiniteType R S] [EssFiniteType R K]
    [FormallySmooth K (ResidueField S)] : FormallySmooth K S := by
  have : Module.Finite K Ω[K⁄R] := inferInstance
  have : Module.Finite S Ω[S⁄R] := inferInstance
  have : Module.Free S Ω[S⁄R] := Module.free_of_flat_of_isLocalRing
  have hκ := gfs_lTensor_mapBaseChange_injective R K S
  have hfree : Module.Free S Ω[S⁄K] :=
    Module.free_of_lTensor_residueField_injective _ _ (map_surjective R K S)
      (exact_mapBaseChange_map R K S) hκ
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).mpr hκ
  have hl : Function.Injective (mapBaseChange R K S) :=
    Function.HasLeftInverse.injective ⟨l', LinearMap.congr_fun hl'⟩
  refine ⟨inferInstance, ⟨fun x y ↦ ?_⟩⟩
  have key : ∀ z : H1Cotangent K S, z = 0 := by
    intro z
    have h0 : H1Cotangent.δ R K S z = 0 := hl (by
      rw [map_zero]; exact (H1Cotangent.exact_δ_mapBaseChange R K S).apply_apply_eq_zero z)
    obtain ⟨w, rfl⟩ := (H1Cotangent.exact_map_δ R K S z).mp h0
    rw [Subsingleton.elim w 0, map_zero]
  rw [key x, key y]

/-- Formal smoothness over an intermediate field of characteristic zero. -/
lemma gfs_formallySmooth_of_tower_of_charZero [CharZero K] [FormallySmooth R S]
    [EssFiniteType R S] [EssFiniteType R K] : FormallySmooth K S := by
  have : EssFiniteType K S := .of_comp R K S
  have : EssFiniteType S (ResidueField S) := inferInstance
  have : EssFiniteType K (ResidueField S) := .comp K S (ResidueField S)
  exact gfs_formallySmooth_of_tower R K S

/-- The characteristic-zero statement for a ring `K` known to be a field through `IsField`. -/
lemma gfs_formallySmooth_of_isField {R K S : Type*} [CommRing R] [CommRing K] [CommRing S]
    [IsLocalRing S] [Algebra R K] [Algebra K S] [Algebra R S] [IsScalarTower R K S]
    (hK : IsField K) [CharZero K] [FormallySmooth R S] [EssFiniteType R S] [EssFiniteType R K] :
    FormallySmooth K S := by
  let := hK.toField
  exact gfs_formallySmooth_of_tower_of_charZero R K S

end Algebra

namespace AlgebraicGeometry

open CategoryTheory

universe u

variable {X Y : Scheme.{u}}

/-- A dominant morphism of integral schemes sends the generic point to the generic point. -/
lemma gfs_map_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  show closure {f (genericPoint X)} = Set.univ
  refine Set.eq_univ_of_univ_subset ?_
  rw [← f.denseRange.closure_range]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨z, rfl⟩
  exact specializes_iff_mem_closure.mp ((genericPoint_specializes z).map f.continuous)

/-- A point whose image has a field as stalk lies in the smooth locus, when the composite to the
spectrum of a characteristic-zero field is smooth. -/
lemma gfs_mem_smoothLocus_of_isField_stalk {k : Type u} [Field k] [CharZero k]
    (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType sY] [LocallyOfFiniteType (f ≫ sY)] [Smooth (f ≫ sY)] (x : X)
    (hx : IsField (Y.presheaf.stalk (f x))) : x ∈ f.smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus]
  have hS : (f ≫ sY).smoothLocus = ⊤ := (f ≫ sY).smoothLocus_eq_top
  have hxS : x ∈ (f ≫ sY).smoothLocus := hS ▸ trivial
  have h1 : ((f.stalkMap x).hom.comp (sY.stalkMap (f x)).hom).FormallySmooth := by
    rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.stalkMap_comp] at hxS; exact hxS
  have hR := LocallyOfFiniteType.stalkMap sY (f x)
  have h2 : ((f.stalkMap x).hom.comp (sY.stalkMap (f x)).hom).EssFiniteType := by
    have := LocallyOfFiniteType.stalkMap (f ≫ sY) x
    rw [Scheme.Hom.stalkMap_comp] at this; exact this
  let ψ : k →+* Y.presheaf.stalk (f x) := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (Spec (.of k)).presheaf.germ ⊤ (sY (f x)) trivial ≫ sY.stalkMap (f x)).hom
  have : CharZero (Y.presheaf.stalk (f x)) := by
    let := hx.toField
    exact charZero_of_injective_ringHom ψ.injective
  algebraize [(sY.stalkMap (f x)).hom, (f.stalkMap x).hom,
    (f.stalkMap x).hom.comp (sY.stalkMap (f x)).hom]
  exact Algebra.gfs_formallySmooth_of_isField (R := (Spec (.of k)).presheaf.stalk (sY (f x))) hx

/-- Every point over the generic point of an integral target lies in the smooth locus, when the
source is smooth over a characteristic-zero field compatibly with the target. -/
lemma gfs_mem_smoothLocus_of_map_eq_genericPoint {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral Y] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) (x : X) (hx : f x = genericPoint Y) : x ∈ f.smoothLocus := by
  subst hf
  refine gfs_mem_smoothLocus_of_isField_stalk sY f x ?_
  exact (Y.presheaf.stalkCongr (.of_eq hx)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField Y.functionField)

end AlgebraicGeometry
