import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineSchemeConormalMono
import HodgeLean.Foundations.Program.G32Native.UnionConormalBaseChangeMono
import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalExact
import HodgeLean.Foundations.Program.G32Native.UnionConormalResLEClosed
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison

/-! # Left injectivity for the natural smooth conormal flag -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The first natural conormal map of a flag of smooth closed immersions
is injective. Formal smoothness splits the affine cotangent map,
and the split injection persists under scalar extension.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.8.17. -/
theorem paired_c3_smooth_conormal_first_mono_aux
    (Q F X : Scheme.{0})
    (q : Q ⟶ Spec ↧ℂ) (φ : F ⟶ Spec ↧ℂ) (x : X ⟶ Spec ↧ℂ)
    [Smooth q] [Smooth φ] [Smooth x]
    (i : F ⟶ X) (j : Q ⟶ F) (hi : i ≫ x = φ) (hj : j ≫ φ = q)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    Mono (Conormal.comparisonMap i (j ≫ i) (𝟙 _) j (by rw [Category.comp_id])) := by
  change Mono (unionConormalFirst i (j ≫ i) j rfl)
  apply unionConormal_mono_of_open_neighborhoods
  intro z
  obtain ⟨U, hU, hz, _⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (U := ⊤) (x := (j ≫ i) z) (show (j ≫ i) z ∈ (⊤ : X.Opens) from trivial)
  let UF := i ⁻¹ᵁ U
  let UQ := (j ≫ i) ⁻¹ᵁ U
  have hEq : UQ = j ⁻¹ᵁ UF := by
    change (j ≫ i) ⁻¹ᵁ U = j ⁻¹ᵁ (i ⁻¹ᵁ U)
    rw [Scheme.Hom.comp_preimage]
  let j' := j.resLE UF UQ hEq.le
  have hb : j' ≫ UF.ι = UQ.ι ≫ j := j.resLE_comp_ι hEq.le
  have ha' : j' ≫ (i ∣_ U) = (j ≫ i) ∣_ U := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb,
      Category.assoc, morphismRestrict_ι]
  let sx := U.ι ≫ x
  let sf := UF.ι ≫ φ
  let sq := UQ.ι ≫ q
  haveI : Smooth sx := by dsimp only [sx]; infer_instance
  haveI : Smooth sf := by dsimp only [sf]; infer_instance
  have hi' : (i ∣_ U) ≫ sx = sf := by
    dsimp only [sx, sf]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hi]
  have hj' : j' ≫ sf = sq := by
    dsimp only [sf, sq]
    rw [← Category.assoc, hb, Category.assoc, hj]
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine UF.toScheme := hU.preimage i
  haveI : IsAffine UQ.toScheme := hU.preimage (j ≫ i)
  haveI : IsClosedImmersion j' :=
    unionConormal_resLE_isClosedImmersion j UF UQ hEq.le hEq
  haveI : Mono (unionConormalFirst (i ∣_ U) ((j ≫ i) ∣_ U) j' ha') :=
    paired_c3_affine_scheme_conormal_first_mono U.toScheme UF.toScheme UQ.toScheme
      sx sf sq (i ∣_ U) ((j ≫ i) ∣_ U) j' ha' hi' hj'
  have h₀ : UF.ι ≫ i = (i ∣_ U) ≫ U.ι := (morphismRestrict_ι i U).symm
  have h₁ : UQ.ι ≫ (j ≫ i) = ((j ≫ i) ∣_ U) ≫ U.ι :=
    (morphismRestrict_ι (j ≫ i) U).symm
  haveI : IsIso (Conormal.idealPullbackMap i (i ∣_ U) U.ι UF.ι h₀) :=
    Conormal.idealPullbackMap_open_isIso i U
  haveI : IsIso (Conormal.idealPullbackMap (j ≫ i) ((j ≫ i) ∣_ U) U.ι UQ.ι h₁) :=
    Conormal.idealPullbackMap_open_isIso (j ≫ i) U
  haveI : Mono (Conormal.comparisonMap (i ∣_ U) ((j ≫ i) ∣_ U)
      (𝟙 _) j' (ha'.trans (Category.comp_id _).symm)) := by
    change Mono (unionConormalFirst (i ∣_ U) ((j ≫ i) ∣_ U) j' ha')
    infer_instance
  have hmono := unionConormal_baseChange_mono i (j ≫ i) j rfl
    (i ∣_ U) ((j ≫ i) ∣_ U) j' ha' U.ι UF.ι UQ.ι h₀ h₁ hb
  haveI : Mono ((Scheme.Modules.pullback UQ.ι).map
      (unionConormalFirst i (j ≫ i) j rfl)) := hmono
  exact ⟨UQ, hz, unionConormal_mono_map_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback UQ.ι).symm
    (unionConormalFirst i (j ≫ i) j rfl)⟩

#print axioms paired_c3_smooth_conormal_first_mono_aux

end HodgeLean.Foundations.Program.G32Native
