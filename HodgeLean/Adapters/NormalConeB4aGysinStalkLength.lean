import HodgeLean.Adapters.NormalConeB4aGysinMultiplicity
import HodgeLean.Adapters.NormalConeB4aGysinLocalizedFibre

/-! # Image-cycle coefficients on the actual source scheme

The image of an immersion is isomorphic to its source, including its local
rings. Consequently the image-cycle coefficient retains the source stalk length.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The coefficient of an immersed component is the exact length of its source local ring. -/
theorem a3b4a_gysin_imageCycle_coeff_stalkLength
    {Z K : Scheme.{0}} [IsNoetherian Z] (i : K ⟶ Z) [IsClosedImmersion i]
    (y : K) (hy : y ∈ genericPoints K) :
    a3b3_imageCycle i inferInstance (i y) =
      ((Module.length (K.presheaf.stalk y) (K.presheaf.stalk y)).toNat : ℚ) := by
  have hy' : i.toImage y ∈ genericPoints i.ker.subscheme :=
    (a3b2_homeomorph_mem_genericPoints (Scheme.homeoOfIso (asIso i.toImage)) y).2 hy
  have hpt : i.ker.subschemeι (i.toImage y) = i y := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
  rw [a3b3_imageCycle, ← hpt, a3b2_idealCycle_apply i.ker _ _ ⟨i.toImage y, hy'⟩]
  congr 1
  rw [a3b2_genericLength, ENat.lift_eq_toNat_of_lt_top]
  exact congrArg ENat.toNat
    (a3b2_length_eq_of_ringEquiv (asIso (i.toImage.stalkMap y)).commRingCatIsoToRingEquiv)


/-- At a point on just one immersed component, normalization uses the length
of the actual source stalk at that component's generic point. -/
theorem a3b4a_gysin_multiplicity_eq_source_stalkLength
    {Z K : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (i : K ⟶ Z) [IsClosedImmersion i] (y : K) (hy : y ∈ genericPoints K)
    (x : ComplexPoint (Over.mk q))
    (hx : x.underlying ∈ closure ({i y} : Set Z))
    (hother : ∀ η ∈ (a3b3_imageCycle i inferInstance).support,
      η ≠ i y → x.underlying ∉ closure ({η} : Set Z)) :
    a3b4_multiplicity q (a3b3_imageCycle i inferInstance) x =
      ((Module.length (K.presheaf.stalk y) (K.presheaf.stalk y)).toNat : ℚ) := by
  have hy' : i.toImage y ∈ genericPoints i.ker.subscheme :=
    (a3b2_homeomorph_mem_genericPoints (Scheme.homeoOfIso (asIso i.toImage)) y).2 hy
  have hpt : i.ker.subschemeι (i.toImage y) = i y := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
  have hξ : i y ∈ (a3b3_imageCycle i inferInstance).support := by
    rw [a3b3_imageCycle, a3b4a_gysin_idealCycle_support]
    exact ⟨i.toImage y, hy', hpt⟩
  rw [a3b4a_classMultiplicity_eq_component q _ _ hξ x hx hother,
    a3b4a_gysin_imageCycle_coeff_stalkLength i y hy]

end HodgeLean.Adapters
