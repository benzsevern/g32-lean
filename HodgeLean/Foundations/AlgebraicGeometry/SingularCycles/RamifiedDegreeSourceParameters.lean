import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeSectionGerms
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeOpenLength
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeIdentitySlice
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeDimension

/-! # Affine source slices from regular target parameters

Flat pullback preserves the target regular sequence. Its quotient length
is unchanged by restriction to an affine source neighbourhood.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem affine_source_parameter_slice
    {Y X Z : Over (Spec (CommRingCat.of ℂ))} (j : Y ⟶ X) [IsOpenImmersion j.left]
    (f : X ⟶ Z) [Flat f.left]
    (U : Z.left.Opens) (himage : (⊤ : Y.left.Opens) ≤ (j ≫ f).left ⁻¹ᵁ U)
    (w : ComplexPoint Y) (d : ℕ) (g : Fin d → Γ(Z.left, U))
    (hreg : RingTheory.Sequence.IsRegular (Z.left.presheaf.stalk ((j ≫ f).left w.underlying))
      (List.ofFn fun k => Z.left.presheaf.germ U ((j ≫ f).left w.underlying)
        (himage (by trivial)) (g k)))
    (hgen : Ideal.ofList (List.ofFn fun k =>
      Z.left.presheaf.germ U ((j ≫ f).left w.underlying) (himage (by trivial)) (g k)) =
      IsLocalRing.maximalIdeal (Z.left.presheaf.stalk ((j ≫ f).left w.underlying)))
    (m : ℕ) (hm : pointFibreLength f.left (j.left w.underlying) = m) :
    let s := fun k => (j ≫ f).left.appLE U ⊤ himage (g k)
    RingTheory.Sequence.IsRegular (Y.left.presheaf.stalk w.underlying)
      (a3b4a_gysin_sliceSequence Y.hom (𝟙 Y.left) ⊤ s 0 w.underlying (by trivial)) ∧
    a3b4a_gysin_sliceLength Y.hom (𝟙 Y.left) ⊤ s 0 w = m := by
  let F := j ≫ f
  letI : Flat F.left := inferInstanceAs (Flat (j.left ≫ f.left))
  let s := fun k => F.left.appLE U ⊤ himage (g k)
  have hr := regular_appLE_parameter_germs_pullback F.left U ⊤ himage w.underlying
    (by trivial) g hreg
  have hlength := appLE_parameter_quotient_length_eq_fibreLength F.left U ⊤ himage
    w.underlying (by trivial) g hgen
  have hopen := pointFibreLength_comp_open_of_parameters j.left f.left w.underlying
    (List.ofFn fun k => Z.left.presheaf.germ U (F.left w.underlying)
      (himage (by trivial)) (g k)) hgen
  constructor
  · rw [identity_slice_sequence]
    exact hr
  · rw [identity_slice_length]
    exact hlength.trans (hopen.trans hm)

end AlgebraicGeometry.SingularCycles
