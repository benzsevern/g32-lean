import HodgeLean.Adapters.NormalConeB4aGysinBridgeDefs

/-! # The literal identity-immersion slice

For the identity immersion and the whole affine source, the zero-parameter
slice is the quotient by the supplied global parameter germs.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.SingularCycles

theorem identity_slice_sequence
    {K : Scheme.{0}} (q : K ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (g : Fin d → Γ(K, ⊤)) (w : K) :
    a3b4a_gysin_sliceSequence q (𝟙 K) ⊤ g 0 w (by trivial) =
      List.ofFn (fun j => K.presheaf.germ ⊤ w (by trivial) (g j)) := by
  apply congrArg List.ofFn
  funext j
  change K.presheaf.germ ⊤ w _ (g j - a3b4a_gysin_sectionConst q ⊤ 0) = _
  rw [map_zero, sub_zero]

theorem identity_slice_length
    {K : Scheme.{0}} (q : K ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (g : Fin d → Γ(K, ⊤)) (w : ComplexPoint (Over.mk q)) :
    a3b4a_gysin_sliceLength q (𝟙 K) ⊤ g 0 w =
      Module.length (K.presheaf.stalk w.underlying)
        (K.presheaf.stalk w.underlying ⧸ Ideal.ofList
          (List.ofFn fun j => K.presheaf.germ ⊤ w.underlying (by trivial) (g j))) := by
  classical
  have hseq : a3b4a_gysin_sliceSequence q (𝟙 K) ⊤ g 0 w.underlying (by trivial) =
      List.ofFn (fun j => K.presheaf.germ ⊤ w.underlying (by trivial) (g j)) := by
    apply congrArg List.ofFn
    funext j
    change K.presheaf.germ ⊤ w.underlying _
      (g j - a3b4a_gysin_sectionConst q ⊤ 0) = _
    rw [map_zero, sub_zero]
  unfold a3b4a_gysin_sliceLength
  rw [dif_pos (show (𝟙 K) w.underlying ∈ (⊤ : K.Opens) from by trivial), hseq]

end AlgebraicGeometry.SingularCycles
