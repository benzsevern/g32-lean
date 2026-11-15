module

public import HodgeLean.Foundations.Program.SchoenTowerFoundC1bProofs

@[expose] public section

/-! # C1: off-centre inverse for a specified modification
Implication from an explicit image-ideal universal property and an open avoiding its support.
The output identifies the actual inverse-image open with the specified base open.
Generic-point recursion and normalization remain in their separate units.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Away from the ideal support, a specified universal modification has an actual inverse.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.14;
Stacks Project, Tag 01OF, Lemmas 31.33.4(1) and 31.33.5. -/
theorem s2t_cartierUniversal_offCentre {B X : Scheme.{0}}
    (I : B.IdealSheafData) (b : X ⟶ B)
    (huniv : ∀ (T : Scheme.{0}) (f : T ⟶ B),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X, u ≫ b = f)
    (U : B.Opens) (hU : ∀ x ∈ U, x ∉ I.support) :
    ∃! e : (b ⁻¹ᵁ U).toScheme ≅ U.toScheme,
      e.hom = b ∣_ U ∧ e.inv ≫ (b ⁻¹ᵁ U).ι ≫ b = U.ι :=
  s2t_cartierUniversal_offCentre_aux I b huniv U hU

example := @s2t_cartierUniversal_offCentre

end HodgeLean.Foundations.Program
