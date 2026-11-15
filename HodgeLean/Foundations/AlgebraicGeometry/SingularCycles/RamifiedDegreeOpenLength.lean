import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreePointLength
import HodgeLean.Adapters.NormalConeB4aGysinSliceEquiv

/-! # Parameter quotient lengths on an open source neighbourhood

The stalk map of an open immersion is an isomorphism. Transport through it
preserves the full quotient length of every finite parameter list.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace AlgebraicGeometry.SingularCycles

theorem parameter_quotient_length_pullback_open
    {Y X : Scheme} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    (rs : List (X.presheaf.stalk (j y))) :
    Module.length (X.presheaf.stalk (j y)) (X.presheaf.stalk (j y) ⧸ Ideal.ofList rs) =
      Module.length (Y.presheaf.stalk y)
        (Y.presheaf.stalk y ⧸ Ideal.ofList (rs.map (j.stalkMap y).hom)) := by
  let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  exact a3b4a_gysin_slice_length_ringEquiv e rs

theorem pointFibreLength_comp_open_of_parameters
    {Y X Z : Scheme} (j : Y ⟶ X) [IsOpenImmersion j] (f : X ⟶ Z) (y : Y)
    (rs : List (Z.presheaf.stalk (f (j y))))
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal (Z.presheaf.stalk (f (j y)))) :
    pointFibreLength (j ≫ f) y = pointFibreLength f (j y) := by
  let κ : Z.presheaf.stalk (f (j y)) →+* Y.presheaf.stalk y := ((j ≫ f).stalkMap y).hom
  have h := parameter_quotient_length_pullback_open j y (rs.map (f.stalkMap (j y)).hom)
  have hleft : pointFibreLength (j ≫ f) y =
      Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸ Ideal.ofList (rs.map κ)) := by
    calc
      _ = Module.length (Y.presheaf.stalk y)
          (Y.presheaf.stalk y ⧸ (Ideal.ofList rs).map κ) := by
        exact congrArg (fun I => Module.length (Y.presheaf.stalk y)
          (Y.presheaf.stalk y ⧸ I)) (congrArg (Ideal.map κ) hgen).symm
      _ = _ := by rw [Ideal.map_ofList]
  have hright : pointFibreLength f (j y) =
      Module.length (X.presheaf.stalk (j y))
        (X.presheaf.stalk (j y) ⧸ Ideal.ofList (rs.map (f.stalkMap (j y)).hom)) := by
    unfold pointFibreLength
    rw [← hgen, Ideal.map_ofList]
  have hlist : rs.map κ = (rs.map (f.stalkMap (j y)).hom).map (j.stalkMap y).hom := by
    rw [List.map_map]
    apply congrArg (fun t : Z.presheaf.stalk (f (j y)) → Y.presheaf.stalk y => rs.map t)
    funext a
    exact ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_comp j f y) a
  rw [hleft, hright, hlist]
  exact h.symm

end AlgebraicGeometry.SingularCycles
