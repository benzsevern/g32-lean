import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneComap

/-! # Exact principal generators under open pullback -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Open pullback carries a specified principal ideal generator through the actual
coordinate-ring isomorphism, rather than merely preserving its vanishing locus. -/
theorem conormal_principal_ideal_open_pullback {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (I : Y.IdealSheafData) (U : X.affineOpens)
    (a : Γ(Y, f ''ᵁ U.1))
    (ha : I.ideal ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩ = Ideal.span {a}) :
    (I.comap f).ideal U = Ideal.span {((f.appIso U.1).hom).hom a} := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, ha]
  let e := (f.appIso U.1).commRingCatIsoToRingEquiv
  change Ideal.comap e.symm.toRingHom (Ideal.span {a}) = Ideal.span {e a}
  erw [← Ideal.map_comap_of_equiv e, Ideal.map_span, Set.image_singleton]
  rfl

end HodgeLean.Foundations.Program.G32Native
