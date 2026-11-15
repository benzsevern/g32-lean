import HodgeLean.Adapters.KleimanCoheightCharts
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A flat locally quasi-finite morphism preserves point coheight on locally
Noetherian schemes. -/
theorem s2e_coheight_eq_of_flat_locallyQuasiFinite
    {X Y : Scheme} (f : X ⟶ Y) [Flat f] [LocallyQuasiFinite f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X) :
    Order.coheight x = Order.coheight (f x) := by
  apply hc9k8_coheight_eq_of_flat f x
  intro y hy hyx
  let F := f ⁻¹' ({f x} : Set Y)
  letI : DiscreteTopology F :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (f x))
  let y' : F := ⟨y, hy⟩
  let x' : F := ⟨x, Set.mem_singleton _⟩
  have hs : y' ⤳ x' := Topology.IsInducing.subtypeVal.specializes_iff.mp hyx
  exact congrArg Subtype.val hs.eq

/-- An étale restriction over a smooth complex base preserves coheight at
every point lying over that restriction. -/
theorem s2e_coheight_eq_of_finite_etale_near
    {W B : Over (Spec ↧ℂ)} [Smooth B.hom]
    (β : W ⟶ B) (U : B.left.Opens)
    (hfin : IsFinite (β.left ∣_ U)) (he : Etale (β.left ∣_ U))
    (w : W.left) (hw : β.left w ∈ U) :
    Order.coheight w = Order.coheight (β.left w) := by
  let V := β.left ⁻¹ᵁ U
  letI : Etale (β.left ∣_ U) := he
  letI : IsFinite (β.left ∣_ U) := hfin
  letI : Smooth (U.ι ≫ B.hom) := inferInstance
  letI : Smooth (V.ι ≫ W.hom) := by
    have hs : Smooth ((β.left ∣_ U) ≫ U.ι ≫ B.hom) := inferInstance
    rw [morphismRestrict_ι_assoc, Over.w β] at hs
    exact hs
  letI : IsLocallyNoetherian U.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ B.hom)
  letI : IsLocallyNoetherian V.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ W.hom)
  let y : V.toScheme := ⟨w, hw⟩
  calc
    Order.coheight w = Order.coheight y := coheight_eq_of_isOpenImmersion (x := y) V.ι
    _ = Order.coheight ((β.left ∣_ U) y) :=
      s2e_coheight_eq_of_flat_locallyQuasiFinite (β.left ∣_ U) y
    _ = Order.coheight (β.left w) := by
      have hp : U.ι ((β.left ∣_ U) y) = β.left w := morphismRestrict_base_coe β.left U y
      rw [← hp]
      exact (coheight_eq_of_isOpenImmersion (x := (β.left ∣_ U) y) U.ι).symm

end HodgeLean.Foundations.Program
