import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineFlatIdeal
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChangeTransport
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Flat conormal comparison for affine quotient presentations
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- The morphism between quotient spectra induced by scalar extension. -/
def quotientBaseChangeMap (I : Ideal R) :
    Spec (CommRingCat.of (S ⧸ I.map (algebraMap R S))) ⟶
      Spec (CommRingCat.of (R ⧸ I)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))

lemma quotientBaseChangeMap_square (I : Ideal R) :
    quotientBaseChangeMap (S := S) I ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R S)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [quotientBaseChangeMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- Flat comparison for the actual conormal sheaves of affine quotient immersions. -/
def affineQuotientFlatConormalIso [Module.Flat R S] (I : Ideal R) :
    (Scheme.Modules.pullback (quotientBaseChangeMap (S := S) I)).obj
        (sheaf (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≅
      sheaf (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (algebraMap R S))))) := by
  apply sheafIsoOfIdealIso _ _ _ _ (quotientBaseChangeMap_square I)
  apply affineFlatKernelIdealIso
  change (RingHom.ker (Ideal.Quotient.mk I)).map (algebraMap R S) =
    RingHom.ker (Ideal.Quotient.mk (I.map (algebraMap R S)))
  rw [Ideal.mk_ker, Ideal.mk_ker]

end AlgebraicGeometry.Conormal
