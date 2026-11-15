import HodgeLean.Foundations.Program.SchoenSchemeSectionAction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- A ring action element induces the corresponding inverse-pullback automorphism of its spectrum. -/
def s2_specActionIso (A G : Type) [CommRing A] [Group G] [MulSemiringAction G A] (g : G) :
    Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of A) where
  hom := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g⁻¹))
  inv := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g))
  hom_inv_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of A) using 1
    congr 1
    ext a
    exact inv_smul_smul g a
  inv_hom_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of A) using 1
    congr 1
    ext a
    exact smul_inv_smul g a

/-- A ring action induces an actual group action on its spectrum scheme. -/
def s2_specAction (A G : Type) [CommRing A] [Group G] [MulSemiringAction G A] :
    G →* Aut (Spec (CommRingCat.of A)) where
  toFun g := Aut.of (s2_specActionIso A G g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A (1 : G)⁻¹)) = 𝟙 _
    convert Spec.map_id (CommRingCat.of A) using 1
    congr 1
    ext a
    change (1 : G)⁻¹ • a = a
    rw [inv_one, one_smul]
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A (g * h)⁻¹)) =
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A h⁻¹)) ≫
        Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g⁻¹))
    rw [← Spec.map_comp]
    congr 1
    ext a
    change (g * h)⁻¹ • a = h⁻¹ • (g⁻¹ • a)
    rw [mul_inv_rev, mul_smul]

end HodgeLean.Foundations.Program
