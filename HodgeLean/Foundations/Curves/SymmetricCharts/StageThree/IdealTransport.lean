import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Basic

/-! # Ideal transport through scheme isomorphisms
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Transport of ideal sheaves along a scheme isomorphism.
HC no distance; AV milestone no distance.
-/
def idealTransport {X Y : Scheme} (e : X ≅ Y) :
    X.IdealSheafData ≃o Y.IdealSheafData where
  toFun I := I.map e.hom
  invFun J := J.map e.inv
  left_inv I := by simp only [← Scheme.IdealSheafData.map_comp, e.hom_inv_id,
    Scheme.IdealSheafData.map_id]
  right_inv J := by simp only [← Scheme.IdealSheafData.map_comp, e.inv_hom_id,
    Scheme.IdealSheafData.map_id]
  map_rel_iff' := by
    intro I J
    change I.map e.hom ≤ J.map e.hom ↔ I ≤ J
    constructor
    · intro h
      have := Scheme.IdealSheafData.map_mono e.inv h
      simpa only [← Scheme.IdealSheafData.map_comp, e.hom_inv_id,
        Scheme.IdealSheafData.map_id] using this
    · intro h; exact Scheme.IdealSheafData.map_mono e.hom h

/-- The subscheme of a transported ideal retains its original scheme.
HC no distance; AV milestone no distance.
-/
def subschemeTransport {X Y : Scheme} (e : X ≅ Y) (I : X.IdealSheafData) :
    I.subscheme ≅ (I.map e.hom).subscheme := by
  let J := I.map e.hom
  have hI : J.map e.inv = I := (idealTransport e).left_inv I
  let a := Scheme.IdealSheafData.subschemeMap I J e.hom le_rfl
  let b := Scheme.IdealSheafData.subschemeMap J I e.inv hI.ge
  refine ⟨a, b, ?_, ?_⟩
  · apply (cancel_mono I.subschemeι).mp
    dsimp only [a, b]
    rw [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      ← Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply (cancel_mono J.subschemeι).mp
    dsimp only [a, b]
    rw [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      ← Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The transported subscheme inclusion commutes with the ambient comparison.
HC no distance; AV milestone no distance.
-/
theorem subschemeTransport_hom_ι {X Y : Scheme} (e : X ≅ Y) (I : X.IdealSheafData) :
    (subschemeTransport e I).hom ≫ (I.map e.hom).subschemeι = I.subschemeι ≫ e.hom :=
  Scheme.IdealSheafData.subschemeMap_subschemeι I _ e.hom le_rfl

end HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
