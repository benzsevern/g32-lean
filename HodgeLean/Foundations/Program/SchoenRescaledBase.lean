import HodgeLean.Foundations.Program.SchoenRescaledCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unit basic chart computes the actual degree-zero structure morphism. -/
theorem s2_basicOpenOne_ι_toSpecZero {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] :
    (Proj.basicOpen 𝒜 (1 : A)).ι ≫ Proj.toSpecZero 𝒜 =
      Proj.basicOpenToSpec 𝒜 1 ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers (1 : A)))) := by
  have hι : (Proj.basicOpen 𝒜 (1 : A)).ι =
      (Scheme.isoOfEq (Proj 𝒜) (Proj.basicOpen_one 𝒜)).hom ≫
        (Scheme.topIso (Proj 𝒜)).hom :=
    (Scheme.isoOfEq_hom_ι (Proj 𝒜) (Proj.basicOpen_one 𝒜)).symm
  rw [hι, Proj.toSpecZero]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

namespace S2RescaledProj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Proj rescaling morphism respects the retained degree-zero base. -/
theorem map_toSpecZero {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))] :
    map 𝒜 D hD ≫ Proj.toSpecZero (fun n => 𝒜 (D * n)) = Proj.toSpecZero 𝒜 := by
  let e := Scheme.isoOfEq (Proj 𝒜) (Proj.basicOpen_one 𝒜)
  have hι : (Proj.basicOpen 𝒜 (1 : A)).ι = e.hom ≫ (Scheme.topIso (Proj 𝒜)).hom :=
    (Scheme.isoOfEq_hom_ι (Proj 𝒜) (Proj.basicOpen_one 𝒜)).symm
  haveI : IsIso (Proj.basicOpen 𝒜 (1 : A)).ι := by rw [hι]; infer_instance
  apply (cancel_epi (Proj.basicOpen 𝒜 (1 : A)).ι).mp
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (map 𝒜 D hD) (show
    Proj.basicOpen 𝒜 (1 : A) ≤ map 𝒜 D hD ⁻¹ᵁ
      Proj.basicOpen (fun n => 𝒜 (D * n)) (1 : A) from le_rfl)]
  simp only [Category.assoc, s2_basicOpenOne_ι_toSpecZero]
  rw [← Category.assoc, resLE_comp_basicOpenToSpec]
  simp only [Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact localizationHom_fromZeroRingHom 𝒜 D _

end S2RescaledProj
end HodgeLean.Foundations.Program
