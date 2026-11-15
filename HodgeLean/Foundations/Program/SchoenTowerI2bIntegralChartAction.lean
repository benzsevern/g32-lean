import HodgeLean.Foundations.Program.SchoenTowerI2bIntegralField
import HodgeLean.Foundations.Program.SchoenTowerI2bChartScalars
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! Identifying the actual chart action with the integral field action.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant original-field chart identifies the retained action with the integral-closure action.
Source: injectivity on the generic field, Kummer commutation, and separatedness of an affine scheme. -/
theorem s2v_i2b_integral_chart_action
    {F R K : Type} [Field F] [CommRing R] [Field K]
    [Algebra F R] [Algebra R K] [Algebra F K] [IsScalarTower F R K]
    (m : ℕ) (hm : 0 < m) (ζ₀ : F) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (v : K) (hv0 : v ≠ 0) (hvint : IsIntegral R v)
    (r : R) (hv : v ^ m = algebraMap R K r)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (δ : K ≃ₐ[R] K) (a : R) (hδ : δ v = algebraMap R K a * v)
    {X : Scheme} [IsReduced X] (eN : X ≅ Spec ↧(integralClosure R K))
    (dn : X ⟶ X) (q : Spec ↧K ⟶ X) [IsDominant q]
    (hq : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ q = q ≫ dn)
    (hbase : ∀ a : R, (Spec.preimage (q ≫ eN.hom)).hom
      (algebraMap R (integralClosure R K) a) = algebraMap R K a) :
    dn ≫ eN.hom = eN.hom ≫ Spec.map
      (CommRingCat.ofHom δ.mapIntegralClosure.toRingHom) := by
  let p := q ≫ eN.hom
  let f : integralClosure R K →ₐ[R] K :=
    { (Spec.preimage p).hom with commutes' := hbase }
  have hf : Function.Injective f := s2v_i2b_spec_preimage_injective p
  have hcomm := s2v_i2b_integral_embedding_commutes m hm ζ₀ hζ₀ v hv0 hvint r hv hgen
    δ a hδ f hf
  have hsquare : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom δ.mapIntegralClosure.toRingHom) := by
    apply Spec.preimage_injective
    simp only [Spec.preimage_comp, Spec.preimage_map]
    ext b
    change δ (f b) = f (δ.mapIntegralClosure b)
    exact (hcomm b).symm
  apply ext_of_isDominant q
  calc
    q ≫ dn ≫ eN.hom = (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ q) ≫ eN.hom := by
      rw [← Category.assoc, hq]
    _ = Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ p := Category.assoc _ _ _
    _ = p ≫ Spec.map (CommRingCat.ofHom δ.mapIntegralClosure.toRingHom) := hsquare
    _ = q ≫ eN.hom ≫ Spec.map (CommRingCat.ofHom δ.mapIntegralClosure.toRingHom) :=
      Category.assoc _ _ _

end HodgeLean.Foundations.Program
