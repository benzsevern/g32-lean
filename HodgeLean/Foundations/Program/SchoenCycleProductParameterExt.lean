import HodgeLean.Foundations.Program.SchoenCycleStalkMapInjectivity
import HodgeLean.Foundations.Program.SchoenCycleStalkMapNaturality
import HodgeLean.Foundations.Program.SchoenCycleStalkScalars
import HodgeLean.Foundations.Program.SchoenCycleProductStalkPoints

/-! # Uniqueness of nilpotent coordinates in actual curve powers -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Local maps from an actual curve-power stalk with nilpotent coordinate
values are determined by the pulled-back regular curve parameters.
Source: Hartshorne, Algebraic Geometry, II.2, local spectra and products;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_power_nilpotent_parameter_ext
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [IsIntegral (g3_power X n).left] (x : ComplexPoint (g3_power X n))
    (t : ∀ i, X.left.presheaf.stalk ((g3_proj X n i).left x.underlying))
    (ht : ∀ i, IsLocalRing.maximalIdeal
      (X.left.presheaf.stalk ((g3_proj X n i).left x.underlying)) = Ideal.span {t i})
    (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (f g : (g3_power X n).left.presheaf.stalk x.underlying →+* A)
    [IsLocalHom f] [IsLocalHom g]
    (hf : ∀ c, f (HodgeLean.Foundations.Curves.stalkC x.underlying c) = algebraMap ℂ A c)
    (hg : ∀ c, g (HodgeLean.Foundations.Curves.stalkC x.underlying c) = algebraMap ℂ A c)
    (hnil : ∀ i, IsNilpotent (f ((g3_proj X n i).left.stalkMap x.underlying (t i))))
    (heq : ∀ i, f ((g3_proj X n i).left.stalkMap x.underlying (t i)) =
      g ((g3_proj X n i).left.stalkMap x.underlying (t i))) : f = g := by
  let P := g3_power X n
  have hu : s2e_stalkMap_to_base_morphism P x.underlying A f hf =
      s2e_stalkMap_to_base_morphism P x.underlying A g hg := by
    apply (spec_g3_isLimit_fan X n).some.hom_ext
    rintro ⟨i⟩
    change s2e_stalkMap_to_base_morphism P x.underlying A f hf ≫ g3_proj X n i =
      s2e_stalkMap_to_base_morphism P x.underlying A g hg ≫ g3_proj X n i
    let q := g3_proj X n i
    let p := Point.map q x
    let R := X.left.presheaf.stalk p.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
    let f' : R →ₐ[ℂ] A :=
      { toRingHom := f.comp (q.left.stalkMap x.underlying).hom
        commutes' := fun c => by
          change f ((q.left.stalkMap x.underlying).hom
            (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying) c)) = algebraMap ℂ A c
          rw [s2e_stalkMap_complex_scalars P X q x.underlying c]
          exact hf c }
    let g' : R →ₐ[ℂ] A :=
      { toRingHom := g.comp (q.left.stalkMap x.underlying).hom
        commutes' := fun c => by
          change g ((q.left.stalkMap x.underlying).hom
            (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying) c)) = algebraMap ℂ A c
          rw [s2e_stalkMap_complex_scalars P X q x.underlying c]
          exact hg c }
    let φ : R →ₐ[ℂ] ℂ :=
      { toRingHom := p.stalkHom.hom
        commutes' := s2e_complex_point_stalk_constants X p }
    have hfg : f' = g' := by
      obtain ⟨N, hN⟩ := hnil i
      exact s2e_parameter_nilpotent_map_ext R A φ (t i) (ht i) N f' g' hN (heq i)
    rw [s2e_stalkMap_to_base_morphism_comp P X q x.underlying A f hf
      (fun c => f'.commutes c),
      s2e_stalkMap_to_base_morphism_comp P X q x.underlying A g hg
      (fun c => g'.commutes c)]
    have he : f.comp (q.left.stalkMap x.underlying).hom =
        g.comp (q.left.stalkMap x.underlying).hom := congrArg AlgHom.toRingHom hfg
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (f.comp (q.left.stalkMap x.underlying).hom)) ≫
        X.left.fromSpecStalk (q.left x.underlying) =
      Spec.map (CommRingCat.ofHom (g.comp (q.left.stalkMap x.underlying).hom)) ≫
        X.left.fromSpecStalk (q.left x.underlying)
    rw [he]
  exact s2e_stalkMap_to_base_morphism_injective P x.underlying A f g hf hg hu

end HodgeLean.Foundations.Program
