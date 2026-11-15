import HodgeLean.Foundations.Program.SchoenCycleLocalTestPoints
import HodgeLean.Foundations.Program.SchoenCycleStalkMapInjectivity
import HodgeLean.Foundations.Program.SchoenCycleStalkMapNaturality
import HodgeLean.Foundations.Program.SchoenCycleStalkScalars
import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints

/-! # Nilpotent coordinate maps from actual curve-power stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every tuple of nilpotent parameter values defines a scalar-compatible
local map from the actual curve-power stalk at the specified complex tuple.
Source: Hartshorne, Algebraic Geometry, II.2, local spectra and products;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_power_nilpotent_stalk_map_exists
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [IsIntegral (g3_power X n).left] (x : ComplexPoint (g3_power X n))
    (t : ∀ i, X.left.presheaf.stalk ((g3_proj X n i).left x.underlying))
    (ht : ∀ i, IsLocalRing.maximalIdeal
      (X.left.presheaf.stalk ((g3_proj X n i).left x.underlying)) = Ideal.span {t i})
    (hreg : ∀ i, Function.Injective (fun z => t i * z))
    (A : Type) [CommRing A] [Algebra ℂ A] [IsLocalRing A]
    (ε : A →ₐ[ℂ] ℂ) (a : Fin n → A) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ l : (g3_power X n).left.presheaf.stalk x.underlying →+* A,
      IsLocalHom l ∧
      (∀ c, l (HodgeLean.Foundations.Curves.stalkC x.underlying c) = algebraMap ℂ A c) ∧
      ∀ i, l ((g3_proj X n i).left.stalkMap x.underlying (t i)) = a i := by
  classical
  let P := g3_power X n
  let p (i : Fin n) := Point.map (g3_proj X n i) x
  let R (i : Fin n) := X.left.presheaf.stalk (p i).underlying
  letI (i : Fin n) : Algebra ℂ (R i) :=
    (HodgeLean.Foundations.Curves.stalkC (p i).underlying).toAlgebra
  let φ (i : Fin n) : R i →ₐ[ℂ] ℂ :=
    { toRingHom := (p i).stalkHom.hom
      commutes' := s2e_complex_point_stalk_constants X (p i) }
  have hmaps (i : Fin n) : ∃ f : R i →ₐ[ℂ] A, f (t i) = a i := by
    obtain ⟨N, hN⟩ := ha i
    exact (s2e_parameter_nilpotent_map_exists_unique (R i) A (φ i) (t i) (ht i)
      (hreg i) N (a i) hN).exists
  choose f hf using hmaps
  have hnil (i : Fin n) : IsNilpotent (f i (t i)) := (hf i).symm ▸ ha i
  letI (i : Fin n) : IsLocalHom (f i).toRingHom :=
    s2e_nilpotent_parameter_map_isLocalHom (R i) A (t i) (ht i) (f i).toRingHom (hnil i)
  let u := s2_lift n (fun i => s2e_stalkMap_to_base_morphism X (p i).underlying A
    (f i).toRingHom (fun c => (f i).commutes c))
  have hred : s2e_scalarResidue_morphism A ε ≫ u = x := by
    have h := s2e_curve_power_nilpotent_parameter_reduction X n p t ht A f hnil ε
    exact h.trans (s2e_lift_coordinates n x)
  have hp := s2e_base_morphism_point_of_scalar_reduction P A ε u x hred
  obtain ⟨l, hl, hC, hlu⟩ := s2e_base_morphism_stalk_map_at_point P A u x.underlying hp
  letI : IsLocalHom l := hl
  refine ⟨l, hl, hC, ?_⟩
  intro i
  let q := g3_proj X n i
  have hc (c : ℂ) : (l.comp (q.left.stalkMap x.underlying).hom)
      (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying) c) = algebraMap ℂ A c := by
    change l ((q.left.stalkMap x.underlying).hom _) = _
    rw [s2e_stalkMap_complex_scalars P X q x.underlying c]
    exact hC c
  have hu : u ≫ q = s2e_stalkMap_to_base_morphism X (p i).underlying A
      (f i).toRingHom (fun c => (f i).commutes c) := s2_check_lift_proj n _ i
  have he : s2e_stalkMap_to_base_morphism X (q.left x.underlying) A
      (l.comp (q.left.stalkMap x.underlying).hom) hc =
        s2e_stalkMap_to_base_morphism X (p i).underlying A
          (f i).toRingHom (fun c => (f i).commutes c) :=
    (s2e_stalkMap_to_base_morphism_comp P X q x.underlying A l hC hc).symm.trans
      ((congrArg (fun v => v ≫ q) hlu).trans hu)
  have hr := s2e_stalkMap_to_base_morphism_injective X (q.left x.underlying) A
    (l.comp (q.left.stalkMap x.underlying).hom) (f i).toRingHom hc
    (fun c => (f i).commutes c) he
  exact (congrArg (fun k : R i →+* A => k (t i)) hr).trans (hf i)

end HodgeLean.Foundations.Program
