import HodgeLean.Foundations.TubularEuler.ConormalRegularRepresentativeHelpers
import HodgeLean.Foundations.TubularEuler.RetainedConormalRankHelpers
import HodgeLean.Foundations.TubularEuler.NormalGeneratorLocalization

/-! # Independent regular conormal covectors at the specified point

Every selected equation is an element of the original affine immersion
ideal. Its analytic differential is the image of an actual conormal basis vector.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleThom

theorem exists_independent_regular_conormal_covectors
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (k : ℕ) [SmoothOfRelativeDimension k Y.hom] [SmoothOfRelativeDimension (k + k) X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin (k + k) → ℂ) z).source) :
    ∃ u : Fin k → RingHom.ker (j.left.app V).hom,
      LinearIndependent ℂ (fun i =>
        fderiv ℂ (fun a : Fin (k + k) → ℂ =>
          Point.evaluate V (u i).val ((chartAt (Fin (k + k) → ℂ) z).symm a))
          ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x))) := by
  classical
  let ρ := (j.left.app V ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
  letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
  obtain ⟨e⟩ := i1_conormalFibre_coordinates_nonempty j.left k X.hom (Over.w j) x
  let b := (Pi.basisFun ℂ (Fin k)).map e.symm
  choose u hu using fun i : Fin k => retainedConormal_regular_representative X Y j V hV x hx (b i)
  let D := retainedAffineConormalDifferential X Y j (k + k) V hV x hx z hz
  have hi := (retainedAffineConormalDifferential_rank X Y j k V hV x hx z hz).1
  have heq : (fun i => D (b i)) = (fun i =>
      fderiv ℂ (fun a : Fin (k + k) → ℂ =>
        Point.evaluate V (u i).val ((chartAt (Fin (k + k) → ℂ) z).symm a))
        ((chartAt (Fin (k + k) → ℂ) z) (Point.map j x))) := by
    funext i
    simpa only [one_smul] using
      retained_conormal_generator_localization X Y j (k + k) V hV x hx z hz (u i) 1 (b i) (hu i)
  refine ⟨u, ?_⟩
  rw [← heq]
  exact b.linearIndependent.map' D (LinearMap.ker_eq_bot.mpr hi)

#print axioms exists_independent_regular_conormal_covectors

end HodgeLean.Foundations.TubularEuler
