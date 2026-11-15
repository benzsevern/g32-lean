import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

/-! Explicit real coordinates on finite complex coordinate families.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.WitnessSelection.StageTwo

/-- Record every real and imaginary coordinate in a finite real Euclidean space.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
def s2e_pair_complexRealCoordinates {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    EuclideanSpace ℝ (Fin (Fintype.card (ι ⊕ ι))) :=
  WithLp.toLp 2 (fun k =>
    Sum.elim (fun i => (v i).re) (fun i => (v i).im) ((Fintype.equivFin (ι ⊕ ι)).symm k))

/-- The explicit real coordinate map is injective.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_complexRealCoordinates_injective {ι : Type*} [Fintype ι] :
    Function.Injective (s2e_pair_complexRealCoordinates (ι := ι)) := by
  intro v w he
  funext i
  apply Complex.ext
  · have h := congrArg (fun z => z (Fintype.equivFin (ι ⊕ ι) (Sum.inl i))) he
    change Sum.elim (fun j => (v j).re) (fun j => (v j).im)
        ((Fintype.equivFin (ι ⊕ ι)).symm (Fintype.equivFin (ι ⊕ ι) (Sum.inl i))) =
      Sum.elim (fun j => (w j).re) (fun j => (w j).im)
        ((Fintype.equivFin (ι ⊕ ι)).symm (Fintype.equivFin (ι ⊕ ι) (Sum.inl i))) at h
    simpa only [Equiv.symm_apply_apply, Sum.elim_inl] using h
  · have h := congrArg (fun z => z (Fintype.equivFin (ι ⊕ ι) (Sum.inr i))) he
    change Sum.elim (fun j => (v j).re) (fun j => (v j).im)
        ((Fintype.equivFin (ι ⊕ ι)).symm (Fintype.equivFin (ι ⊕ ι) (Sum.inr i))) =
      Sum.elim (fun j => (w j).re) (fun j => (w j).im)
        ((Fintype.equivFin (ι ⊕ ι)).symm (Fintype.equivFin (ι ⊕ ι) (Sum.inr i))) at h
    simpa only [Equiv.symm_apply_apply, Sum.elim_inr] using h

/-- The explicit real coordinate map is continuous.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_complexRealCoordinates_continuous {ι : Type*} [Fintype ι] :
    Continuous (s2e_pair_complexRealCoordinates (ι := ι)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  cases (Fintype.equivFin (ι ⊕ ι)).symm k with
  | inl i => exact Complex.continuous_re.comp (continuous_apply i)
  | inr i => exact Complex.continuous_im.comp (continuous_apply i)

end HodgeLean.WitnessSelection.StageTwo
