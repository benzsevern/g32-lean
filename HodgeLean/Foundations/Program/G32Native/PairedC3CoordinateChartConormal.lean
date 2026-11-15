import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateChartPolynomials
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateEliminationConormal
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalFreeTransport

/-! # Actual affine conormal frames of the projective chart comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Normal indices on a retained affine chart are exactly the original
discarded homogeneous indices. No denominator coordinate is discarded. -/
def pairedC3ChartNormalIndexEquiv {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    {j : {j : Fin (n + 1) // j ≠ e i} //
      j ∉ Set.range (pairedC3ChartCoordinateEmbedding e i)} ≃
      {j : Fin (n + 1) // j ∉ Set.range e} where
  toFun j := ⟨j.val.val, fun h => j.property ((paired_c3_chart_coordinate_mem_range e i j.val).mpr h)⟩
  invFun j :=
    let q : {j : Fin (n + 1) // j ≠ e i} := ⟨j.val, fun h => j.property ⟨i, h.symm⟩⟩
    ⟨q, fun h => j.property ((paired_c3_chart_coordinate_mem_range e i q).mp h)⟩
  left_inv j := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv j := by apply Subtype.ext; rfl

/-- The normalized chart comparison retains its actual conormal, framed
by the same discarded labels as its polynomial coordinate-elimination map. -/
def pairedC3CoordinateChartConormalFrame {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    let B := CommRingCat.of (Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i))
    s2c_conormal (Spec.map (CommRingCat.ofHom (pairedC3CoordinateChartMap e i))) ≅
      (SheafOfModules.free (R := (Spec B).ringCatSheaf)
        {j : Fin (n + 1) // j ∉ Set.range e} : (Spec B).Modules) := by
  let EA := pairedC3PolynomialChartAlgEquiv n (e i)
  let EB := pairedC3PolynomialChartAlgEquiv k i
  let π := MvPolynomial.killCompl (R := ℂ) (pairedC3ChartCoordinateEmbedding e i).injective
  let a := asIso (Spec.map EA.toRingEquiv.toCommRingCatIso.hom)
  let b := asIso (Spec.map EB.toRingEquiv.toCommRingCatIso.hom)
  let f := Spec.map (CommRingCat.ofHom (pairedC3CoordinateChartMap e i))
  let g := Spec.map (CommRingCat.ofHom π.toRingHom)
  have hw : b.hom ≫ f = g ≫ a.hom := by
    change Spec.map EB.toRingEquiv.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (pairedC3CoordinateChartMap e i)) =
      Spec.map (CommRingCat.ofHom π.toRingHom) ≫ Spec.map EA.toRingEquiv.toCommRingCatIso.hom
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    have hz := congrArg (fun h => h (EA z)) (paired_c3_coordinate_chart_polynomial_map e i)
    change EB (pairedC3CoordinateChartMap e i (EA.symm (EA z))) = π (EA z) at hz
    rw [AlgEquiv.symm_apply_apply] at hz
    exact hz
  let E := s2e_conormalArrowIso b.hom a.hom f g hw ≪≫
    pairedC3CoordinateEliminationConormalFrame (A := ℂ) (pairedC3ChartCoordinateEmbedding e i)
  exact s2e_freeOfPullbackIso b _ _ E ≪≫
    SheafOfModules.freeFunctor.mapIso (pairedC3ChartNormalIndexEquiv e i).toIso

end HodgeLean.Foundations.Program.G32Native
