import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateChartConormal
import HodgeLean.Foundations.Program.G32Native.PairedC3CotangentRingEquiv
import HodgeLean.Foundations.Program.G32Native.PairedC3SemilinearBasis

/-! # Original normal-ratio basis for a labelled projective coordinate inclusion -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry MvPolynomial HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual chart kernel is the discarded-variable ideal in its specified polynomial coordinates. -/
theorem paired_c3_original_chart_kernel_map {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    (RingHom.ker (pairedC3CoordinateChartMap e i)).map
      (pairedC3PolynomialChartAlgEquiv n (e i)).toRingHom =
      Ideal.span (X (R := ℂ) '' (Set.range (pairedC3ChartCoordinateEmbedding e i))ᶜ) := by
  let EA := pairedC3PolynomialChartAlgEquiv n (e i)
  let EB := pairedC3PolynomialChartAlgEquiv k i
  rw [← paired_c3_coordinate_elimination_kernel]
  ext z
  have hmem := Ideal.symm_apply_mem_of_equiv_iff
    (I := RingHom.ker (pairedC3CoordinateChartMap e i)) (f := EA.toRingEquiv) (y := z)
  change z ∈ Ideal.map EA.toRingEquiv (RingHom.ker (pairedC3CoordinateChartMap e i)) ↔ _
  rw [← hmem, RingHom.mem_ker, RingHom.mem_ker]
  have hz := congrArg (fun f => f z) (paired_c3_coordinate_chart_polynomial_map e i)
  change EB (pairedC3CoordinateChartMap e i (EA.symm z)) =
    MvPolynomial.killCompl (R := ℂ) (pairedC3ChartCoordinateEmbedding e i).injective z at hz
  change pairedC3CoordinateChartMap e i (EA.symm z) = 0 ↔
    MvPolynomial.killCompl (R := ℂ) (pairedC3ChartCoordinateEmbedding e i).injective z = 0
  rw [← hz]
  exact EB.map_eq_zero_iff.symm

/-- A discarded-variable basis under an equality of the actual polynomial ideals. -/
def pairedC3EliminationIdealBasis {A ι κ : Type} [CommRing A] (e : κ ↪ ι)
    (I : Ideal (MvPolynomial ι A))
    (hI : I = Ideal.span (X (R := A) '' (Set.range e)ᶜ)) :
    Module.Basis {j : ι // j ∉ Set.range e} (MvPolynomial ι A ⧸ I) I.Cotangent := by
  subst I
  exact pairedC3CoordinateEliminationConormalBasis e

/-- The transported polynomial basis still uses its original coordinate classes. -/
theorem paired_c3_elimination_ideal_basis_apply {A ι κ : Type} [CommRing A] (e : κ ↪ ι)
    (I : Ideal (MvPolynomial ι A))
    (hI : I = Ideal.span (X (R := A) '' (Set.range e)ᶜ))
    (j : {j : ι // j ∉ Set.range e}) :
    pairedC3EliminationIdealBasis e I hI j =
      I.toCotangent ⟨X j.val, hI.symm ▸ Ideal.subset_span ⟨j.val, j.property, rfl⟩⟩ := by
  subst I
  exact paired_c3_coordinate_elimination_conormal_basis_apply e j

/-- The original chart kernel cotangent has one basis vector per original
homogeneous discarded label. -/
def pairedC3OriginalChartKernelBasis {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    let P := Away (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i))
    let I := RingHom.ker (pairedC3CoordinateChartMap e i)
    Module.Basis {j : Fin (n + 1) // j ∉ Set.range e} (P ⧸ I) I.Cotangent := by
  let I := RingHom.ker (pairedC3CoordinateChartMap e i)
  let EA := (pairedC3PolynomialChartAlgEquiv n (e i)).toRingEquiv
  let q := Ideal.quotientEquiv I (I.map EA.toRingHom) EA rfl
  letI := RingHomInvPair.of_ringEquiv q
  letI := RingHomInvPair.of_ringEquiv_symm q
  exact (pairedC3SemilinearBasis q (pairedC3CotangentRingEquiv I EA)
    (pairedC3EliminationIdealBasis (pairedC3ChartCoordinateEmbedding e i)
      (I.map EA.toRingHom) (paired_c3_original_chart_kernel_map e i))).reindex
        (pairedC3ChartNormalIndexEquiv e i)

/-- Every basis vector is its actual homogeneous normal-ratio class. -/
theorem paired_c3_original_chart_kernel_basis_apply {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : {j : Fin (n + 1) // j ∉ Set.range e}) :
    let I := RingHom.ker (pairedC3CoordinateChartMap e i)
    pairedC3OriginalChartKernelBasis e i j =
      I.toCotangent ⟨ProjSpace.ratio ℂ n (e i) j.val,
        paired_c3_coordinate_chart_map_discarded_ratio e i j.val j.property⟩ := by
  let I := RingHom.ker (pairedC3CoordinateChartMap e i)
  let EA := (pairedC3PolynomialChartAlgEquiv n (e i)).toRingEquiv
  let q := Ideal.quotientEquiv I (I.map EA.toRingHom) EA rfl
  letI := RingHomInvPair.of_ringEquiv q
  letI := RingHomInvPair.of_ringEquiv_symm q
  let c := pairedC3CotangentRingEquiv I EA
  let b := pairedC3EliminationIdealBasis (pairedC3ChartCoordinateEmbedding e i)
    (I.map EA.toRingHom) (paired_c3_original_chart_kernel_map e i)
  change ((pairedC3SemilinearBasis q c b).reindex (pairedC3ChartNormalIndexEquiv e i)) j = _
  rw [Module.Basis.reindex_apply, paired_c3_semilinear_basis_apply]
  apply c.injective
  rw [c.apply_symm_apply, paired_c3_elimination_ideal_basis_apply,
    paired_c3_cotangent_ring_equiv_toCotangent]
  apply congrArg (I.map EA.toRingHom).toCotangent
  apply Subtype.ext
  change X _ = pairedC3PolynomialChartCoordinates n (e i) (ProjSpace.ratio ℂ n (e i) j.val)
  rw [paired_c3_polynomial_chart_coordinates_ratio]
  have hj : j.val ≠ e i := fun h => j.property ⟨i, h.symm⟩
  rw [dif_neg hj]
  congr 1

#print axioms paired_c3_original_chart_kernel_basis_apply
end HodgeLean.Foundations.Program.G32Native
