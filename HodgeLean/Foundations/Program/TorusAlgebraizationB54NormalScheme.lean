import HodgeLean.Foundations.Program.TorusAlgebraizationB54NormalCharts
import HodgeLean.Foundations.Mathlib.ZmtIso
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem b54_normal_of_affineCover {X : Scheme} (U : X.AffineOpenCover)
    (hdom : ∀ i, IsDomain (U.X i)) (hnormal : ∀ i, IsIntegrallyClosed (U.X i)) :
    zmtiso_IsNormal X := by
  intro x
  obtain ⟨i, y, rfl⟩ : ∃ i y, U.f i y = x := ⟨U.idx x, U.covers x⟩
  letI := hdom i
  letI := hnormal i
  have hs : y.asIdeal.primeCompl ≤ nonZeroDivisors (U.X i) := by
    intro a ha
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hz
    exact ha (hz ▸ y.asIdeal.zero_mem)
  letI : IsIntegrallyClosed (Localization.AtPrime y.asIdeal) :=
    isIntegrallyClosed_of_isLocalization _ y.asIdeal.primeCompl hs
  let e : X.presheaf.stalk (U.f i y) ≃+* Localization.AtPrime y.asIdeal :=
    ((asIso ((U.f i).stalkMap y)).commRingCatIsoToRingEquiv).trans
      (StructureSheaf.stalkIso (U.X i) y).toRingEquiv.symm
  exact ⟨e.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e.symm⟩

theorem b54_proj_normal_of_degree_one {A σ ι : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hne : ∀ i, v i ≠ 0)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range v)) :
    zmtiso_IsNormal (Proj G) := by
  let U := Proj.affineOpenCoverOfIrrelevantLESpan G v hv (fun _ => zero_lt_one) hcover
  apply b54_normal_of_affineCover U
  · intro i
    exact b54_away_isDomain G (hne i)
  · intro i
    exact b54_away_integrallyClosed G (hv i) (hne i)

end HodgeLean.Foundations.Program
