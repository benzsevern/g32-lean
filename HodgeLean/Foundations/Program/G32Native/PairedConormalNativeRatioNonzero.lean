import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeRatio

/-! # Regularity of the actual coordinate ratios -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The native affine coordinate ring is a domain over a domain. -/
theorem paired_nativeAway_isDomain (R : Type) [CommRing R] [IsDomain R]
    (k : ℕ) (i : Fin (k + 1)) :
    IsDomain (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) (MvPolynomial.X i)) := by
  letI : Algebra R (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) (MvPolynomial.X i)) :=
    Proj.instAlgebraAway R (MvPolynomial.X i)
  exact (Proj.dehom R i (MvPolynomial.X i) rfl).toRingEquiv.isDomain_iff.mp inferInstance

/-- Every actual native coordinate ratio is nonzero over a domain. -/
theorem paired_nativeRatio_ne_zero (R : Type) [CommRing R] [IsDomain R]
    (k : ℕ) (i j : Fin (k + 1)) : ProjSpace.ratio R k i j ≠ 0 := by
  classical
  letI := paired_nativeAway_isDomain R k i
  by_cases h : j = i
  · subst j
    rw [ProjSpace.ratio_self]
    exact one_ne_zero
  · letI : Algebra R (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) (MvPolynomial.X i)) :=
      Proj.instAlgebraAway R (MvPolynomial.X i)
    let e := (Proj.dehom R i (MvPolynomial.X i) rfl).toRingEquiv
    have he : e (MvPolynomial.X ⟨j, h⟩) = ProjSpace.ratio R k i j := by
      change (Proj.dehomAux R i (MvPolynomial.X i) rfl) (MvPolynomial.X ⟨j, h⟩) = _
      rw [Proj.dehomAux, MvPolynomial.aeval_X]
      rfl
    rw [← he, EmbeddingLike.map_ne_zero_iff]
    exact MvPolynomial.X_ne_zero _

end HodgeLean.Foundations.Program.G32Native
