import HodgeLean.Foundations.Singular.Cup

/-! # Detection of actual singular cocycles in degree zero

There is no incoming boundary in degree zero, so the original closed cochain
is retained by passage to singular cohomology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Simplicial AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

variable {R : Type} [CommRing R] (Y : TopCat.{0})

theorem i1_degreeZero_cohomologyClass_injective :
    Function.Injective (cohomologyClass (R := R) Y 0) := by
  intro φ ψ h
  let S := ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).sc 0
  let E := S.linearDual.moduleCatHomologyIso.toLinearEquiv.symm.trans
    (cochainCohomologyEquiv R Y 0)
  have hq := E.injective h
  have hb : S.linearDual.moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro η
    apply Subtype.ext
    change (S.g.hom.dualMap) η = 0
    have hg : S.g = 0 := by
      change (SingularChainComplex R Y).d 0 ((ComplexShape.down ℕ).next 0) = 0
      apply HomologicalComplex.shape
      rw [ChainComplex.next_nat_zero]
      simp
    rw [hg]
    ext c
    let ηF : Module.Dual R S.X₃ := η
    change ηF 0 = 0
    exact map_zero ηF
  change Submodule.Quotient.mk
      (⟨φ.1, _⟩ : LinearMap.ker S.linearDual.g.hom) =
    Submodule.Quotient.mk (⟨ψ.1, _⟩ : LinearMap.ker S.linearDual.g.hom) at hq
  rw [Submodule.Quotient.eq, hb, LinearMap.range_zero] at hq
  have hc := sub_eq_zero.mp hq
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.ker S.linearDual.g.hom => z.1) hc

end HodgeLean.Foundations.BundleResolution
