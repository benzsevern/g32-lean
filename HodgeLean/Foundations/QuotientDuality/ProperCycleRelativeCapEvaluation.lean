import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCapUnit

/-! # Original relative Kronecker evaluation through the degree-zero cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluating the actual degree-zero relative cap against the original cup unit equals the original relative universal-coefficient pairing.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3, relative Kronecker pairing and cap evaluation.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_cap_unit_evaluation
    (P : TopPair.{0}) (p : ℕ) (a : RelativeCohomology ℚ P p)
    (c : RelativeHomology ℚ P p) :
    cohomologyEquivDualHomology ℚ P.fst 0 (unit (R := ℚ) P.fst)
      (relativeCapCohomologyLinear ℚ P p 0 a c) =
      relativeCohomologyEquivDualHomology ℚ P p a c := by
  let S := ((relativeChainFunctor ℚ).obj P).sc p
  let T := (SingularChainComplex ℚ P.fst).sc 0
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ P p).surjective a
  obtain ⟨φ, rfl⟩ := S.linearDual.moduleCatHomologyClass_surjective u
  let ψ := relativeCohomologyCycleToCocycle ℚ P p φ
  let F := relativeCapShortComplexHom ℚ P p 0 ψ.1 ψ.2
  let β : LinearMap.ker T.linearDual.g.hom := ⟨unitCochain (R := ℚ) P.fst, by
    change (((SingularChainComplex ℚ P.fst).sc 0).f.hom.dualMap)
      (unitCochain (R := ℚ) P.fst) = 0
    change (((SingularChainComplex ℚ P.fst).d ((ComplexShape.down ℕ).prev 0) 0).hom.dualMap)
      (unitCochain (R := ℚ) P.fst) = 0
    rw [ChainComplex.prev]
    exact coboundary_unitCochain P.fst⟩
  have hu : unit (R := ℚ) P.fst = cochainCohomologyEquiv ℚ P.fst 0
      (T.linearDual.moduleCatHomologyClass β) := rfl
  have hβ : ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap F) β = φ := by
    apply Subtype.ext
    change (unitCochain (R := ℚ) P.fst).comp (relativeCap ℚ P p 0 ψ.1) = φ.1
    exact properCycle_relative_cap_unit_cochain P p φ.1
  have hm : (ShortComplex.homologyMap (ShortComplex.linearDualMap F)).hom
      (T.linearDual.moduleCatHomologyClass β) = S.linearDual.moduleCatHomologyClass φ := by
    rw [ShortComplex.moduleCatHomologyClass_naturality, hβ]
    rfl
  have hcap : relativeCapCohomologyLinear ℚ P p 0
      (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ)) =
      relativeCohomologyCycleCapLinear ℚ P p 0 φ := relativeCapCohomologyLinear_on_cycle ℚ P p 0 φ
  rw [hcap, hu]
  change T.linearDualHomologyEquiv
      ((cochainCohomologyEquiv ℚ P.fst 0).symm
        (cochainCohomologyEquiv ℚ P.fst 0 (T.linearDual.moduleCatHomologyClass β)))
      ((ShortComplex.homologyMap F).hom c) =
    S.linearDualHomologyEquiv
      ((relativeCochainCohomologyEquiv ℚ P p).symm
        (relativeCochainCohomologyEquiv ℚ P p (S.linearDual.moduleCatHomologyClass φ))) c
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hn := LinearMap.congr_fun (ShortComplex.linearDualHomologyEquiv_naturality F
    (T.linearDual.moduleCatHomologyClass β)) c
  rw [hm] at hn
  exact hn.symm

end HodgeLean.Foundations.QuotientDuality
