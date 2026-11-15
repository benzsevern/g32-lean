import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVSequence

/-! # Actual relative quotients under small-chain equivalences -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A small-chain inclusion inducing homology isomorphisms also induces homology isomorphisms on the actual relative quotients.
Source: Hatcher, Algebraic Topology, section 2.2, the relative small-chain theorem.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_quotient_quasiIso
    {K : SSet.{0}} {P Q : K.Subcomplex} (h : P ≤ Q)
    (hq : QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) (ModuleCat.of ℚ ℚ))) :
    QuasiIso (properCycle_subcomplex_quotient_map h) := by
  let C := (SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let φ : ShortComplex.cokernelSequence (C.map P.ι) ⟶
      ShortComplex.cokernelSequence (C.map Q.ι) :=
    ShortComplex.homMk (C.map (SSet.Subcomplex.homOfLE h)) (𝟙 _)
      (properCycle_subcomplex_quotient_map h)
      (by
        change C.map (SSet.Subcomplex.homOfLE h) ≫ C.map Q.ι = C.map P.ι ≫ 𝟙 _
        rw [Category.comp_id, ← C.map_comp]
        rfl)
      (by simpa using (properCycle_subcomplex_quotient_projection h).symm)
  have hP : (ShortComplex.cokernelSequence (C.map P.ι)).ShortExact := by
    refine { exact := ShortComplex.cokernelSequence_exact _, mono_f := ?_, epi_g := by infer_instance }
    dsimp [C, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  have hQ : (ShortComplex.cokernelSequence (C.map Q.ι)).ShortExact := by
    refine { exact := ShortComplex.cokernelSequence_exact _, mono_f := ?_, epi_g := by infer_instance }
    dsimp [C, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hP hQ hq
    (inferInstanceAs (QuasiIso (𝟙 (C.obj K))))

end HodgeLean.Foundations.QuotientDuality
