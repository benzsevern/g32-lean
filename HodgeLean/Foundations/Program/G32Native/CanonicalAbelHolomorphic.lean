import HodgeLean.Foundations.Program.G32Native.CanonicalAbelAlgebraicDescent
/-! # Holomorphic descent through the retained algebraic quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Algebraization on the ordered power permits holomorphic descent without selecting roots. -/
theorem canonicalSymmetricAbel_contMDiff (G : CanonicalAbelGeometry)
    (p : ComplexPoint G.Z) :
    let h := Module.finrank_fin_fun (n := 1) ℂ
    letI := b3_periodLattice_finite (C := ComplexPoint G.Z) h
    letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint G.Z)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint G.Z) h)
    ContMDiff 𝓘(ℂ, Fin (G.k + G.k) → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint G.Z)) ω (canonicalSymmetricAbel G p) := by
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := ComplexPoint G.Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint G.Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint G.Z) h)
  let J := model (C := ComplexPoint G.Z) h
  let s := canonicalSymmetricAbel G p
  obtain ⟨vB, hvB⟩ := canonical_symmetric_abel_algebraic G p
  have he (b : ComplexPoint G.B) : s b = (theta h).symm (Point.map vB b) :=
    ((theta h).symm_apply_apply (s b)).symm.trans
      (congrArg (theta h).symm (congrFun hvB b).symm)
  exact ((theta_symm_contMDiff (C := ComplexPoint G.Z) h).comp
    (spec_contMDiff_pointMap G.B J (G.k + G.k) _ vB)).congr he

#print axioms canonicalSymmetricAbel_contMDiff
end HodgeLean.Foundations.Program.G32Native
