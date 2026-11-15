import HodgeLean.Foundations.Program.SchoenCycleS3Initial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Differential coordinates and the actual projective adaptation of one initial slice.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.5, pp. 13–15. -/
structure G32InitialResidueData
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] (k r : ℕ)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (γ : g3_power Z (2 * k) ⟶ B)
    (ℓadapt : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B) where
  [curve : SmoothOfRelativeDimension 1 Z.hom]
  [finite : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
  w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
    (Module.finrank_fin_fun (n := 1) ℂ)
  hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
    (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0
  hpair : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
    (w i) (y ⟨2 * j.val, by omega⟩) = if i = j then -1 else 0
  horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
    (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0
  hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
    (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0
  hg : 2 * k + 2 = 2 * Module.finrank ℂ
    (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r
  hd : Module.finrank ℂ
    (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1
  e : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ≅
    Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  raw : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B
  coefficients : (Fin (k + 1) → ℂ) ≃ₗ[ℂ]
    (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ))
  coordinate_change : e = s2e_linearProjectiveOverIso
    (coefficients.trans (Module.finBasisOfFinrankEq ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) hd).equivFun)
  indices : Fin r ↪ Fin (k + 1)
  coefficient_residues : ∀ v j, (coefficients v).2 j = v (indices j)
  adapted : ℓadapt = e.hom ≫ raw
  point_formula :
    letI : ConnectedSpace (ComplexPoint Z) :=
      AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
    Point.map raw = fun R => s2e_projectiveDifferentialQuotientPoint
      (Module.finrank_fin_fun (n := 1) ℂ) w
      (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hg γ id
      (ep.symm R)

end HodgeLean.Foundations.Program
