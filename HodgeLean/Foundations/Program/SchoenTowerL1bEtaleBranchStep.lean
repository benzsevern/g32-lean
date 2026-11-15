import HodgeLean.Foundations.Program.SchoenTowerL1bRegularTransform
import HodgeLean.Foundations.Program.SchoenTowerL1bAffineIdeal

/-! Actual branch ideal equations in an etale successor chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A branch coordinate outside the centre retains its exact reduced transform
ideal on an actual etale blowup chart, including its exceptional points. -/
theorem s2v_l1b_etale_chart_branch_step
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hV : V.1 ≤ f ⁻¹ᵁ U.1)
    {k σ : Type*} [CommRing k] [IsDomain k] [DecidableEq σ]
    (c : k →+* Γ(X, V)) (z : σ → Γ(Y, U)) (w : σ → Γ(X, V))
    (hw : (MvPolynomial.eval₂Hom c w).Etale) (a b t : σ)
    (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b)
    (hcoords : ∀ j, (f.appLE U.1 V.1 hV).hom (z j) =
      if j = a then w a * w b else w j)
    (hD : D.ideal U = Ideal.span {z t}) (hK : z b ∈ K.ideal U) :
    (s2c_strictTransform f D K).ideal V = Ideal.span {w t} := by
  have ht : (f.appLE U.1 V.1 hV).hom (z t) = w t :=
    (hcoords t).trans (ite_eq_right hta)
  have hb : (f.appLE U.1 V.1 hV).hom (z b) = w b :=
    (hcoords b).trans (ite_eq_right hab.symm)
  apply s2v_l1b_strictTransform_etale_coordinate f D K V c w hw t b htb
  · rw [s2v_l1b_comap_ideal_affine_charts f D U V hV, hD,
      Ideal.map_span, Set.image_singleton, ht]
  · rw [s2v_l1b_comap_ideal_affine_charts f K U V hV, ← hb]
    exact Ideal.mem_map_of_mem _ hK

end HodgeLean.Foundations.Program
