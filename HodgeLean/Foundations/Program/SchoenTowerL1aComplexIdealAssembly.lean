import HodgeLean.Foundations.Program.SchoenTowerL1aIdealAssembly
import HodgeLean.Foundations.Program.SchoenTowerL1aComplexCover

/-! # Principal ideal charts indexed by complex points

Implication from compatible affine principal charts at complex points to the
global scheme ideal comparison. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Affine principal charts at complex points suffice for the global scheme ideal comparison.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5–6, Jacobson schemes and ideal-sheaf locality. -/
theorem s2v_l1a_ideal_comparison_of_complex_principal_charts
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {ι : Type*} [Fintype ι] (γ : X ⟶ Y)
    (I : Y.left.IdealSheafData) (J : ι → X.left.IdealSheafData)
    (hcharts : ∀ x : ComplexPoint X,
      ∃ (U V : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (hV : IsAffine V.left)
        (u : U ⟶ Y) (v : V ⟶ X) (q : V ⟶ U),
        IsOpenImmersion v.left ∧ v ≫ γ = q ≫ u ∧ x ∈ Set.range (Point.map v) ∧
        ∃ (c : Γ(U.left, ⊤)) (z : ι → Γ(V.left, ⊤)),
          (I.comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ = Ideal.span {c} ∧
          (∀ j, ((J j).comap v.left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
            Ideal.span {z j}) ∧ q.left.appTop.hom c = ∏ j, z j) :
    I.comap γ.left = ∏ j, J j := by
  choose U V hU hV u v q hv hsquare hx c z hI hJ hc using hcharts
  let : ∀ x, IsAffine (U x).left := hU
  let : ∀ x, IsAffine (V x).left := hV
  let : ∀ x, IsOpenImmersion (v x).left := hv
  have hcover : ∀ x : X.left, ∃ k, x ∈ Set.range (v k).left :=
    s2v_l1a_scheme_cover_of_complex_cover X V v (fun x => ⟨x, hx x⟩)
  apply s2v_l1a_ideal_comparison_of_principal_cover γ.left I J
    (fun x => (U x).left) (fun x => (V x).left)
    (fun x => (u x).left) (fun x => (v x).left) (fun x => (q x).left)
    (fun x => congrArg (fun f : V x ⟶ Y => f.left) (hsquare x))
    hcover c z hI hJ hc

end HodgeLean.Foundations.Program
