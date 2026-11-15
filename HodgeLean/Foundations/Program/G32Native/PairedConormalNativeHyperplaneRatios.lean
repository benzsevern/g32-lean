import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneSections

/-! # Native affine coordinates as actual regular sections -/

noncomputable section
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- The affine chart-ring inverse is the canonical homogeneous-localization
section map with its original open-set transport. -/
theorem paired_nativeHyperplaneChartEquiv_symm (k : ℕ) (i : Fin (k + 1))
    (r : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ) (MvPolynomial.X i)) :
    (paired_nativeHyperplaneChartEquiv k i).symm r =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).presheaf.map
        (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).le).op
        (Proj.awayToSection _ (MvPolynomial.X i) r) := by
  let G := MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ
  let U := Proj.basicOpen G (MvPolynomial.X i)
  let e := Proj.basicOpenIsoSpec G (MvPolynomial.X i) (ProjSpace.X_mem_one ℂ k i) one_pos
  let f := Proj.awayι G (MvPolynomial.X i) (ProjSpace.X_mem_one ℂ k i) one_pos
  have hh := IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq e.hom f U.ι
    (by dsimp [f, e, U, Proj.awayι]; simp only [Iso.hom_inv_id_assoc]) ⊤
  change (Proj.basicOpenToSpec G (MvPolynomial.X i)).app ⊤ = _ at hh
  rw [Proj.basicOpenToSpec_app_top] at hh
  have ht := congrArg (fun m => (Scheme.ΓSpecIso _).inv ≫ m ≫ U.topIso.hom ≫
    (Proj G).presheaf.map (homOfLE (paired_nativeHyperplaneChartOpen_eq k i).le).op) hh
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Scheme.Opens.ι_app, Scheme.Opens.topIso_hom,
    Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp] at ht
  have ht' := congrArg (fun m => m r) ht
  exact ht'.symm

end HodgeLean.Foundations.Program.G32Native
