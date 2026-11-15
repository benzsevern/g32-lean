import HodgeLean.Foundations.Program.SchoenCycleIdealStalkCharts
import HodgeLean.Foundations.Program.SchoenCycleIdealSupportNeighbourhood
import Mathlib.RingTheory.Localization.Ideal

/-! # Finite intersections of actual ideal stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite intersection of affine ideals commutes with passage to the actual stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_affine_stalk_map_finite_iInf
    {X : Scheme} (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    {ι : Type*} [Finite ι] (J : ι → Ideal Γ(X, U.1)) :
    Ideal.map (X.presheaf.germ U.1 x hx).hom (⨅ i, J i) =
      ⨅ i, Ideal.map (X.presheaf.germ U.1 x hx).hom (J i) := by
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hx).hom.toAlgebra
  letI := U.2.isLocalization_stalk ⟨x, hx⟩
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Function.comp_apply, IsLocalization.mapFrameHom_apply, RingHom.algebraMap_toAlgebra] using map_finset_inf (IsLocalization.mapFrameHom
    (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)) Finset.univ J

/-- Outside an actual ideal support, its image ideal in any affine stalk chart is the unit ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_ideal_stalk_eq_top_off_support
    {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : X) (hxU : x ∈ U.1) (hx : x ∉ I.support) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) = ⊤ := by
  obtain ⟨V, hxV, hV⟩ := s2e_affine_ideal_eq_top_of_not_mem_support I x hx
  rw [s2e_ideal_stalk_affine_chart_independent I U V x hxU hxV, hV,
    Ideal.map_top]

end HodgeLean.Foundations.Program
