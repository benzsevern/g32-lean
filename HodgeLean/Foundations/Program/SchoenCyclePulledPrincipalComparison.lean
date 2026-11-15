import HodgeLean.Foundations.Program.SchoenCycleS1i4
import HodgeLean.Foundations.Program.SchoenCycleNativeGermComparison
import HodgeLean.Adapters.IntersectionProductScaf

/-! # Comparing pulled principal equations in native source coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An analytic unit between a pulled generator and a source generator identifies
their actual ideal stalks on a common affine neighbourhood.
Source: Serre, GAGA, §2, no. 6, Proposition 3 and Corollary 1;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_pulled_principal_analytic_unit_stalk
    (X Y : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : X ⟶ Y) (I : Y.left.IdealSheafData) (J : X.left.IdealSheafData)
    (p : ComplexPoint X) (U : Y.left.affineOpens)
    (hpU : (Point.map f p).underlying ∈ U.1)
    (s : Γ(Y.left, U.1)) (hs : I.ideal U = Ideal.span {s})
    (V : X.left.affineOpens) (hpV : p.underlying ∈ V.1)
    (t : Γ(X.left, V.1)) (ht : J.ideal V = Ideal.span {t})
    (η : (Fin d → ℂ) → ℂ) (hη : AnalyticAt ℂ η 0) (hη0 : η 0 ≠ 0)
    (he : (fun z => Point.evaluate U.1 s (Point.map f
      ((localChart X d p).symm (localChart X d p p + z)))) =ᶠ[𝓝 0]
      (fun z => η z * Point.evaluate V.1 t
        ((localChart X d p).symm (localChart X d p p + z)))) :
    ∃ W : X.left.affineOpens, ∃ hpW : p.underlying ∈ W.1,
      Ideal.map (X.left.presheaf.germ W.1 p.underlying hpW).hom ((I.comap f.left).ideal W) =
        Ideal.map (X.left.presheaf.germ W.1 p.underlying hpW).hom (J.ideal W) := by
  have hp : p.underlying ∈ (f.left ⁻¹ᵁ U.1) ⊓ V.1 := ⟨hpU, hpV⟩
  obtain ⟨W, hW, hpW, hsub⟩ := exists_isAffineOpen_mem_and_subset hp
  have hWU : W ≤ f.left ⁻¹ᵁ U.1 := fun _ hx => (hsub hx).1
  have hWV : W ≤ V.1 := fun _ hx => (hsub hx).2
  let sW := (f.left.appLE U.1 W hWU).hom s
  let tW := (X.left.presheaf.map (homOfLE hWV).op).hom t
  have hIW : (I.comap f.left).ideal ⟨W, hW⟩ = Ideal.span {sW} := by
    rw [IntersectionProductScaf_comap_ideal_affine_charts f.left I U ⟨W, hW⟩ hWU,
      hs, Ideal.map_span, Set.image_singleton]
  have hJW : J.ideal ⟨W, hW⟩ = Ideal.span {tW} := by
    rw [← J.map_ideal hWV, ht, Ideal.map_span, Set.image_singleton]
    rfl
  have hmem : ∀ᶠ z in 𝓝 (0 : Fin d → ℂ),
      ((localChart X d p).symm (localChart X d p p + z)).underlying ∈ W :=
    s2e_centered_native_chart_tendsto X d p ((Point.isOpen_overOpen W).mem_nhds hpW)
  have heW : (fun z => Point.evaluate W sW
        ((localChart X d p).symm (localChart X d p p + z))) =ᶠ[𝓝 0]
      (fun z => η z * Point.evaluate W tW
        ((localChart X d p).symm (localChart X d p p + z))) := by
    filter_upwards [he, hmem] with z hz hzm
    let q := (localChart X d p).symm (localChart X d p p + z)
    have hsE : Point.evaluate W sW q = Point.evaluate U.1 s (Point.map f q) :=
      (Point.evaluate_res hWU (f.left.app U.1 s) q hzm).symm.trans
        (Point.evaluate_map f U.1 s q).symm
    have htE : Point.evaluate W tW q = Point.evaluate V.1 t q :=
      (Point.evaluate_res hWV t q hzm).symm
    rw [hsE, htE]
    exact hz
  refine ⟨⟨W, hW⟩, hpW, ?_⟩
  rw [hIW, hJW, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  exact s2e_analytic_unit_descends_principal_ideal X d p W hpW sW tW η hη hη0 heW

end HodgeLean.Foundations.Program
