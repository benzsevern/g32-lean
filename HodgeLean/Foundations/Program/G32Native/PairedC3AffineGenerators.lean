import HodgeLean.Foundations.Program.SchoenCycleAffineIdealShrinking
import HodgeLean.Foundations.Program.SchoenCycleSimultaneousAffineGerms

/-! # Affine equations realizing a prescribed finite stalk generating family -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Prescribed finite generators in a stalk extend to generators of the
same ideal sheaf on an affine neighbourhood inside the supplied chart.
Source: Hartshorne, Algebraic Geometry, II.5, finite ideals and stalks. -/
theorem paired_c3_affine_generators_of_stalk_generators
    (X : Scheme) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    {ι : Type*} [Finite ι] (t : ι → X.presheaf.stalk x)
    (hgen : (I.ideal U).map (X.presheaf.germ U.1 x hx).hom =
      Ideal.span (Set.range t)) :
    ∃ (V : X.affineOpens) (hVU : V ≤ U) (hxV : x ∈ V.1)
      (f : ι → Γ(X, V.1)), I.ideal V = Ideal.span (Set.range f) ∧
        ∀ i, (X.presheaf.germ V.1 x hxV).hom (f i) = t i := by
  obtain ⟨W, hW, hWU, hxW, c, hc⟩ :=
    s2e_simultaneous_affine_germ_representatives X x U.1 hx t
  let Wb : X.affineOpens := ⟨W, hW⟩
  have he : (I.ideal Wb).map (X.presheaf.germ W x hxW).hom =
      (Ideal.span (Set.range c)).map (X.presheaf.germ W x hxW).hom := by
    rw [← I.map_ideal (show Wb ≤ U from hWU), Ideal.map_map,
      ← CommRingCat.hom_comp]
    change (I.ideal U).map ((X.presheaf.map (homOfLE hWU).op ≫
      X.presheaf.germ W x hxW).hom) = _
    rw [X.presheaf.germ_res, hgen, Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext hc)).symm
  letI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian Wb
  obtain ⟨V, hVW, hxV, hEq⟩ := s2e_affine_ideals_equal_near_point X Wb x hxW
    (I.ideal Wb) (Ideal.span (Set.range c)) (Ideal.fg_of_isNoetherianRing _)
    (Ideal.fg_of_isNoetherianRing _) he
  let res := X.presheaf.map (homOfLE (X := X.Opens) hVW).op
  refine ⟨V, hVW.trans hWU, hxV, fun i => res.hom (c i), ?_, ?_⟩
  · have h := (I.map_ideal hVW).symm.trans hEq
    rw [Ideal.map_span, ← Set.range_comp] at h
    exact h
  · intro i
    change (res ≫ X.presheaf.germ V.1 x hxV).hom (c i) = t i
    rw [X.presheaf.germ_res]
    exact hc i

#print axioms paired_c3_affine_generators_of_stalk_generators
end HodgeLean.Foundations.Program.G32Native
