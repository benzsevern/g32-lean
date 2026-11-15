import HodgeLean.Foundations.Program.G32Native.EtaleConormalComparison

/-! # Conormal comparison over the specified etale locus
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified etale locus containing the component suffices for actual conormal transport.
Source: Hartshorne, Algebraic Geometry, II.8, localization and flat base change of conormals;
EGA IV, 17.9.3 and 17.11.1.
HC no distance; AV milestone no distance. -/
theorem s2e_i1_etale_locus_component_conormalIso
    {Q P W B : Over (Spec ↧ℂ)} (i : P ⟶ B) [IsClosedImmersion i.left]
    (β : W ⟶ B) (U : B.left.Opens) (hU : Set.range i.left ⊆ U)
    (het : Etale (β.left ∣_ U)) (g : Q ⟶ P) [IsIso g.left]
    (j : Q ⟶ W) [IsClosedImmersion j.left] (h : g ≫ i = j ≫ β) :
    Nonempty (Conormal.sheaf j.left ≅
      (Scheme.Modules.pullback g.left).obj (Conormal.sheaf i.left)) := by
  let V := β.left ⁻¹ᵁ U
  have hiRange : Set.range i.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hU
  let i₀ := IsOpenImmersion.lift U.ι i.left hiRange
  have hi : i₀ ≫ U.ι = i.left := IsOpenImmersion.lift_fac _ _ _
  have hjRange : Set.range j.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change β.left (j.left x) ∈ U
    have hh : i.left (g.left x) = β.left (j.left x) :=
      congrArg (fun f : Q ⟶ B => f.left x) h
    exact hh ▸ hU ⟨g.left x, rfl⟩
  let j₀ := IsOpenImmersion.lift V.ι j.left hjRange
  have hj : j₀ ≫ V.ι = j.left := IsOpenImmersion.lift_fac _ _ _
  let BU : Over (Spec ↧ℂ) := Over.mk (U.ι ≫ B.hom)
  let WV : Over (Spec ↧ℂ) := Over.mk (V.ι ≫ W.hom)
  let iU : P ⟶ BU := Over.homMk i₀ (by
    change i₀ ≫ (U.ι ≫ B.hom) = P.hom
    rw [← Category.assoc, hi]
    exact Over.w i)
  let jV : Q ⟶ WV := Over.homMk j₀ (by
    change j₀ ≫ (V.ι ≫ W.hom) = Q.hom
    rw [← Category.assoc, hj]
    exact Over.w j)
  let βU : WV ⟶ BU := Over.homMk (β.left ∣_ U) (by
    change (β.left ∣_ U) ≫ U.ι ≫ B.hom = V.ι ≫ W.hom
    rw [morphismRestrict_ι_assoc, Over.w β])
  letI : Etale βU.left := het
  letI : IsClosedImmersion (i₀ ≫ U.ι) := hi.symm ▸ inferInstance
  letI : IsClosedImmersion i₀ := IsClosedImmersion.of_comp i₀ U.ι
  letI : IsClosedImmersion (j₀ ≫ V.ι) := hj.symm ▸ inferInstance
  letI : IsClosedImmersion j₀ := IsClosedImmersion.of_comp j₀ V.ι
  letI : IsClosedImmersion iU.left := (show IsClosedImmersion i₀ from inferInstance)
  letI : IsClosedImmersion jV.left := (show IsClosedImmersion j₀ from inferInstance)
  have hsquare : g ≫ iU = jV ≫ βU := by
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    change g.left ≫ i₀ ≫ U.ι = j₀ ≫ (β.left ∣_ U) ≫ U.ι
    rw [hi, morphismRestrict_ι, ← Category.assoc, hj]
    exact congrArg Over.Hom.left h
  obtain ⟨E⟩ := s2e_i1_etale_component_conormalIso iU βU g jV hsquare
  exact ⟨(Classical.choice (i1_openConormalIso_aux j V.ι j₀ hj)).symm ≪≫ E ≪≫
    (Scheme.Modules.pullback g.left).mapIso
      (Classical.choice (i1_openConormalIso_aux i U.ι i₀ hi))⟩

#print axioms s2e_i1_etale_locus_component_conormalIso

end HodgeLean.Foundations.Program.G32Native
