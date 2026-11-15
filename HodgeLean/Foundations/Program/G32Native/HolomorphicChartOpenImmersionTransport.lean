import HodgeLean.Foundations.Program.G32Native.HolomorphicChartIsoTransport

/-! # Holomorphic chart transport through an arbitrary ambient open immersion

The isomorphism with the actual open image retains the given scheme map.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Set Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler

theorem holomorphic_chart_openImmersion_transport
    (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [Nonempty (ComplexPoint X)]
    (f : X ⟶ Y) [IsOpenImmersion f.left] (r c : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) :
    ∃ a : OpenPartialHomeomorph (ComplexPoint Y) ((Fin r → ℂ) × (Fin c → ℂ)),
      a3b4_IsHolChart Y.hom a ∧
      a.source = Point.map f '' e.source ∧
      ∀ y, a (Point.map f y) = e y := by
  let O := f.left.opensRange
  let Z := ComplexPoint.openScheme Y O
  letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  letI : IsNoetherian Y.left := ⟨⟩
  letI : LocallyOfFiniteType Z.hom :=
    inferInstanceAs (LocallyOfFiniteType (O.ι ≫ Y.hom))
  letI : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (O.ι ≫ Y.hom))
  letI : IsSeparated Z.hom := inferInstanceAs (IsSeparated (O.ι ≫ Y.hom))
  have hI : f.left.isoOpensRange.hom ≫ (O.ι ≫ Y.hom) = X.hom := by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact Over.w f
  let I : X ≅ Z := Over.isoMk f.left.isoOpensRange hI
  let g := ComplexPoint.openInclusion Y O
  have hcomp : I.hom ≫ g = f := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.isoOpensRange_hom_ι f.left
  have hpoint : Point.map g ∘ Point.map I.hom = Point.map f := by
    funext y
    rw [Function.comp_apply, ← Point.map_comp_apply, hcomp]
  letI : Nonempty (ComplexPoint Z) :=
    ⟨Point.map I.hom (Classical.choice inferInstance)⟩
  obtain ⟨eZ, heZ, hsourceZ, hevalZ⟩ := holomorphic_chart_iso_transport X Z I r c e he
  obtain ⟨a, ha, hsource, heval⟩ :=
    a3b4a_classHolomorphicChart_openTransport Y O r c eZ heZ
  refine ⟨a, ha, ?_, ?_⟩
  · rw [hsource, hsourceZ, Set.image_image]
    change (Point.map g ∘ Point.map I.hom) '' e.source = Point.map f '' e.source
    rw [hpoint]
  · intro y
    have hp := congrFun hpoint y
    change Point.map g (Point.map I.hom y) = Point.map f y at hp
    rw [← hp, heval, hevalZ]

#print axioms holomorphic_chart_openImmersion_transport
end HodgeLean.Foundations.TubularEuler
