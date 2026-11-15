import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionPointEquality
import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionBoundary

/-! Actual point-relative boundary witnesses of ambient subdivision sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equality with an ambient boundary section gives an actual subdivided relative boundary at every point of its domain.
Source: Bredon, Sheaf Theory, second edition, VI.12; local boundary representatives and subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_point_boundary (X : TopCat.{0}) (n m k : ℕ)
    (U : Opens X) (z : (SingularChainComplex ℚ X).X n)
    (a : (SingularChainComplex ℚ X).X (n + 1))
    (h : (subdivisionAmbientSectionMap X n U m).hom z =
      (subdivisionAmbientSectionMap X n U k).hom ((SingularChainComplex ℚ X).d (n + 1) n a))
    (x : X) (hx : x ∈ U) :
    ∃ (r : ℕ) (b : ((relativeChainFunctor ℚ).obj (pointComplementPair x)).X (n + 1)),
      ((relativeChainFunctor ℚ).obj (pointComplementPair x)).d (n + 1) n b =
        (relativeChainProjection ℚ (pointComplementPair x)).f n
          ((rationalSubdivisionIterate X r).f n z) := by
  obtain ⟨r, s, he⟩ := subdivisionAmbientSection_point_eq_eventually X n m k U z
    ((SingularChainComplex ℚ X).d (n + 1) n a) h x hx
  let π := relativeChainProjection ℚ (pointComplementPair x)
  let b := π.f (n + 1) ((rationalSubdivisionIterate X s).f (n + 1) a)
  refine ⟨r, b, ?_⟩
  have hπ := ConcreteCategory.congr_hom (π.comm (n + 1) n)
    ((rationalSubdivisionIterate X s).f (n + 1) a)
  change ((relativeChainFunctor ℚ).obj (pointComplementPair x)).d (n + 1) n b =
    π.f n ((SingularChainComplex ℚ X).d (n + 1) n
      ((rationalSubdivisionIterate X s).f (n + 1) a)) at hπ
  have hd := ConcreteCategory.congr_hom ((rationalSubdivisionIterate X s).comm (n + 1) n) a
  change (SingularChainComplex ℚ X).d (n + 1) n
      ((rationalSubdivisionIterate X s).f (n + 1) a) =
    (rationalSubdivisionIterate X s).f n ((SingularChainComplex ℚ X).d (n + 1) n a) at hd
  rw [hd] at hπ
  exact hπ.trans he.symm

#print axioms subdivisionAmbientSection_point_boundary
/-- A sheaf primitive of an ambient section supplies an actual subdivided boundary witness at each point.
Source: Bredon, Sheaf Theory, second edition, VI.12; local ambient representatives of supported sheaf primitives.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_sheaf_primitive_point_boundary (X : TopCat.{0}) (n m : ℕ)
    (U : Opens X) (z : (SingularChainComplex ℚ X).X n)
    (s : ((subdivisionLimitSheafComplex X).X (n + 1)).obj.obj (Opposite.op U))
    (hs : (((subdivisionLimitSheafComplex X).d (n + 1) n).hom.app (Opposite.op U)) s =
      (subdivisionAmbientSectionMap X n U m).hom z) (x : X) (hx : x ∈ U) :
    ∃ (r : ℕ) (b : ((relativeChainFunctor ℚ).obj (pointComplementPair x)).X (n + 1)),
      ((relativeChainFunctor ℚ).obj (pointComplementPair x)).d (n + 1) n b =
        (relativeChainProjection ℚ (pointComplementPair x)).f n
          ((rationalSubdivisionIterate X r).f n z) := by
  obtain ⟨V, hV, k, a, hxV, ha⟩ :=
    subdivisionLimitSheaf_section_locally_ambient X (n + 1) U s x hx
  change (subdivisionAmbientSectionMap X (n + 1) V k).hom a =
    ((subdivisionLimitSheafComplex X).X (n + 1)).obj.map (homOfLE hV).op s at ha
  let d := ((subdivisionLimitSheafComplex X).d (n + 1) n).hom
  have hn := ConcreteCategory.congr_hom (d.naturality (homOfLE hV).op) s
  change d.app (Opposite.op V)
      (((subdivisionLimitSheafComplex X).X (n + 1)).obj.map (homOfLE hV).op s) =
    ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hV).op
      (d.app (Opposite.op U) s) at hn
  rw [← ha, hs] at hn
  have hb := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_boundary X n k V) a
  change d.app (Opposite.op V) ((subdivisionAmbientSectionMap X (n + 1) V k).hom a) =
    (subdivisionAmbientSectionMap X n V k).hom ((SingularChainComplex ℚ X).d (n + 1) n a) at hb
  have hr := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_restriction X n m U V hV) z
  change ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hV).op
      ((subdivisionAmbientSectionMap X n U m).hom z) =
    (subdivisionAmbientSectionMap X n V m).hom z at hr
  exact subdivisionAmbientSection_point_boundary X n m k V z a
    (hr.symm.trans (hn.symm.trans hb)) x hxV

#print axioms subdivisionAmbientSection_sheaf_primitive_point_boundary
end HodgeLean.Foundations.RationalHomologyManifold
