import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionEquality

/-! Actual point-relative witnesses for equality of ambient sections at different subdivision stages.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equal ambient sheaf sections at possibly different stages give equal actual point-relative subdivided chains.
Source: Bredon, Sheaf Theory, second edition, VI.12; local finite-stage equality and relative point projection.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_point_eq_eventually (X : TopCat.{0}) (n a b : ℕ)
    (U : Opens X) (z w : (SingularChainComplex ℚ X).X n)
    (h : (subdivisionAmbientSectionMap X n U a).hom z =
      (subdivisionAmbientSectionMap X n U b).hom w) (x : X) (hx : x ∈ U) :
    ∃ r s : ℕ, (relativeChainProjection ℚ (pointComplementPair x)).f n
        ((rationalSubdivisionIterate X r).f n z) =
      (relativeChainProjection ℚ (pointComplementPair x)).f n
        ((rationalSubdivisionIterate X s).f n w) := by
  have hz := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_transition X n U a b) z
  have hw := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_transition X n U b a) w
  change (subdivisionAmbientSectionMap X n U (a + b)).hom
      ((rationalSubdivisionIterate X b).f n z) = (subdivisionAmbientSectionMap X n U a).hom z at hz
  change (subdivisionAmbientSectionMap X n U (b + a)).hom
      ((rationalSubdivisionIterate X a).f n w) = (subdivisionAmbientSectionMap X n U b).hom w at hw
  rw [Nat.add_comm b a] at hw
  obtain ⟨V, hV, t, hxV, he⟩ := subdivisionAmbientSection_eq_locally_subdivided X n (a + b) U
    ((rationalSubdivisionIterate X b).f n z) ((rationalSubdivisionIterate X a).f n w)
    (hz.trans (h.trans hw.symm)) x hx
  let P := TopPair.ofSubset (X := X) (V : Set X)ᶜ
  let Q := pointComplementPair x
  let f := supportInclusionPairMap X (Set.singleton_subset_iff.mpr hxV)
  let φ := (relativeChainFunctor ℚ).map f
  have hp := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f
  change relativeChainProjection ℚ P ≫ φ =
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫ relativeChainProjection ℚ Q at hp
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hp
  have hpn := congrArg (fun f => f.f n) hp
  have hpz := ConcreteCategory.congr_hom hpn
    ((rationalSubdivisionIterate X t).f n ((rationalSubdivisionIterate X b).f n z))
  have hpw := ConcreteCategory.congr_hom hpn
    ((rationalSubdivisionIterate X t).f n ((rationalSubdivisionIterate X a).f n w))
  change φ.f n ((relativeChainProjection ℚ P).f n
      ((rationalSubdivisionIterate X t).f n ((rationalSubdivisionIterate X b).f n z))) =
    (relativeChainProjection ℚ Q).f n
      ((rationalSubdivisionIterate X t).f n ((rationalSubdivisionIterate X b).f n z)) at hpz
  change φ.f n ((relativeChainProjection ℚ P).f n
      ((rationalSubdivisionIterate X t).f n ((rationalSubdivisionIterate X a).f n w))) =
    (relativeChainProjection ℚ Q).f n
      ((rationalSubdivisionIterate X t).f n ((rationalSubdivisionIterate X a).f n w)) at hpw
  have hpoint := hpz.symm.trans ((congrArg (φ.f n) he).trans hpw)
  change (relativeChainProjection ℚ Q).f n
      ((rationalSubdivisionIterate X b ≫ rationalSubdivisionIterate X t).f n z) =
    (relativeChainProjection ℚ Q).f n
      ((rationalSubdivisionIterate X a ≫ rationalSubdivisionIterate X t).f n w) at hpoint
  rw [← rationalSubdivisionIterate_add X b t, ← rationalSubdivisionIterate_add X a t] at hpoint
  exact ⟨b + t, a + t, hpoint⟩

#print axioms subdivisionAmbientSection_point_eq_eventually
end HodgeLean.Foundations.RationalHomologyManifold
