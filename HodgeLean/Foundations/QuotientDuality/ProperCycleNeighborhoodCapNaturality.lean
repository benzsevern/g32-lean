import HodgeLean.Foundations.QuotientDuality.ProperCycleRetractedCapRestriction

/-! # Naturality of actual excised neighborhood cap classes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Projection of an actual homology class to relative homology commutes with a map of pairs.
Source: Hatcher, Algebraic Topology, section 2.1, functoriality of relative homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_homology_projection_naturality
    {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ) (c : Homology ℚ P.fst n) :
    relativeHomologyMap ℚ n f ((relativeHomologyProjection ℚ P n).hom c) =
      (relativeHomologyProjection ℚ Q n).hom (homologyMap ℚ n (TopPair.Hom.fst f) c) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

/-- The actual neighborhood excision inverse transports the projected original class along a commuting square of complement pairs.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_relative_fundamental_naturality
    (X Y : TopCat.{0}) (S : Set X) (T : Set Y) (U : Set X) (V : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) (hU : IsOpen U) (hV : IsOpen V)
    (hSU : S ⊆ U) (hTV : T ⊆ V)
    (f : TopPair.ofSubset (X := X) Sᶜ ⟶ TopPair.ofSubset (X := Y) Tᶜ)
    (g : neighborhoodSupportComplementPair U S ⟶ neighborhoodSupportComplementPair V T)
    (hsquare : g ≫ b6m_subspacePairMap Y V Tᶜ = b6m_subspacePairMap X U Sᶜ ≫ f)
    (n : ℕ) (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n g
      (properCycle_neighborhood_relative_fundamental X S U hS hU hSU n c) =
      properCycle_neighborhood_relative_fundamental Y T V hT hV hTV n
        (homologyMap ℚ n (TopPair.Hom.fst f) c) := by
  apply (b6m_closed_support_excision_bijective ℚ hV hT hTV n).injective
  have hm : (relativeHomologyMap ℚ n (b6m_subspacePairMap Y V Tᶜ)).comp
      (relativeHomologyMap ℚ n g) =
      (relativeHomologyMap ℚ n f).comp
        (relativeHomologyMap ℚ n (b6m_subspacePairMap X U Sᶜ)) := by
    rw [← relativeHomologyMap_comp, hsquare, relativeHomologyMap_comp]
  calc
    _ = relativeHomologyMap ℚ n f
        (relativeHomologyMap ℚ n (b6m_subspacePairMap X U Sᶜ)
          (properCycle_neighborhood_relative_fundamental X S U hS hU hSU n c)) :=
      LinearMap.congr_fun hm _
    _ = relativeHomologyMap ℚ n f ((relativeHomologyProjection ℚ
        (TopPair.ofSubset (X := X) Sᶜ) n).hom c) := by
      rw [properCycle_neighborhood_relative_fundamental_pushforward]
    _ = _ := (properCycle_relative_homology_projection_naturality f n c).trans
      (properCycle_neighborhood_relative_fundamental_pushforward Y T V hT hV hTV n _).symm

/-- The actual neighborhood cap commutes with a map of complement pairs and its actual neighborhood restriction.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, excision and relative cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_cap_naturality
    (X Y : TopCat.{0}) (S : Set X) (T : Set Y) (U : Set X) (V : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) (hU : IsOpen U) (hV : IsOpen V)
    (hSU : S ⊆ U) (hTV : T ⊆ V)
    (f : TopPair.ofSubset (X := X) Sᶜ ⟶ TopPair.ofSubset (X := Y) Tᶜ)
    (g : neighborhoodSupportComplementPair U S ⟶ neighborhoodSupportComplementPair V T)
    (hsquare : g ≫ b6m_subspacePairMap Y V Tᶜ = b6m_subspacePairMap X U Sᶜ ≫ f)
    (p q : ℕ) (a : CohomologyWithSupport ℚ Y T p) (c : Homology ℚ X (p + q)) :
    homologyMap ℚ q (TopPair.Hom.fst g)
      (properCycle_neighborhood_cap X S U hS hU hSU p q
        (relativeCohomologyMap ℚ p f a) c) =
      properCycle_neighborhood_cap Y T V hT hV hTV p q a
        (homologyMap ℚ (p + q) (TopPair.Hom.fst f) c) := by
  have ha : relativeCohomologyMap ℚ p (b6m_subspacePairMap X U Sᶜ)
      (relativeCohomologyMap ℚ p f a) =
      relativeCohomologyMap ℚ p g
        (relativeCohomologyMap ℚ p (b6m_subspacePairMap Y V Tᶜ) a) := by
    have hm := congrArg (fun h => relativeCohomologyMap ℚ p h) hsquare
    rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at hm
    exact (LinearMap.congr_fun hm a).symm
  have hd := properCycle_neighborhood_relative_fundamental_naturality
    X Y S T U V hS hT hU hV hSU hTV f g hsquare (p + q) c
  change homologyMap ℚ q (TopPair.Hom.fst g)
    (relativeCapCohomologyLinear ℚ (neighborhoodSupportComplementPair U S) p q
      (relativeCohomologyMap ℚ p (b6m_subspacePairMap X U Sᶜ)
        (relativeCohomologyMap ℚ p f a))
      (properCycle_neighborhood_relative_fundamental X S U hS hU hSU (p + q) c)) = _
  rw [ha]
  exact (properCycle_relative_cap_naturality g p q
    (relativeCohomologyMap ℚ p (b6m_subspacePairMap Y V Tᶜ) a) _).trans
    (congrArg (relativeCapCohomologyLinear ℚ (neighborhoodSupportComplementPair V T) p q
      (relativeCohomologyMap ℚ p (b6m_subspacePairMap Y V Tᶜ) a)) hd)

/-- Homotopy retractions transport actual homology maps along maps respecting the original support inclusions.
Source: Hatcher, Algebraic Topology, section 2.1, homotopy invariance.
HC no distance; AV milestone no distance. -/
lemma properCycle_homology_retraction_naturality
    {S T U V : TopCat.{0}} (jS : S ⟶ U) (jT : T ⟶ V)
    (rS : U ⟶ S) (rT : V ⟶ T) (g : U ⟶ V) (s : S ⟶ T)
    (hsquare : jS ≫ g = s ≫ jT) (hjT : jT ≫ rT = 𝟙 T)
    (H : TopCat.Homotopy (𝟙 U) (rS ≫ jS)) (n : ℕ) :
    (homologyMap ℚ n rT).comp (homologyMap ℚ n g) =
      (homologyMap ℚ n s).comp (homologyMap ℚ n rS) := by
  have he : homologyMap ℚ n (rS ≫ jS) = homologyMap ℚ n (𝟙 U) :=
    (congrArg ModuleCat.Hom.hom
      ((H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq n)).symm
  have hs : jS ≫ (g ≫ rT) = s := by
    rw [← Category.assoc, hsquare, Category.assoc, hjT, Category.comp_id]
  ext z
  have hz : homologyMap ℚ n jS (homologyMap ℚ n rS z) = z := by
    simpa only [homologyMap_comp, LinearMap.comp_apply, homologyMap_id, LinearMap.id_apply]
      using LinearMap.congr_fun he z
  change homologyMap ℚ n rT (homologyMap ℚ n g z) = _
  rw [← hz]
  rw [← LinearMap.comp_apply, ← homologyMap_comp,
    ← LinearMap.comp_apply, ← homologyMap_comp, hs]
  exact congrArg (fun w => homologyMap ℚ n s (homologyMap ℚ n rS w)) hz.symm

/-- Retracting the actual excised cap to its support preserves naturality whenever the neighborhood map respects the support inclusions.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, homotopy invariance and supported cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_retracted_neighborhood_cap_naturality
    (X Y : TopCat.{0}) (S : Set X) (T : Set Y) (U : Set X) (V : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) (hU : IsOpen U) (hV : IsOpen V)
    (hSU : S ⊆ U) (hTV : T ⊆ V)
    (f : TopPair.ofSubset (X := X) Sᶜ ⟶ TopPair.ofSubset (X := Y) Tᶜ)
    (g : neighborhoodSupportComplementPair U S ⟶ neighborhoodSupportComplementPair V T)
    (hsquare : g ≫ b6m_subspacePairMap Y V Tᶜ = b6m_subspacePairMap X U Sᶜ ≫ f)
    (jS : TopCat.of S ⟶ TopCat.of U) (jT : TopCat.of T ⟶ TopCat.of V)
    (rS : TopCat.of U ⟶ TopCat.of S) (rT : TopCat.of V ⟶ TopCat.of T)
    (s : TopCat.of S ⟶ TopCat.of T)
    (hsupport : jS ≫ TopPair.Hom.fst g = s ≫ jT)
    (hjT : jT ≫ rT = 𝟙 (TopCat.of T))
    (H : TopCat.Homotopy (𝟙 (TopCat.of U)) (rS ≫ jS))
    (p q : ℕ) (a : CohomologyWithSupport ℚ Y T p) (c : Homology ℚ X (p + q)) :
    homologyMap ℚ q s
      (properCycle_retracted_neighborhood_cap X S U hS hU hSU rS p q
        (relativeCohomologyMap ℚ p f a) c) =
      properCycle_retracted_neighborhood_cap Y T V hT hV hTV rT p q a
        (homologyMap ℚ (p + q) (TopPair.Hom.fst f) c) := by
  have hm := properCycle_homology_retraction_naturality jS jT rS rT
    (TopPair.Hom.fst g) s hsupport hjT H q
  have hc := properCycle_neighborhood_cap_naturality
    X Y S T U V hS hT hU hV hSU hTV f g hsquare p q a c
  change homologyMap ℚ q s (homologyMap ℚ q rS _) = homologyMap ℚ q rT _
  exact (LinearMap.congr_fun hm _).symm.trans (congrArg (homologyMap ℚ q rT) hc)

end HodgeLean.Foundations.QuotientDuality
