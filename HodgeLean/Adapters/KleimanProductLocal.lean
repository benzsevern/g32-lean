import HodgeLean.Adapters.KleimanProductDefs
import HodgeLean.Adapters.CycleClassDivisorLocalTransport

/-! # Local tools for the supported intersection product
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- The closure of a scheme point minus a closed set missing it has a complex point.
Source: closed points of a Jacobson scheme are dense in locally closed subsets;
`pointEquivClosedPoint`. -/
theorem hc9k_exists_complexPoint_closure_diff (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : X.left) (B : Closeds X.left) (hz : z ∉ B) :
    ∃ a : ComplexPoint X, a.underlying ∈ closure ({z} : Set X.left) ∧ a.underlying ∉ B := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hlc : IsLocallyClosed (closure ({z} : Set X.left) ∩ (B : Set X.left)ᶜ) :=
    ⟨(B : Set X.left)ᶜ, closure {z}, B.isClosed.isOpen_compl, isClosed_closure,
      Set.inter_comm _ _⟩
  obtain ⟨y, ⟨hy1, hy2⟩, hyc⟩ := nonempty_inter_closedPoints
    (⟨z, subset_closure rfl, hz⟩ : (closure ({z} : Set X.left) ∩ (B : Set X.left)ᶜ).Nonempty) hlc
  let p := (pointEquivClosedPoint X.hom).symm ⟨y, hyc⟩
  let a : ComplexPoint X := Over.homMk p.1 p.2
  refine ⟨a, ?_⟩
  have hu : a.underlying = y :=
    pointOfClosedPoint_apply X.hom y hyc _
  rw [hu]
  exact ⟨hy1, hy2⟩

/-- The prime intersection has finitely many generic points of irreducible components.
Source: Hartshorne, *Algebraic Geometry*, I, Proposition 1.5. -/
theorem hc9k_components_finite (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left) :
    Set.Finite {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme |
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme} := by
  let J := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace J.subscheme :=
    (quasiCompact_iff_compactSpace J.subschemeι).1 inferInstance
  let : IsNoetherian J.subscheme :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  exact genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- The prime intersection subscheme has the intersection of the two closures as image.
Source: `Scheme.IdealSheafData.support_sup`. -/
theorem hc9k_range_subschemeι (X : Over (Spec ↧ℂ)) (x y : X.left) :
    Set.range (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι =
      closure ({x} : Set X.left) ∩ closure ({y} : Set X.left) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_sup]
  simp only [ccm3_primeIdeal, Closeds.coe_inf, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The closure of a component point in the ambient scheme is the image of its closure.
Source: `Topology.IsClosedEmbedding.closure_image_eq`. -/
theorem hc9k_mem_closure_component (X : Over (Spec ↧ℂ)) (x y : X.left)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (z : X.left) :
    z ∈ closure ({(ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w} :
      Set X.left) ↔
      ∃ b, b ∈ closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∧
        (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι b = z := by
  let ι := (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι
  have he := ι.isClosedEmbedding.closure_image_eq ({w} : Set _)
  rw [Set.image_singleton] at he
  change z ∈ closure {ι w} ↔ _
  rw [he]
  rfl

/-- A component generic point specializing to another component generic point equals it.
Source: maximality of irreducible components and uniqueness of generic points. -/
theorem hc9k_component_eq_of_mem_closure (X : Over (Spec ↧ℂ)) (x y : X.left)
    (w w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (h : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w ∈
      closure ({(ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w'} :
        Set X.left)) : w = w' := by
  obtain ⟨b, hb, hbw⟩ := (hc9k_mem_closure_component X x y w' _).mp h
  have hbw' : b = w :=
    (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι.isClosedEmbedding.injective hbw
  subst hbw'
  have hsub : closure ({b} : Set _) ⊆ closure ({w'} : Set _) :=
    closure_minimal (Set.singleton_subset_iff.mpr hb) isClosed_closure
  have heq : closure ({b} : Set _) = closure ({w'} : Set _) :=
    hsub.antisymm (hw.2 isIrreducible_singleton.closure hsub)
  exact (inseparable_iff_closure_eq.mpr heq).eq

/-- A complex point lies on both prime supports exactly when it lies on the support of a component
of their scheme-theoretic intersection.
Source: generic points of irreducible components. -/
theorem hc9k_mem_support_inf_iff (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left)
    (a : ComplexPoint X) :
    a ∈ cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y ↔
      ∃ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left y).subscheme ∧
        a ∈ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) := by
  let J := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y
  have hr := hc9k_range_subschemeι X x y
  change a.underlying ∈ closure ({x} : Set X.left) ∩ closure ({y} : Set X.left) ↔
    ∃ w : J.subscheme, closure ({w} : Set J.subscheme) ∈ irreducibleComponents J.subscheme ∧
      a.underlying ∈ closure ({J.subschemeι w} : Set X.left)
  constructor
  · intro ha
    rw [← hr] at ha
    obtain ⟨b, hb⟩ := ha
    let C := irreducibleComponent b
    have hC : C ∈ irreducibleComponents J.subscheme :=
      irreducibleComponent_mem_irreducibleComponents b
    let g := hC.1.genericPoint
    have hg : closure ({g} : Set J.subscheme) = C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    refine ⟨g, hg ▸ hC, ?_⟩
    rw [← hb]
    exact (hc9k_mem_closure_component X x y g _).mpr
      ⟨b, hg.symm ▸ mem_irreducibleComponent, rfl⟩
  · rintro ⟨w, -, hw⟩
    have hc : IsClosed (closure ({x} : Set X.left) ∩ closure ({y} : Set X.left)) :=
      isClosed_closure.inter isClosed_closure
    apply hc.closure_subset_iff.mpr ?_ hw
    rw [Set.singleton_subset_iff, ← hr]
    exact ⟨w, rfl⟩

/-- The intersection of two prime supports is the finite union of the component supports.
Source: `hc9k_mem_support_inf_iff`. -/
theorem hc9k_support_inf_eq_iSup (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left)
    [Fintype {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme}] :
    cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y =
      ⨆ c : {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left y).subscheme},
        cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) := by
  ext a
  change a ∈ cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y ↔
    a ∈ ⨆ c : {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left y).subscheme},
        cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1)
  rw [ccm5_mem_finite_iSup, hc9k_mem_support_inf_iff]
  exact ⟨fun ⟨w, hw, ha⟩ => ⟨⟨w, hw⟩, ha⟩, fun ⟨c, ha⟩ => ⟨c.1, c.2, ha⟩⟩

/-- Germs commute with transport along an equality of degrees.
Source: `Eq.rec`. -/
theorem hc9k_supportGerm_cast (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) {m n : ℕ} (e : m = n) (a : ComplexPoint X)
    (u : H_[S]^m(X; ℚ)) :
    ccm5_supportGerm X S n a (e ▸ u) = e ▸ ccm5_supportGerm X S m a u := by
  subst e
  rfl

/-- Pullback commutes with transport along an equality of degrees.
Source: `Eq.rec`. -/
theorem hc9k_relativeCohomologyMap_cast {A B : TopPair.{0}} (f : A ⟶ B) {m n : ℕ}
    (e : m = n) (u : RelativeCohomology ℚ B m) :
    relativeCohomologyMap ℚ n f (e ▸ u) = e ▸ relativeCohomologyMap ℚ m f u := by
  subst e
  rfl

/-- Local germs commute with transport along an equality of degrees.
Source: `Eq.rec`. -/
theorem hc9k_supportRelativeCohomologyGerm_cast (Y : TopCat.{0}) (S : Set Y)
    (U : Opens Y) (a : Y) (ha : a ∈ U) {m n : ℕ} (e : m = n)
    (u : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set Y) S) m) :
    supportRelativeCohomologyGerm Y S n U a ha (e ▸ u) =
      e ▸ supportRelativeCohomologyGerm Y S m U a ha u := by
  subst e
  rfl

/-- Restricting the ambient relative comparison to an open is the neighbourhood restriction.
Source: `ccm16_fullPairIso` and functoriality of relative cohomology. -/
theorem hc9k_supportedComparison_restrict (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X))
    (n : ℕ) (u : H_[S]^n(X; ℚ)) :
    relativeCohomologyMap ℚ n
      (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
        ⟨Subtype.val, continuous_subtype_val⟩ S)
      (ccm16_supportedComparison X S n u) =
    relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
        (⊤ : Opens (ComplexPoint X)) from le_top) (S : Set (ComplexPoint X)))
      (supportedSingularClass X S n u) := by
  change (relativeCohomologyMap ℚ n
    (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
      ⟨Subtype.val, continuous_subtype_val⟩ S)).comp
    (relativeCohomologyMap ℚ n (ccm16_fullPairIso (TopCat.of (ComplexPoint X)) S).hom)
      (supportedSingularClass X S n u) = _
  rw [← relativeCohomologyMap_comp]
  rfl

/-- The relative cup is compatible with the identity maps between equal supports.
Source: `relativeCohomologyMap_id`. -/
theorem hc9k_relativeCup_congr (Y : TopCat.{0}) (S S' T T' : Closeds Y)
    (hS : S = S') (hT : T = T') (p q : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S' : Set Y)ᶜ) p)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (T' : Set Y)ᶜ) q) :
    ccm15_relativeCup Y S T p q
        (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom (A := (S : Set Y)ᶜ) (B := (S' : Set Y)ᶜ) (𝟙 Y)
          (fun _ hz h => hz (hS ▸ h))) u)
        (relativeCohomologyMap ℚ q (TopPair.ofSubsetHom (A := (T : Set Y)ᶜ) (B := (T' : Set Y)ᶜ) (𝟙 Y)
          (fun _ hz h => hz (hT ▸ h))) v) =
      relativeCohomologyMap ℚ (p + q) (TopPair.ofSubsetHom
          (A := ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (B := ((S' ⊓ T' : Closeds Y) : Set Y)ᶜ) (𝟙 Y)
          (fun _ hz h => hz (by rw [hS, hT]; exact h)))
        (ccm15_relativeCup Y S' T' p q u v) := by
  subst hS hT
  have h1 : ∀ (A : Set Y) (hA : ∀ z ∈ A, (𝟙 Y : Y ⟶ Y) z ∈ A),
      TopPair.ofSubsetHom (𝟙 Y) hA = 𝟙 (TopPair.ofSubset A) := by
    intro A hA
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  rw [h1, h1, h1, relativeCohomologyMap_id, relativeCohomologyMap_id, relativeCohomologyMap_id]
  rfl

/-- Two successive pullbacks are the pullback along a given composite.
Source: `relativeCohomologyMap_comp`. -/
theorem hc9k_relativeCohomologyMap_map_of_comp {A B C : TopPair.{0}} (n : ℕ)
    (φ : A ⟶ B) (ψ : B ⟶ C) (χ : A ⟶ C) (hχ : φ ≫ ψ = χ) (z : RelativeCohomology ℚ C n) :
    relativeCohomologyMap ℚ n φ (relativeCohomologyMap ℚ n ψ z) =
      relativeCohomologyMap ℚ n χ z := by
  rw [← hχ, relativeCohomologyMap_comp, LinearMap.comp_apply]

-- Needs definitional unfolding across the supported-class wrappers.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A class supported on a closed set has zero germ, after enlarging the support, off that set.
Source: `neighborhoodSupportRelativeCohomology_subsingleton`. -/
theorem hc9k_supportGerm_enlarge_eq_zero_of_not_mem
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ)
    (a : ComplexPoint X) (ha : a ∉ S)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    ccm5_supportGerm X T n a (supportEnlarge X h n u) = 0 := by
  rw [ccm5_supportGerm_enlarge]
  let W : Opens (ComplexPoint X) := S.compl
  have haW : a ∈ W := ha
  have hW : W ≤ ⊤ := le_top
  rw [← supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (T : Set (ComplexPoint X)) n hW a haW]
  have hcomp :
      neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆
        (⊤ : Opens (ComplexPoint X)) from hW) (T : Set (ComplexPoint X)) ≫
        neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr h) =
      neighborhoodSupportEnlargePairMap (W : Set (ComplexPoint X))
        (SetLike.coe_subset_coe.mpr h) ≫
        neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆
          (⊤ : Opens (ComplexPoint X)) from hW) (S : Set (ComplexPoint X)) := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomp,
    relativeCohomologyMap_comp, LinearMap.comp_apply]
  let := neighborhoodSupportRelativeCohomology_subsingleton
    (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) n W (fun _ hy => hy)
  have hz : relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆
        (⊤ : Opens (ComplexPoint X)) from hW) (S : Set (ComplexPoint X)))
      (supportedSingularClass X S n u) = 0 := Subsingleton.elim _ _
  rw [hz, map_zero]
  simp only [supportRelativeCohomologyGerm, map_zero]

/-- The appended coordinates vanish exactly when both coordinate maps vanish.
Source: `Fin.append_left` and `Fin.append_right`. -/
theorem hc9k_appendCoordinates_eq_zero_iff {Y : Type*} [TopologicalSpace Y] {p q : ℕ}
    (f : C(Y, Fin p → ℂ)) (g : C(Y, Fin q → ℂ)) (u : Y) :
    hc9k_appendCoordinates f g u = 0 ↔ f u = 0 ∧ g u = 0 := by
  constructor
  · intro h0
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun h0 (Fin.castAdd q i)
      exact (Fin.append_left (f u) (g u) i).symm.trans this
    · have := congrFun h0 (Fin.natAdd p i)
      exact (Fin.append_right (f u) (g u) i).symm.trans this
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (Fin.append_left (f u) (g u) j).trans (congrFun h1 j)
    · exact (Fin.append_right (f u) (g u) j).trans (congrFun h2 j)

/-- The head coordinates of the appended map are the first map.
Source: `Fin.append_left`. -/
theorem hc9k_coordinateHead_append {Y : Type*} [TopologicalSpace Y] {p q : ℕ}
    (f : C(Y, Fin p → ℂ)) (g : C(Y, Fin q → ℂ)) (u : Y) :
    hc9k_coordinateHead p q (hc9k_appendCoordinates f g u) = f u :=
  funext fun i => Fin.append_left (f u) (g u) i

/-- The tail coordinates of the appended map are the second map.
Source: `Fin.append_right`. -/
theorem hc9k_coordinateTail_append {Y : Type*} [TopologicalSpace Y] {p q : ℕ}
    (f : C(Y, Fin p → ℂ)) (g : C(Y, Fin q → ℂ)) (u : Y) :
    hc9k_coordinateTail p q (hc9k_appendCoordinates f g u) = g u :=
  funext fun i => Fin.append_right (f u) (g u) i

/-- The pullback of the normalized class along a head chart factors through the head
coordinates of the appended map.
Source: functoriality of relative cohomology; `hc9k_coordinateHead_append`. -/
theorem hc9k_normalCoordinatePair_head (M : Type) [TopologicalSpace M] (U : Opens M) (S : Closeds M) (p q : ℕ)
    (f : C(U, Fin p → ℂ)) (g : C(U, Fin q → ℂ))
    (hf : ∀ u : U, f u = 0 ↔ u.1 ∈ S) :
    relativeCohomologyMap ℚ (2 * p) (hc9k_normalCoordinatePair U S p f (fun u => (hf u).mp))
        (normalizedPointCoclass p) =
      relativeCohomologyMap ℚ (2 * p)
        (TopPair.ofSubsetHom (X := TopCat.of U) (Y := TopCat.of U)
          (A := ((S.preimage (continuous_subtype_val (p := fun z => z ∈ U)) : Closeds U) : Set U)ᶜ)
          (B := (((ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p
            (hc9k_coordinateHead p q)).preimage (hc9k_appendCoordinates f g).continuous :
              Closeds U) : Set U)ᶜ) (𝟙 _)
          (fun u hu h0 => hu ((hf u).mp ((hc9k_coordinateHead_append f g u).symm.trans h0))))
        (relativeCohomologyMap ℚ (2 * p)
          (ccm17_preimagePair (TopCat.of U) (TopCat.of (Fin (p + q) → ℂ))
            (hc9k_appendCoordinates f g) (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p
              (hc9k_coordinateHead p q)))
          (ccm17_normalClass (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q))) := by
  rw [ccm17_normalClass, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  refine congrArg (fun φ => relativeCohomologyMap ℚ (2 * p) φ (normalizedPointCoclass p)) ?_
  apply MorphismProperty.Arrow.Hom.ext
  · ext u
    exact Subtype.ext (hc9k_coordinateHead_append f g u.1).symm
  · ext u
    exact (hc9k_coordinateHead_append f g u).symm

/-- The pullback of the normalized class along a tail chart factors through the tail
coordinates of the appended map.
Source: functoriality of relative cohomology; `hc9k_coordinateTail_append`. -/
theorem hc9k_normalCoordinatePair_tail (M : Type) [TopologicalSpace M] (U : Opens M) (S : Closeds M) (p q : ℕ)
    (f : C(U, Fin p → ℂ)) (g : C(U, Fin q → ℂ))
    (hf : ∀ u : U, g u = 0 ↔ u.1 ∈ S) :
    relativeCohomologyMap ℚ (2 * q) (hc9k_normalCoordinatePair U S q g (fun u => (hf u).mp))
        (normalizedPointCoclass q) =
      relativeCohomologyMap ℚ (2 * q)
        (TopPair.ofSubsetHom (X := TopCat.of U) (Y := TopCat.of U)
          (A := ((S.preimage (continuous_subtype_val (p := fun z => z ∈ U)) : Closeds U) : Set U)ᶜ)
          (B := (((ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q
            (hc9k_coordinateTail p q)).preimage (hc9k_appendCoordinates f g).continuous :
              Closeds U) : Set U)ᶜ) (𝟙 _)
          (fun u hu h0 => hu ((hf u).mp ((hc9k_coordinateTail_append f g u).symm.trans h0))))
        (relativeCohomologyMap ℚ (2 * q)
          (ccm17_preimagePair (TopCat.of U) (TopCat.of (Fin (p + q) → ℂ))
            (hc9k_appendCoordinates f g) (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q
              (hc9k_coordinateTail p q)))
          (ccm17_normalClass (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q))) := by
  rw [ccm17_normalClass, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  refine congrArg (fun φ => relativeCohomologyMap ℚ (2 * q) φ (normalizedPointCoclass q)) ?_
  apply MorphismProperty.Arrow.Hom.ext
  · ext u
    exact Subtype.ext (hc9k_coordinateTail_append f g u.1).symm
  · ext u
    exact (hc9k_coordinateTail_append f g u).symm

/-- The analytic singular locus of a prime lies in its analytic support.
Source: `range_cycleComponentι`. -/
theorem hc9k_singular_le_support (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : X.left) :
    cycleComponentSingularAnalyticClosedFiltration X z 0 ≤ cycleComponentAnalyticClosedSupport X z := by
  intro a ha
  change a.underlying ∈ closure ({z} : Set X.left)
  rw [← range_cycleComponentι X.left z]
  obtain ⟨b, _, hb⟩ := ha
  exact ⟨b, hb⟩

/-- A point on no other component and off the singular locus of its own component lies off the
component boundary.
Source: `ccm5_componentBoundary`. -/
theorem hc9k_mem_componentBoundary_compl
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (I : Type*) [Fintype I] [DecidableEq I] (xs : I → X.left) (c : I) (a : ComplexPoint X)
    (hother : ∀ c', c' ≠ c → a ∉ cycleComponentAnalyticClosedSupport X (xs c'))
    (hsing : a ∉ cycleComponentSingularAnalyticClosedFiltration X (xs c) 0) :
    a ∈ (ccm5_componentBoundary X (Fintype.card I) (xs ∘ (Fintype.equivFin I).symm)).compl := by
  classical
  intro hm
  simp only [ccm5_componentBoundary, Closeds.coe_sup, Set.mem_union] at hm
  rcases hm with h1 | h2
  · obtain ⟨i, hi⟩ := (ccm5_mem_finite_iSup _ _).mp h1
    by_cases he : (Fintype.equivFin I).symm i = c
    · exact hsing (by simpa only [Function.comp_apply, he] using hi)
    · exact hother _ he (hc9k_singular_le_support X _ hi)
  · obtain ⟨i, hi⟩ := (ccm5_mem_finite_iSup _ _).mp h2
    obtain ⟨j, hj⟩ := (ccm5_mem_finite_iSup _ _).mp hi
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte] at hj
      exact hj
    · simp only [hij, ↓reduceIte] at hj
      by_cases he : (Fintype.equivFin I).symm i = c
      · have hne : (Fintype.equivFin I).symm j ≠ c := fun h' =>
          hij ((Fintype.equivFin I).symm.injective (he.trans h'.symm))
        exact hother _ hne hj.2
      · exact hother _ he hj.1

/-- Every intersection component has a complex point on no other component and off the singular
loci of the component and of both primes.
Source: generic smoothness of the component and `hc9k_exists_complexPoint_closure_diff`. -/
theorem hc9k_exists_component_point
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x y : X.left)
    (hregular : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∧
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X y 0 : Set X.left))
    (c : {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme})
    [Fintype {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme}] :
    ∃ a : ComplexPoint X, a ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) ∧
      (∀ c' : {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme},
        c' ≠ c → a ∉ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c'.1)) ∧
      a ∉ cycleComponentSingularAnalyticClosedFiltration X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) 0 ∧
      a ∉ cycleComponentSingularAnalyticClosedFiltration X x 0 ∧
      a ∉ cycleComponentSingularAnalyticClosedFiltration X y 0 := by
  classical
  let J := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y
  let B : Closeds X.left :=
    (⨆ c' : {w : J.subscheme // closure ({w} : Set J.subscheme) ∈
        irreducibleComponents J.subscheme},
      if c' = c then ⊥ else ⟨closure {J.subschemeι c'.1}, isClosed_closure⟩) ⊔
    cycleComponentSingularAmbientClosedFiltration X (J.subschemeι c.1) 0 ⊔
    cycleComponentSingularAmbientClosedFiltration X x 0 ⊔
    cycleComponentSingularAmbientClosedFiltration X y 0
  have hB : J.subschemeι c.1 ∉ B := by
    intro hm
    simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union] at hm
    rcases hm with ((h1 | h2) | h3) | h4
    · obtain ⟨c', hc'⟩ := (ccm5_mem_finite_iSup _ _).mp h1
      by_cases he : c' = c
      · simp only [he, ↓reduceIte] at hc'
        exact hc'
      · simp only [he, ↓reduceIte] at hc'
        exact he (Subtype.ext (hc9k_component_eq_of_mem_closure X x y c.1 c'.1 c.2 hc')).symm
    · exact ccm5_generic_not_mem_singularBoundary X _ h2
    · exact (hregular c.1 c.2).1 h3
    · exact (hregular c.1 c.2).2 h4
  obtain ⟨a, ha1, ha2⟩ := hc9k_exists_complexPoint_closure_diff X _ B hB
  refine ⟨a, ha1, fun c' hc' hm => ha2 ?_, fun hm => ha2 ?_, fun hm => ha2 ?_,
    fun hm => ha2 ?_⟩
  · simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
    refine Or.inl (Or.inl (Or.inl ((ccm5_mem_finite_iSup _ _).mpr ⟨c', ?_⟩)))
    simp only [hc', ↓reduceIte]
    exact hm
  · simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
    exact Or.inl (Or.inl (Or.inr hm))
  · simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
    exact Or.inl (Or.inr hm)
  · simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
    exact Or.inr hm

end HodgeLean.Adapters
