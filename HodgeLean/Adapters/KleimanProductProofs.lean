import HodgeLean.Adapters.KleimanProductDefs
import HodgeLean.Adapters.KleimanProductSubmersion
import HodgeLean.Adapters.KleimanProductGerms
import HodgeLean.Adapters.KleimanProductCoordinate
import HodgeLean.Adapters.CycleClassDivisorLocalTransport
import HodgeLean.Papers.PapersWeilCupDefs

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.RealDefs
open scoped ContDiff Manifold

namespace HodgeLean.Adapters

theorem hc9k_prime_supportedClass_chart_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (x : X.left) (hx : Order.coheight x = p)
    (U : Opens (ComplexPoint X)) (f : C(U, Fin p → ℂ))
    (hzero : ∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x)
    (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hsub : ∀ u : U, f u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u)) :
    relativeCohomologyMap ℚ (2 * p)
        (neighborhoodSupportInclusionPairMap
          (show (U : Set (ComplexPoint X)) ⊆ (⊤ : Opens (ComplexPoint X)) from le_top)
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
        (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) (2 * p)
          (cycleComponentSupportedInjectiveClass X x hx)) =
      relativeCohomologyMap ℚ (2 * p)
        (hc9k_normalCoordinatePair U (cycleComponentAnalyticClosedSupport X x) p f
          (fun u => (hzero u).mp))
        (normalizedPointCoclass p) :=
  hc9k_prime_supportedClass_chart_of_charts X d p x hx U f hzero hhol hsub

set_option linter.unusedVariables false in
theorem hc9k_intersection_supportedClass_chart_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ℕ) (x y : X.left)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme)
    (hwcodim : Order.coheight ((ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subschemeι w) = p + q)
    (U : Opens (ComplexPoint X))
    (f : C(U, Fin p → ℂ))
    (hfzero : ∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x)
    (hfhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hfsub : ∀ u : U, f u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u))
    (h : C(U, Fin q → ℂ))
    (hhzero : ∀ u : U, h u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X y)
    (hhhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h)
    (hhsub : ∀ u : U, h u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u))
    (hzero : ∀ u : U, hc9k_appendCoordinates f h u = 0 ↔
      u.1 ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
    (hsub : ∀ u : U, hc9k_appendCoordinates f h u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ)
        (hc9k_appendCoordinates f h) u)) :
    relativeCohomologyMap ℚ (2 * (p + q))
        (neighborhoodSupportInclusionPairMap
          (show (U : Set (ComplexPoint X)) ⊆ (⊤ : Opens (ComplexPoint X)) from le_top)
          (cycleComponentAnalyticClosedSupport X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) :
              Set (ComplexPoint X)))
        (supportedSingularClass X
          (cycleComponentAnalyticClosedSupport X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
          (2 * (p + q))
          (cycleComponentSupportedInjectiveClass X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)
            hwcodim)) =
      relativeCohomologyMap ℚ (2 * (p + q))
        (hc9k_normalCoordinatePair U
          (cycleComponentAnalyticClosedSupport X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
          (p + q) (hc9k_appendCoordinates f h) (fun u => (hzero u).mp))
        (normalizedPointCoclass (p + q)) := by
  have hloc := hc9k_weighted_chart_eq_of_local X (p + q) _ hwcodim U 1 _ fun a haU haS haB => by
    simpa only [one_smul] using hc9k_chart_local_of_submersion X d (p + q) _ hwcodim U
      (hc9k_appendCoordinates f h) hzero (hc9k_appendCoordinates_contMDiff f h hfhol hhhol)
      a haU haS haB (hsub ⟨a, haU⟩ ((hzero ⟨a, haU⟩).mpr haS))
  simpa only [one_smul] using hloc

theorem hc9k_exists_transverse_chart_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme)
    (a : ComplexPoint X)
    (ha : a ∈ cycleComponentAnalyticClosedSupport X
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
    (hax : a ∉ cycleComponentSingularAnalyticClosedFiltration X x 0)
    (hay : a ∉ cycleComponentSingularAnalyticClosedFiltration X y 0)
    (hunique : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      a ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w') → w' = w) :
    ∃ (U : Opens (ComplexPoint X)) (_ : a ∈ U) (f : C(U, Fin p → ℂ)) (h : C(U, Fin q → ℂ)),
      (∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x) ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f ∧
      (∀ u : U, f u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u)) ∧
      (∀ u : U, h u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X y) ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h ∧
      (∀ u : U, h u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u)) ∧
      (∀ u : U, hc9k_appendCoordinates f h u = 0 ↔
        u.1 ∈ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)) :=
  hc9k_exists_transverse_chart_of_charts X d p q x y hx hy w hw a ha hax hay hunique

theorem hc9k_transverse_chart_submersion_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (t : ComplexPoint X) (ht : t ∈ hc9k_transverseLocus X x y)
    (w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme)
    (U : Opens (ComplexPoint X))
    (f : C(U, Fin p → ℂ))
    (hfzero : ∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x)
    (hfhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hfsub : ∀ u : U, f u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u))
    (h : C(U, Fin q → ℂ))
    (hhzero : ∀ u : U,
      h u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X (hc9k_translatePoint X t y))
    (hhhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h)
    (hhsub : ∀ u : U, h u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u))
    (hzero : ∀ u : U, hc9k_appendCoordinates f h u = 0 ↔
      u.1 ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w))
    (a : U) (ha : hc9k_appendCoordinates f h a = 0)
    (hax : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X x 0)
    (hay : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X
      (hc9k_translatePoint X t y) 0)
    (haw : a.1 ∉ cycleComponentSingularAnalyticClosedFiltration X
      ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) 0) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ)
      (hc9k_appendCoordinates f h) a) :=
  hc9k_transverse_chart_submersion_of_charts X d p q x y hx hy t ht w hw U f hfzero hfhol hfsub
    h hhzero hhhol hhsub hzero a ha hax hay haw

-- Germ maps unfold through `supportH` instances, which needs defeq past instance transparency.
set_option backward.isDefEq.respectTransparency false in
theorem hc9k_supportedClass_eq_of_generic_germs_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (I : Type*) [Fintype I] (p : ℕ) (x : I → X.left)
    (hx : ∀ i, Order.coheight (x i) = p)
    (S : Closeds (ComplexPoint X))
    (hS : S = ⨆ i, cycleComponentAnalyticClosedSupport X (x i))
    (n : ℕ) (hn : n = 2 * p) (a : I → ComplexPoint X)
    (haS : ∀ i, a i ∈ cycleComponentAnalyticClosedSupport X (x i))
    (haB : ∀ i, a i ∈ (ccm5_componentBoundary X (Fintype.card I)
      (x ∘ (Fintype.equivFin I).symm)).compl)
    (u v : H_[S]^n(X; ℚ))
    (h : ∀ i, ccm5_supportGerm X S n (a i) u = ccm5_supportGerm X S n (a i) v) :
    u = v := by
  classical
  let r := Fintype.card I
  let eqv := Fintype.equivFin I
  let y : Fin r → X.left := x ∘ eqv.symm
  have hyc : ∀ j, Order.coheight (y j) = p := fun j => hx _
  have hyinj : Function.Injective y := by
    intro j k hjk
    by_contra hne
    apply haB (eqv.symm j)
    apply (hc9k_mem_componentBoundary X r y _).mpr
    refine Or.inr ⟨j, k, hne, haS (eqv.symm j), ?_⟩
    rw [← hjk]
    exact haS (eqv.symm j)
  have hsup : S = ⨆ j, cycleComponentAnalyticClosedSupport X (y j) :=
    hS.trans (eqv.symm.iSup_comp (g := fun i => cycleComponentAnalyticClosedSupport X (x i))).symm
  clear hS
  subst hn hsup
  apply hc9k_componentUnion_goodOpen_germs_injective X r p y hyinj hyc u v
  intro b hb
  have hw : ∀ i, ccm5_supportGerm X (⨆ j, cycleComponentAnalyticClosedSupport X (y j)) (2 * p)
      (a i) (u - v) = 0 := fun i => by rw [map_sub, h i, sub_self]
  have key : ccm5_supportGerm X (⨆ j, cycleComponentAnalyticClosedSupport X (y j)) (2 * p)
      b (u - v) = 0 := by
    by_cases hbS : b ∈ (⨆ j, cycleComponentAnalyticClosedSupport X (y j))
    · obtain ⟨j, hj⟩ := (ccm5_mem_finiteClosedSup _ b).mp hbS
      have haB' : a (eqv.symm j) ∈ (ccm5_componentBoundary X r y).compl := haB _
      have haS' : a (eqv.symm j) ∈ cycleComponentAnalyticClosedSupport X (y j) := haS _
      exact hc9k_componentUnion_germ_zero_on_piece X r p y hyc (u - v) j (a (eqv.symm j)) b
        haB' haS' (hw _) hb hj
    · exact supportRelativeCohomologyGerm_eq_zero_of_not_mem (TopCat.of (ComplexPoint X))
        ((⨆ j, cycleComponentAnalyticClosedSupport X (y j) : Closeds (ComplexPoint X)) :
          Set (ComplexPoint X)) (2 * p) (Closeds.isClosed _) ⊤ b trivial hbS _
  exact sub_eq_zero.mp ((map_sub (ccm5_supportGerm X
    (⨆ j, cycleComponentAnalyticClosedSupport X (y j)) (2 * p) b) u v).symm.trans key)

theorem hc9k_coordinate_product_general_aux (p q : ℕ) :
    ccm15_relativeCup (TopCat.of (Fin (p + q) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q))
      (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q))
      (2 * p) (2 * q)
      (ccm17_normalClass (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q))
      (ccm17_normalClass (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q)) =
    hc9k_coordinateIntersectionClass p q :=
  hc9kc_coordinate_product p q


open scoped TensorProduct in
private theorem hc9k_flat_unramified_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] :
    _root_.IsReduced A := by
  let K := FractionRing R
  have : _root_.IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

private theorem hc9k_smooth_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] : _root_.IsReduced A := by
  constructor
  intro u hu
  apply eq_zero_of_localization u
  intro p hp
  let := hp
  obtain ⟨g, hg, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let := hAlg
  let := hTower
  let := hEtale
  have : _root_.IsReduced (Localization.Away g) :=
    hc9k_flat_unramified_reduced_domain (MvPolynomial (Fin n) R) _
  have hz := (hu.map (algebraMap A (Localization.Away g))).eq_zero
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g)
    (Localization.Away g) u).mp hz
  obtain ⟨k, hk⟩ := m.property
  apply (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) u).mpr
  refine ⟨⟨m, ?_⟩, hm⟩
  change (m : A) ∉ p
  rw [← hk]
  exact p.primeCompl.pow_mem hg k

private theorem hc9k_smooth_reduced_integral {X Y : Scheme} (f : X ⟶ Y)
    [IsIntegral Y] [Smooth f] : AlgebraicGeometry.IsReduced X := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, _⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty U := ⟨⟨f x, e hxV⟩⟩
  algebraize [(f.appLE U V e).hom]
  have : Algebra.Smooth Γ(Y, U) Γ(X, V) := by
    rw [← RingHom.smooth_algebraMap]
    exact f.smooth_appLE hU hV e
  have : _root_.IsReduced Γ(X, V) := hc9k_smooth_reduced_domain Γ(Y, U) Γ(X, V)
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) inferInstance

theorem hc9k_transverse_generic_length_one_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left) (t : ComplexPoint X)
    (ht : t ∈ hc9k_transverseLocus X x y)
    (w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme)
    (hx : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
        (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left))
    (hy : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
        (cycleComponentSingularAmbientClosedFiltration X (hc9k_translatePoint X t y) 0 :
          Set X.left)) :
    ccm11_intersectionLength X.left (ccm3_primeIdeal X.left x)
      (ccm3_primeIdeal X.left (hc9k_translatePoint X t y)) w = 1 := by
  have hsmooth := ht.2 w hx hy
  let g := (ccm3_primeIdeal X.left x ⊔
    ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι ≫ X.hom
  let U := g.smoothLocus
  have : Smooth (U.ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact top_le_iff.mp fun u _ ↦ u.2
  have : IsReduced (U : Scheme) := hc9k_smooth_reduced_integral (U.ι ≫ g)
  let w' : (U : Scheme) := ⟨w, hsmooth⟩
  have hw' : closure ({w'} : Set (U : Scheme)) ∈ irreducibleComponents (U : Scheme) := by
    rw [U.ι.isOpenEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents hw U.ι.isOpenEmbedding
      ⟨U.ι w', subset_closure (Set.mem_singleton _), _, rfl⟩
  have hfield := (asIso (U.ι.stalkMap w')).commRingCatIsoToRingEquiv.isField
    (isField_stalk_of_closure_mem_irreducibleComponents (U : Scheme) w' hw')
  change IsField ((ccm3_primeIdeal X.left x ⊔
    ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme.presheaf.stalk w) at hfield
  let := hfield.toField
  exact Module.length_eq_one _ _

theorem hc9k_supported_intersection_product_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (h : 2 * p + 2 * q = 2 * (p + q)) (x y : X.left)
    (hx : Order.coheight x = p) (hy : Order.coheight y = q) (t : ComplexPoint X)
    (ht : t ∈ hc9k_transverseLocus X x y)
    (hregular : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∧
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X
            (hc9k_translatePoint X t y) 0 : Set X.left))
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) = p + q)
    (hsupport : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
      cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) ≤
        cycleComponentAnalyticClosedSupport X x ⊓
          cycleComponentAnalyticClosedSupport X (hc9k_translatePoint X t y)) :
    ccm16_supportedCup X (cycleComponentAnalyticClosedSupport X x)
        (cycleComponentAnalyticClosedSupport X (hc9k_translatePoint X t y)) (2 * p) (2 * q)
        (cycleComponentSupportedInjectiveClass X x hx)
        (cycleComponentSupportedInjectiveClass X (hc9k_translatePoint X t y)
          ((hc9k_translate_coheight X t y).trans hy)) =
      h.symm ▸ hc9k_supportedIntersectionClass X p q x (hc9k_translatePoint X t y)
        hcodim hsupport := by
  set_option backward.isDefEq.respectTransparency false in
  · classical
    set y' := hc9k_translatePoint X t y with hy'def
    have hy' : Order.coheight y' = q := (hc9k_translate_coheight X t y).trans hy
    let : Fintype {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subscheme} :=
      (hc9k_components_finite X x y').fintype
    choose a haS hother hsing hax hay using
      fun c => hc9k_exists_component_point X x y' hregular c
    refine hc9k_supportedClass_eq_of_generic_germs_aux X
      {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subscheme}
      (p + q)
      (fun c => (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subschemeι c.1)
      (fun c => hcodim c.1 c.2) _ (hc9k_support_inf_eq_iSup X x y') (2 * p + 2 * q)
      (show 2 * p + 2 * q = 2 * (p + q) by omega) a
      haS (fun c => hc9k_mem_componentBoundary_compl X _ _ c (a c) (hother c) (hsing c)) _ _ ?_
    intro c
    have hother' : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subscheme,
        closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y').subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left y').subscheme → w' ≠ c.1 →
        a c ∉ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subschemeι w') :=
      fun w' hw' hne => hother c ⟨w', hw'⟩ (fun he => hne (congrArg Subtype.val he))
    let B : Opens (ComplexPoint X) :=
      (cycleComponentSingularAnalyticClosedFiltration X x 0 ⊔
        cycleComponentSingularAnalyticClosedFiltration X y' 0 ⊔
        cycleComponentSingularAnalyticClosedFiltration X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subschemeι c.1) 0).compl
    have haB : a c ∈ B := by
      rintro ((h1 | h2) | h3)
      exacts [hax c h1, hay c h2, hsing c h3]
    obtain ⟨U, haU, hUB, f, g, hfzero, hfhol, hfsub, hgzero, hghol, hgsub, hzero⟩ :=
      hc9k_exists_transverse_chart_in X (dim X.left) p q x y' hx hy' c.1 c.2 (a c) (haS c)
        (hax c) (hay c) (fun w' hw' hm => by
          by_contra hne
          exact hother' w' hw' hne hm) B haB
    have hpair : ∀ u : U, hc9k_appendCoordinates f g u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (p + q) → ℂ)
          (hc9k_appendCoordinates f g) u) := fun u hu => by
      have huB : u.1 ∈ B := hUB u.2
      exact hc9k_transverse_chart_submersion_aux X (dim X.left) p q x y hx hy t ht c.1 c.2 U
        f hfzero hfhol hfsub g hgzero hghol hgsub hzero u hu
        (fun h1 => huB (Or.inl (Or.inl h1))) (fun h2 => huB (Or.inl (Or.inr h2)))
        (fun h3 => huB (Or.inr h3))
    have hlen : ((ccm11_intersectionLength X.left (ccm3_primeIdeal X.left x)
        (ccm3_primeIdeal X.left y') c.1).toNat : ℚ) = 1 := by
      rw [hc9k_transverse_generic_length_one_aux X x y t ht c.1 c.2 (hregular c.1 c.2).1
        (hregular c.1 c.2).2]
      rfl
    have hR :
        ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
            cycleComponentAnalyticClosedSupport X y') (2 * (p + q)) (a c)
          (hc9k_supportedIntersectionClass X p q x y' hcodim hsupport) =
          supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y' : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU
            (relativeCohomologyMap ℚ (2 * (p + q))
              (hc9k_normalCoordinatePair U (cycleComponentAnalyticClosedSupport X x ⊓
                cycleComponentAnalyticClosedSupport X y') (p + q) (hc9k_appendCoordinates f g)
                (fun u hu => ⟨(hfzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).1,
                  (hgzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).2⟩))
              (normalizedPointCoclass (p + q))) := by
      have hfin := hc9k_components_finite X x y'
      unfold hc9k_supportedIntersectionClass
      rw [map_finsum _ (hfin.subset fun w' hw' => by
        by_contra hn
        exact hw' (dite_eq_right_iff.mpr fun h => absurd h hn))]
      rw [finsum_eq_single _ c.1 (fun w' hw' => by
        by_cases hc : closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y').subscheme) ∈
              irreducibleComponents (ccm3_primeIdeal X.left x ⊔
                ccm3_primeIdeal X.left y').subscheme
        · rw [dite_eq_left_of_eq_true (eq_true hc), Nat.cast_smul_eq_nsmul ℚ, map_nsmul,
            hc9k_supportGerm_enlarge_eq_zero_of_not_mem X _ _ (a c) (hother' w' hc hw'), nsmul_zero]
        · rw [dite_eq_right_of_eq_false (eq_false hc), map_zero])]
      rw [dite_eq_left_of_eq_true (eq_true c.2), Nat.cast_smul_eq_nsmul ℚ, map_nsmul, ccm5_supportGerm_enlarge,
        ← supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X)) _ _
          (le_top : U ≤ ⊤) (a c) haU]
      have hloc := hc9k_relativeCohomologyMap_map_of_comp (2 * (p + q))
        (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
          (⊤ : Opens (ComplexPoint X)) from le_top)
          ((cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y' :
            Closeds (ComplexPoint X)) : Set (ComplexPoint X)))
        (neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr (hsupport c.1 c.2)))
        (neighborhoodSupportEnlargePairMap (U : Set (ComplexPoint X))
          (SetLike.coe_subset_coe.mpr (hsupport c.1 c.2)) ≫
          neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
            (⊤ : Opens (ComplexPoint X)) from le_top)
            (cycleComponentAnalyticClosedSupport X
              ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subschemeι c.1) :
                Set (ComplexPoint X)))
        (by apply MorphismProperty.Arrow.Hom.ext <;> rfl)
      rw [hloc, ← hc9k_relativeCohomologyMap_map_of_comp (2 * (p + q))
        (neighborhoodSupportEnlargePairMap (U : Set (ComplexPoint X))
          (SetLike.coe_subset_coe.mpr (hsupport c.1 c.2)))
        (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
            (⊤ : Opens (ComplexPoint X)) from le_top)
            (cycleComponentAnalyticClosedSupport X
              ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y').subschemeι c.1) :
                Set (ComplexPoint X))) _ rfl]
      have hsmul : ∀ (k : ℕ) (z : RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (U : Set (ComplexPoint X))
          ((cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y' :
            Closeds (ComplexPoint X)) : Set (ComplexPoint X))) (2 * (p + q))),
          k • supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y' : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU z =
          supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y' : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU (k • z) := by
        intro k z
        simp only [supportRelativeCohomologyGerm, map_nsmul]
      rw [hsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, hlen, one_smul,
        hc9k_intersection_supportedClass_chart_aux X (dim X.left) p q x y' c.1 c.2 (hcodim c.1 c.2) U
          f hfzero hfhol hfsub g hgzero hghol hgsub hzero hpair,
        hc9k_relativeCohomologyMap_map_of_comp _ _ _ _ rfl]
      congr 2
    have hL :
        ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
            cycleComponentAnalyticClosedSupport X y') (2 * p + 2 * q) (a c)
          (ccm16_supportedCup X (cycleComponentAnalyticClosedSupport X x)
            (cycleComponentAnalyticClosedSupport X y') (2 * p) (2 * q)
            (cycleComponentSupportedInjectiveClass X x hx)
            (cycleComponentSupportedInjectiveClass X y' hy')) =
          h.symm ▸ supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
            ((cycleComponentAnalyticClosedSupport X x ⊓
              cycleComponentAnalyticClosedSupport X y' : Closeds (ComplexPoint X)) :
                Set (ComplexPoint X)) (2 * (p + q)) U (a c) haU
            (relativeCohomologyMap ℚ (2 * (p + q))
              (hc9k_normalCoordinatePair U (cycleComponentAnalyticClosedSupport X x ⊓
                cycleComponentAnalyticClosedSupport X y') (p + q) (hc9k_appendCoordinates f g)
                (fun u hu => ⟨(hfzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).1,
                  (hgzero u).mp ((hc9k_appendCoordinates_eq_zero_iff f g u).mp hu).2⟩))
              (normalizedPointCoclass (p + q))) := by
      rw [ccm17_supportedCup_germ X _ _ U (2 * p) (2 * q) (a c) haU,
        hc9k_supportedComparison_restrict, hc9k_supportedComparison_restrict,
        hc9k_prime_supportedClass_chart_aux X (dim X.left) p x hx U f hfzero hfhol hfsub,
        hc9k_prime_supportedClass_chart_aux X (dim X.left) q y' hy' U g hgzero hghol hgsub,
        hc9k_normalCoordinatePair_head _ U _ p q f g hfzero, hc9k_normalCoordinatePair_tail _ U _ p q f g hgzero]
      have hSx : (cycleComponentAnalyticClosedSupport X x).preimage
          (continuous_subtype_val (p := fun z => z ∈ U)) =
          (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p
            (hc9k_coordinateHead p q)).preimage (hc9k_appendCoordinates f g).continuous := by
        ext u
        change u.1 ∈ cycleComponentAnalyticClosedSupport X x ↔
          hc9k_coordinateHead p q (hc9k_appendCoordinates f g u) = 0
        rw [hc9k_coordinateHead_append, hfzero]
      have hSy : (cycleComponentAnalyticClosedSupport X y').preimage
          (continuous_subtype_val (p := fun z => z ∈ U)) =
          (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q
            (hc9k_coordinateTail p q)).preimage (hc9k_appendCoordinates f g).continuous := by
        ext u
        change u.1 ∈ cycleComponentAnalyticClosedSupport X y' ↔
          hc9k_coordinateTail p q (hc9k_appendCoordinates f g u) = 0
        rw [hc9k_coordinateTail_append, hgzero]
      rw [hc9k_relativeCup_congr (TopCat.of U) _ _ _ _ hSx hSy,
        ← ccm17_relativeCup_pullback, hc9k_coordinate_product_general_aux,
        hc9k_coordinateIntersectionClass, hc9k_relativeCohomologyMap_cast,
        hc9k_relativeCohomologyMap_cast, hc9k_supportRelativeCohomologyGerm_cast]
      congr 2
      rw [hc9k_relativeCohomologyMap_map_of_comp _ _ _ _ rfl]
      apply hc9k_relativeCohomologyMap_map_of_comp
      apply MorphismProperty.Arrow.Hom.ext <;> rfl
    rw [hL, hc9k_supportGerm_cast X _ h.symm, hR]

/-- The cycle class of a single prime cycle in the matching codimension.
Source: the definition of `ccm3_cycleClass`. -/
private theorem hc9k_cycleClass_single (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [DecidableEq X.left]
    (n : ℕ) (z : X.left) (hz : Order.coheight z = n) (a : ℚ) :
    ccm3_cycleClass X n (Function.locallyFinsuppWithin.single z a) =
      a • cycleComponentSheafClass X z hz := by
  unfold ccm3_cycleClass
  change (∑ᶠ w : {w : X.left // Order.coheight w = n},
    (Function.locallyFinsuppWithin.single z a : AlgebraicCycle X.left ℚ) w.1 •
      (cycleComponentSheafClass X w.1 w.2 : HQ X (2 * n))) = _
  rw [finsum_eq_single _ ⟨z, hz⟩ (fun w hw ↦ by
    rw [Function.locallyFinsuppWithin.single_apply, if_neg (fun h ↦ hw (Subtype.ext h)),
      zero_smul])]
  rw [Function.locallyFinsuppWithin.single_apply, if_pos rfl]

/-- The cycle class as an additive map.
Source: `ccm6_cycleClass_linear`. -/
private def hc9k_cycleClassHom (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    AlgebraicCycle X.left ℚ →+ HQ X (2 * n) where
  toFun := ccm3_cycleClass X n
  map_zero' := by
    have h := (ccm6_cycleClass_linear X n 0 0 0).2
    rw [zero_smul] at h
    rw [← h]
    congr 1
    apply Function.locallyFinsuppWithin.ext
    intro z
    simp only [Function.locallyFinsuppWithin.mapRange_apply, zero_mul]
    rfl
  map_add' c d := (ccm6_cycleClass_linear X n 0 c d).1

/-- Every point of the intersection subscheme lies on both analytic supports.
Source: Fulton, *Intersection Theory*, second edition, §1.5. -/
private theorem hc9k_intersection_support_le
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x y : X.left) (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) :
    cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) ≤
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y := by
  have hmem : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w ∈
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).support : Set X.left) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [Scheme.IdealSheafData.support_sup] at hmem
  obtain ⟨hx, hy⟩ := hmem
  change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({x} : Set X.left), isClosed_closure⟩).support : Set X.left) at hx
  change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({y} : Set X.left), isClosed_closure⟩).support : Set X.left) at hy
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hx hy
  intro a ha
  change Point.underlying a ∈ closure ({_} : Set X.left) at ha
  constructor
  · change Point.underlying a ∈ closure ({x} : Set X.left)
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure ha
  · change Point.underlying a ∈ closure ({y} : Set X.left)
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure ha

set_option maxRecDepth 4096 in
/-- Transport of a supported identity along the degree equation.
Source: substitution of the degree equation. -/
private theorem hc9k_cup_forget_cast
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) {i j k : ℕ} (h : i + j = k) (a : HQ X i) (b : HQ X j)
    (u : H_[S]^(i + j)(X; ℚ)) (v : H_[S]^k(X; ℚ)) (huv : u = h.symm ▸ v)
    (hab : (HQ.linearEquiv X (i + j)).symm (forgetSupport ℚ X S (i + j) u) =
      (cupProductOf X).cup rfl a b) :
    (cupProductOf X).cup h a b = (HQ.linearEquiv X k).symm (forgetSupport ℚ X S k v) := by
  subst h huv
  exact hab.symm

theorem hc9k_forget_supported_intersectionCycle_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (x y : X.left)
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w) = p + q)
    (hsupport : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) ≤
        cycleComponentAnalyticClosedSupport X x ⊓
          cycleComponentAnalyticClosedSupport X y) :
    (HQ.linearEquiv X (2 * (p + q))).symm
        (forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x ⊓
          cycleComponentAnalyticClosedSupport X y) (2 * (p + q))
          (hc9k_supportedIntersectionClass X p q x y hcodim hsupport)) =
      ccm3_cycleClass X (p + q) (hc9k_primeIntersectionCycle X x y) := by
  classical
  let := ccm12_isNoetherian X
  have hS := ccm11_intersection_components_finite X.left (ccm3_primeIdeal X.left x)
    (ccm3_primeIdeal X.left y)
  set s := hS.toFinset
  unfold hc9k_supportedIntersectionClass hc9k_primeIntersectionCycle ccm11_intersectionCycle
  rw [finsum_eq_sum_of_support_subset (s := s), finsum_eq_sum_of_support_subset (s := s)]
  · change forgetSupport ℚ X _ _ (∑ w ∈ s, _) = hc9k_cycleClassHom X (p + q) (∑ w ∈ s, _)
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈ irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme
    · rw [dif_pos hw, if_pos hw, map_rat_smul, ← forgetSupport_restrict]
      exact (hc9k_cycleClass_single X (p + q) _ (hcodim w hw) _).symm
    · simp only [dif_neg hw, if_neg hw, map_zero]
      rfl
  · intro w hw
    by_contra hws
    apply hw
    have hnot : ¬ closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈ irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme :=
      fun h ↦ hws (hS.mem_toFinset.mpr h)
    simp only [if_neg hnot]
  · intro w hw
    by_contra hws
    apply hw
    have hnot : ¬ closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈ irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme :=
      fun h ↦ hws (hS.mem_toFinset.mpr h)
    simp only [dif_neg hnot]

set_option maxRecDepth 4096 in
theorem hc9k_prime_intersection_cycleClass_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (h : 2 * p + 2 * q = 2 * (p + q)) (x y : X.left)
    (hx : Order.coheight x = p) (hy : Order.coheight y = q) (t : ComplexPoint X)
    (ht : t ∈ hc9k_transverseLocus X x y)
    (hregular : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∧
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X
            (hc9k_translatePoint X t y) 0 : Set X.left)) :
    (cupProductOf X).cup h (cycleComponentSheafClass X x hx)
        (cycleComponentSheafClass X (hc9k_translatePoint X t y)
          ((hc9k_translate_coheight X t y).trans hy)) =
      ccm3_cycleClass X (p + q)
        (hc9k_primeIntersectionCycle X x (hc9k_translatePoint X t y)) := by
  have hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) = p + q := by
    intro w hw
    rw [ht.1 w hw, hx, hy]
  have hsupport := fun w (_ : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) =>
    hc9k_intersection_support_le X x (hc9k_translatePoint X t y) w
  rw [← hc9k_forget_supported_intersectionCycle_aux X p q x (hc9k_translatePoint X t y)
    hcodim hsupport]
  exact hc9k_cup_forget_cast X _ h _ _ _ _
    (hc9k_supported_intersection_product_aux X p q h x y hx hy t ht hregular hcodim hsupport)
    (ccm16_supportedCup_forget X _ _ (2 * p) (2 * q) _ _)

private theorem hc9k_cycleClass_finset_sum (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℕ)
    {ι : Type*} (s : Finset ι) (f : ι → AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X q (∑ i ∈ s, f i) = ∑ i ∈ s, ccm3_cycleClass X q (f i) :=
  map_sum (hc9k_cycleClassHom X q) f s

private theorem hc9k_cycleClass_eq_sum (X : Over (Spec ↧ℂ)) [DecidableEq X.left]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℕ)
    (e : AlgebraicCycle X.left ℚ) (s : Finset X.left) (hs : ∀ x, e x ≠ 0 → x ∈ s) :
    ccm3_cycleClass X q e =
      ∑ x ∈ s, e x • ccm3_cycleClass X q (Function.locallyFinsuppWithin.single x 1) := by
  have he : e = ∑ x ∈ s, (Function.locallyFinsuppWithin.single x (1 : ℚ)).mapRange
      (e x * ·) (mul_zero _) := by
    apply Function.locallyFinsuppWithin.ext
    intro z
    rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    simp only [Function.locallyFinsuppWithin.mapRange_apply,
      Function.locallyFinsuppWithin.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hz
    · rfl
    · by_contra hne
      exact hz (hs z hne)
  conv_lhs => rw [he]
  rw [hc9k_cycleClass_finset_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  exact (ccm6_cycleClass_linear X q (e x) _ 0).2

private theorem hc9k_cycleClass_single_one (X : Over (Spec ↧ℂ)) [DecidableEq X.left]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℕ)
    (y : X.left) (hy : Order.coheight y = q) :
    ccm3_cycleClass X q (Function.locallyFinsuppWithin.single y 1) =
      cycleComponentSheafClass X y hy := by
  unfold ccm3_cycleClass
  change (∑ᶠ z : {z : X.left // Order.coheight z = q},
    (Function.locallyFinsuppWithin.single y (1 : ℚ)) z.1 •
      (cycleComponentSheafClass X z.1 z.2 : HQ X (2 * q))) = _
  rw [finsum_eq_single _ ⟨y, hy⟩ (fun z hz ↦ by
    rw [show (Function.locallyFinsuppWithin.single y (1 : ℚ)) z.1 = 0 by
      simp only [Function.locallyFinsuppWithin.single_apply, ite_eq_right_iff]
      exact fun h ↦ (hz (Subtype.ext h)).elim]
    exact zero_smul _ _)]
  simp only [Function.locallyFinsuppWithin.single_apply, ↓reduceIte, one_smul]

theorem hc9k_local_to_global_cycleClass_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (p q : ℕ)
    (h : 2 * p + 2 * q = 2 * (p + q)) (c d : AlgebraicCycle X.left ℚ)
    (hc : ∀ x, c x ≠ 0 → Order.coheight x = p)
    (hd : ∀ y, d y ≠ 0 → Order.coheight y = q) (t : ComplexPoint X)
    (ht : ∀ x y, c x ≠ 0 → d y ≠ 0 → t ∈ hc9k_transverseLocus X x y)
    (hregular : ∀ x y, c x ≠ 0 → d y ≠ 0 →
      ∀ w : (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
        (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
            (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∧
        (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
            (cycleComponentSingularAmbientClosedFiltration X
              (hc9k_translatePoint X t y) 0 : Set X.left)) :
    (cupProductOf X).cup h (ccm3_cycleClass X p c)
        (ccm3_cycleClass X q (ccm3_flatPullback (GrpObj.mulRight t).hom.left d)) =
      ccm3_cycleClass X (p + q) (hc9k_transverseIntersectionCycle X c d t) := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let S := c.finite_support.toFinset
  let T := d.finite_support.toFinset
  have hS : ∀ x, c x ≠ 0 → x ∈ S := fun x hx ↦ c.finite_support.mem_toFinset.mpr hx
  have hT : ∀ y, d y ≠ 0 → y ∈ T := fun y hy ↦ d.finite_support.mem_toFinset.mpr hy
  have hcS : ∀ x ∈ S, c x ≠ 0 := fun x hx ↦ c.finite_support.mem_toFinset.mp hx
  have hdT : ∀ y ∈ T, d y ≠ 0 := fun y hy ↦ d.finite_support.mem_toFinset.mp hy
  let M : X.left → X.left → AlgebraicCycle X.left ℚ := fun x y ↦
    (hc9k_primeIntersectionCycle X x (hc9k_translatePoint X t y)).mapRange
      (c x * d y * ·) (mul_zero _)
  have hM : ∀ x y, (c x = 0 ∨ d y = 0) → M x y = 0 := by
    intro x y hxy
    apply Function.locallyFinsuppWithin.ext
    intro z
    simp only [M, Function.locallyFinsuppWithin.mapRange_apply]
    rcases hxy with h0 | h0 <;> simp [h0]
  have hinner : ∀ x, ∑ᶠ y, M x y = ∑ y ∈ T, M x y := fun x ↦
    finsum_eq_sum_of_support_subset _ fun y hy ↦ by
      by_contra hyT
      exact hy (hM x y (Or.inr (by by_contra h; exact hyT (hT y h))))
  have hcycle : hc9k_transverseIntersectionCycle X c d t = ∑ x ∈ S, ∑ y ∈ T, M x y := by
    change ∑ᶠ x, ∑ᶠ y, M x y = _
    simp only [hinner]
    refine finsum_eq_sum_of_support_subset _ fun x hx ↦ ?_
    by_contra hxS
    apply hx
    exact Finset.sum_eq_zero fun y _ ↦
      hM x y (Or.inl (by by_contra h; exact hxS (hS x h)))
  have hpull : ccm3_cycleClass X q (ccm3_flatPullback (GrpObj.mulRight t).hom.left d) =
      ∑ y ∈ T, d y • ccm3_cycleClass X q
        (Function.locallyFinsuppWithin.single (hc9k_translatePoint X t y) 1) := by
    have hzero : ∀ y, d y = 0 → (ccm3_flatPullbackPrime (GrpObj.mulRight t).hom.left y).mapRange
        (d y * ·) (mul_zero _) = 0 := by
      intro y hy
      apply Function.locallyFinsuppWithin.ext
      intro z
      simp only [Function.locallyFinsuppWithin.mapRange_apply, hy, zero_mul]
      rfl
    unfold ccm3_flatPullback
    rw [finsum_eq_sum_of_support_subset _ (s := T) fun y hy ↦ by
      by_contra hyT
      exact hy (hzero y (by by_contra h; exact hyT (hT y h)))]
    rw [hc9k_cycleClass_finset_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [(ccm6_cycleClass_linear X q (d y) _ 0).2, hc9k_translate_flatPullbackPrime]
  rw [hc9k_cycleClass_eq_sum X p c S hS, hpull, hcycle]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul, hc9k_cycleClass_finset_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ ?_
  have hcx := hcS x hx
  have hdy := hdT y hy
  rw [hc9k_cycleClass_single_one X p x (hc x hcx),
    hc9k_cycleClass_single_one X q (hc9k_translatePoint X t y)
      ((hc9k_translate_coheight X t y).trans (hd y hdy)),
    hc9k_prime_intersection_cycleClass_aux X p q h x y (hc x hcx) (hd y hdy) t
      (ht x y hcx hdy) (hregular x y hcx hdy)]
  rw [mul_comm (d y) (c x)]
  exact ((ccm6_cycleClass_linear X (p + q) (c x * d y) _ 0).2).symm

theorem hc9k_translation_replaces_second_class_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (p q : ℕ)
    (h : 2 * p + 2 * q = 2 * (p + q)) (c d : AlgebraicCycle X.left ℚ)
    (hd : ∀ y, d y ≠ 0 → Order.coheight y = q) (t : ComplexPoint X) :
    (cupProductOf X).cup h (ccm3_cycleClass X p c)
        (ccm3_cycleClass X q (ccm3_flatPullback (GrpObj.mulRight t).hom.left d)) =
      (cupProductOf X).cup h (ccm3_cycleClass X p c) (ccm3_cycleClass X q d) := by
  rw [ccm11_translated_cycleClass X t q d hd]

private theorem hc9k_cycleClass_mem_span
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (e : AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X n e ∈ algebraicCycleClassSpan X n := by
  unfold ccm3_cycleClass
  refine finsum_induction (· ∈ algebraicCycleClassSpan X n) (Submodule.zero_mem _)
    (fun _ _ ↦ Submodule.add_mem _) (fun z ↦ Submodule.smul_mem _ _ ?_)
  exact (le_sSup ⟨z.1, z.2, rfl⟩ : Submodule.span ℚ {cycleComponentSheafClass X z.1 z.2} ≤
    algebraicCycleClassSpan X n) (Submodule.mem_span_singleton_self _)

private theorem hc9k_single_pure {S : Scheme} [DecidableEq S] (x : S) {n : ℕ}
    (hx : Order.coheight x = n) :
    ∀ y, (Function.locallyFinsuppWithin.single x 1 : AlgebraicCycle S ℚ) y ≠ 0 →
      Order.coheight y = n := by
  intro y hy
  by_cases hxy : y = x
  · rw [hxy, hx]
  · exact (hy (by simp [Function.locallyFinsuppWithin.single_apply, hxy])).elim

theorem hc9k_rational_cycles_multiply_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (p q : ℕ)
    (h : 2 * p + 2 * q = 2 * (p + q)) (c d : AlgebraicCycle X.left ℚ)
    (hc : ∀ x, c x ≠ 0 → Order.coheight x = p)
    (hd : ∀ y, d y ≠ 0 → Order.coheight y = q) :
    (cupProductOf X).cup h (ccm3_cycleClass X p c) (ccm3_cycleClass X q d) ∈
      algebraicCycleClassSpan X (p + q) := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  choose U hU hUt using fun e : X.left × X.left ↦
    hc9k_transverseLocus_contains_nonempty_open_aux X e.1 e.2
  choose W hW hWt using fun e : X.left × X.left ↦
    hc9k_singular_intersections_smaller_aux X e.1 e.2
  let S : Set (X.left × X.left) := Function.support c ×ˢ Function.support d
  have hS : S.Finite := c.finite_support.prod d.finite_support
  let s : Set (Set X.left) := (fun e ↦ ((U e ⊓ W e : X.left.Opens) : Set X.left)) '' S
  have hs : s.Finite := hS.image _
  have hso : ∀ u ∈ s, IsOpen u := by
    rintro _ ⟨e, -, rfl⟩
    exact (U e ⊓ W e).isOpen
  have hdense : Dense (⋂₀ s) := hs.dense_sInter hso (by
    rintro _ ⟨e, -, rfl⟩
    show Dense ((U e ⊓ W e : X.left.Opens) : Set X.left)
    rw [Opens.coe_inf]
    exact (hU e).inter_of_isOpen_left (hW e) (U e).isOpen)
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hdense.nonempty
    (hs.isOpen_sInter hso).isLocallyClosed
  let t₀ := (pointEquivClosedPoint X.hom).symm ⟨z, hzc⟩
  let t : ComplexPoint X := Over.homMk t₀.1 t₀.2
  have htz : t.underlying = z := pointOfClosedPoint_apply X.hom z hzc _
  have hmem : ∀ x y, c x ≠ 0 → d y ≠ 0 → t.underlying ∈ U (x, y) ⊓ W (x, y) := by
    intro x y hx hy
    rw [htz]
    exact Set.mem_sInter.mp hz _ ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  have ht : ∀ x y, c x ≠ 0 → d y ≠ 0 → t ∈ hc9k_transverseLocus X x y :=
    fun x y hx hy ↦ hUt (x, y) t (hmem x y hx hy).1
  have hreg : ∀ x y, c x ≠ 0 → d y ≠ 0 →
      ∀ w : (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
        (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
            (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∧
        (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w ∉
            (cycleComponentSingularAmbientClosedFiltration X
              (hc9k_translatePoint X t y) 0 : Set X.left) := by
    intro x y hx hy w hw
    have hcod := (ht x y hx hy).1 w hw
    obtain ⟨h₁, h₂⟩ := hWt (x, y) t (hmem x y hx hy).2
    exact ⟨fun hsx ↦ (h₁ w hsx).ne' hcod, fun hsz ↦ (h₂ w hsz).ne' hcod⟩
  rw [← hc9k_translation_replaces_second_class_aux X p q h c d hd t,
    hc9k_local_to_global_cycleClass_aux X p q h c d hc hd t ht hreg]
  exact hc9k_cycleClass_mem_span X (p + q) _

theorem hc9k_cycleClassMultiplicative_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    CycleClassMultiplicative (cupProductOf X) := by
  classical
  refine ⟨fun {p q} h a b ha hb ↦ ?_⟩
  have hspan : ∀ {n : ℕ} (P : Submodule ℚ (HQ X (2 * n))),
      (∀ x (hx : Order.coheight x = n), cycleComponentSheafClass X x hx ∈ P) →
        algebraicCycleClassSpan X n ≤ P := by
    intro n P hP
    exact sSup_le (by
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (hP x hx))
  have key : ∀ x (hx : Order.coheight x = p) y (hy : Order.coheight y = q),
      (cupProductOf X).cup h (cycleComponentSheafClass X x hx)
          (cycleComponentSheafClass X y hy) ∈ algebraicCycleClassSpan X (p + q) := by
    intro x hx y hy
    have h' := hc9k_rational_cycles_multiply_aux X p q h
      (Function.locallyFinsuppWithin.single x 1) (Function.locallyFinsuppWithin.single y 1)
      (hc9k_single_pure x hx) (hc9k_single_pure y hy)
    rwa [hc9k_cycleClass_single_one X p x hx, hc9k_cycleClass_single_one X q y hy] at h'
  have hb' : ∀ x (hx : Order.coheight x = p),
      (cupProductOf X).cup h (cycleComponentSheafClass X x hx) b ∈
        algebraicCycleClassSpan X (p + q) := fun x hx ↦
    hspan ((algebraicCycleClassSpan X (p + q)).comap
      ((cupProductOf X).cup h (cycleComponentSheafClass X x hx))) (key x hx) hb
  exact hspan ((algebraicCycleClassSpan X (p + q)).comap
    (((cupProductOf X).cup h).flip b)) hb' ha

theorem hc9k_papw_PWCupClosed_aux
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] {L : Type*} [Field L] [Algebra ℚ L]
    {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
    [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}
    (theta : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A theta u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) :
    HodgeLean.Papers.papw_PWCupClosed A theta u d hu hW P :=
  HodgeLean.Papers.papw_PWCupClosed_of_hC9 A theta u d hu hW P
    (hc9k_cycleClassMultiplicative_aux Y)

end HodgeLean.Adapters
