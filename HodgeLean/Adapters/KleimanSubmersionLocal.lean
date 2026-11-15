import HodgeLean.Adapters.KleimanProductCharts
import HodgeLean.Adapters.KleimanSubmersionAlgebra

/-! # Algebraic local data for the transverse-submersion lemma

Near a complex point of a smooth translated intersection, the étale coordinates of the
intersection scheme, lifted to the ambient variety, express every ambient chart coordinate
modulo the two prime ideals and a function nonvanishing at the point.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Filter
open Topology
open scoped ContDiff Manifold

namespace HodgeLean.Adapters

/-- Sections of an open immersion's target over an open inside its range are determined by their
pullbacks.
Source: Mathlib `Scheme.Hom.app_invApp'`. -/
theorem hc9k_app_injective_of_le_opensRange {A B : Scheme} (f : A ⟶ B) [IsOpenImmersion f]
    (U' : B.Opens) (hU : U' ≤ f.opensRange) : Function.Injective (f.app U') := by
  intro s t hst
  have e := Scheme.Hom.app_invApp' f U' hU
  have hs := congrArg (fun φ : Γ(B, U') ⟶ _ => φ s) e
  have ht := congrArg (fun φ : Γ(B, U') ⟶ _ => φ t) e
  simp only [CommRingCat.comp_apply] at hs ht
  have h2 := congrArg (f.appIso (f ⁻¹ᵁ U')).inv hst
  rw [hs, ht] at h2
  refine (B.presheaf.mapIso (eqToIso ?_).op).commRingCatIsoToRingEquiv.injective h2
  exact (Scheme.Hom.image_preimage_eq_opensRange_inf f U').trans (inf_eq_right.mpr hU)

/-- The constant section with value `r` on an open of a complex scheme. -/
def hc9k_const (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (r : ℂ) : Γ(X.left, W) :=
  X.hom.appLE ⊤ W le_top ((Scheme.ΓSpecIso ↧ℂ).inv r)

/-- A constant global section evaluates to its value.
Source: `AlgebraicGeometry.ComplexPoint.evaluate_top_eq_appTop`. -/
theorem hc9k_evaluate_top_const (X : Over (Spec ↧ℂ)) (r : ℂ) (z : ComplexPoint X) :
    Point.evaluate ⊤ (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv r)) z = r := by
  rw [evaluate_top_eq_appTop]
  have h1 : X.hom.appTop ≫ z.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    have hw : z.left ≫ X.hom = 𝟙 _ := Over.w z
    rw [hw]
    rfl
  have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) ((Scheme.ΓSpecIso ↧ℂ).inv r)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at h2
  rw [h2]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso ↧ℂ).inv_hom_id) r

/-- A constant section evaluates to its value.
Source: `AlgebraicGeometry.Point.evaluate_res`. -/
theorem hc9k_evaluate_const (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (r : ℂ)
    (z : ComplexPoint X)
    (hz : z ∈ Point.overOpen W) : Point.evaluate W (hc9k_const X W r) z = r := by
  change Point.evaluate W (X.left.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
    (X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv r))) z = r
  rw [← Point.evaluate_res (le_top : W ≤ ⊤) _ z hz]
  exact hc9k_evaluate_top_const X r z

/-- Evaluation of a section pulled back along a morphism over `ℂ` is evaluation at the image.
Source: `AlgebraicGeometry.Point.evaluate_map`. -/
theorem hc9k_evaluate_appLE {X Y : Over (Spec ↧ℂ)} (f : Y ⟶ X) (U : X.left.Opens)
    (V : Y.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U) (s : Γ(X.left, U)) (p : ComplexPoint Y)
    (hp : p ∈ Point.overOpen V) :
    Point.evaluate V (f.left.appLE U V e s) p = Point.evaluate U s (Point.map f p) := by
  rw [Point.evaluate_map, Point.evaluate_res e _ p hp]
  rfl

/-- A section of the reduced ideal of the closure of `x` vanishes at complex points of the
closure.
Source: Mathlib `Scheme.IdealSheafData.supportSet_subset_zeroLocus`. -/
theorem hc9k_evaluate_eq_zero_of_mem_primeIdeal (X : Over (Spec ↧ℂ)) (x : X.left)
    (W : X.left.Opens) (hW : IsAffineOpen W) (s : Γ(X.left, W))
    (hs : s ∈ (ccm3_primeIdeal X.left x).ideal ⟨W, hW⟩) (pt : ComplexPoint X)
    (hpt : pt ∈ Point.overOpen W) (hx : pt.underlying ∈ closure ({x} : Set X.left)) :
    Point.evaluate W s pt = 0 := by
  have hsupp : pt.underlying ∈ (ccm3_primeIdeal X.left x).supportSet := by
    change pt.underlying ∈ ((ccm3_primeIdeal X.left x).support : Set X.left)
    change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ({x} : Set X.left), isClosed_closure⟩).support : Set X.left)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hx
  have hz := (ccm3_primeIdeal X.left x).supportSet_subset_zeroLocus ⟨W, hW⟩ hsupp
  rw [Scheme.mem_zeroLocus_iff] at hz
  have hnot := hz s hs
  by_contra hne
  apply hnot
  exact (Point.mem_overOpen_basicOpen_iff_isUnit_evaluate s pt hpt).mpr
    (isUnit_iff_ne_zero.mpr hne)

/-- A section lifted along a closed map from the image of an open immersion pulls back, on any
smaller open, to the restriction of the original section. -/
theorem hc9k_app_lift_restrict {A B C : Scheme} (om : A ⟶ B) [IsOpenImmersion om] (ι : B ⟶ C)
    (UX W : C.Opens) (hWU : W ≤ UX) (hUXω : ι ⁻¹ᵁ UX ≤ om ''ᵁ ⊤) (s : Γ(A, ⊤))
    (r : Γ(C, UX))
    (hr : ι.app UX r = B.presheaf.map (homOfLE hUXω).op ((om.appIso ⊤).inv s)) :
    (om ≫ ι).app W (C.presheaf.map (homOfLE hWU).op r) =
      A.presheaf.map (homOfLE le_top).op s := by
  have e1 : (om ≫ ι) ⁻¹ᵁ W ≤ om ⁻¹ᵁ (ι ⁻¹ᵁ UX) := fun p hp => hWU hp
  have e2 : (om ≫ ι) ⁻¹ᵁ W ≤ om ⁻¹ᵁ (om ''ᵁ ⊤) := fun p _ =>
    ⟨p, trivial, rfl⟩
  have hmor : C.presheaf.map (homOfLE hWU).op ≫ (om ≫ ι).app W =
      ι.app UX ≫ om.appLE (ι ⁻¹ᵁ UX) ((om ≫ ι) ⁻¹ᵁ W) e1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]
  have hmor2 : B.presheaf.map (homOfLE hUXω).op ≫
      om.appLE (ι ⁻¹ᵁ UX) ((om ≫ ι) ⁻¹ᵁ W) e1 =
        om.appLE (om ''ᵁ ⊤) ((om ≫ ι) ⁻¹ᵁ W) e2 :=
    Scheme.Hom.map_appLE _ _ _
  have hmor3 := Scheme.Hom.appIso_inv_appLE om e2
  have k1 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor) r
  have k2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor2) ((om.appIso ⊤).inv s)
  have k3 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor3) s
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at k1 k2 k3
  rw [k1, hr, k2, k3]

/-- Pulling back a restricted section along a morphism is restricting its pullback. -/
theorem hc9k_app_restrict_appLE {A C : Scheme} (f : A ⟶ C) (U W : C.Opens) (hWU : W ≤ U)
    (hN : (⊤ : A.Opens) ≤ f ⁻¹ᵁ U) (t : Γ(C, U)) :
    f.app W (C.presheaf.map (homOfLE hWU).op t) =
      A.presheaf.map (homOfLE le_top).op (f.appLE U ⊤ hN t) := by
  have hmor : C.presheaf.map (homOfLE hWU).op ≫ f.app W =
      f.appLE U ⊤ hN ≫ A.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)).op := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  have k := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor) t
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using k

/-- Pulling back a constant section gives the restricted constant global section. -/
theorem hc9k_app_const (X : Over (Spec ↧ℂ)) {A : Scheme} (f : A ⟶ X.left) (W : X.left.Opens)
    (r : ℂ) :
    f.app W (hc9k_const X W r) =
      A.presheaf.map (homOfLE le_top).op
        ((f ≫ X.hom).appTop ((Scheme.ΓSpecIso ↧ℂ).inv r)) := by
  have hmor : X.hom.appLE ⊤ W le_top ≫ f.app W =
      (f ≫ X.hom).app ⊤ ≫ A.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)).op := by
    rw [Scheme.Hom.app_eq_appLE]
    exact Scheme.Hom.appLE_comp_appLE f X.hom ⊤ W (f ⁻¹ᵁ W) _ _
  have k := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor) ((Scheme.ΓSpecIso ↧ℂ).inv r)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at k
  exact k

/-- The algebraic local data at a complex point of a translated intersection that is smooth off
the two singular loci: a smooth complex scheme `Y` mapping into the intersection through the
point, and, on a Zariski open around the point, the relation expressing each ambient chart
coordinate through the lifted étale coordinates of `Y` modulo the two prime ideals.
Source: Stacks Project, Tag 02GU; Hartshorne, *Algebraic Geometry*, II, Proposition 5.9. -/
theorem hc9k_transverse_local_data
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (x z : X.left)
    (hsm : ∀ v : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left z).subscheme,
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left z).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) →
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left z).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X z 0 : Set X.left) →
      v ∈ ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left z).subschemeι ≫
        X.hom).smoothLocus)
    (a : ComplexPoint X) (hax : a ∈ cycleComponentAnalyticClosedSupport X x)
    (haz : a ∈ cycleComponentAnalyticClosedSupport X z)
    (hax' : a ∉ cycleComponentSingularAnalyticClosedFiltration X x 0)
    (haz' : a ∉ cycleComponentSingularAnalyticClosedFiltration X z 0) :
    ∃ (n : ℕ) (Y : Over (Spec ↧ℂ)) (_ : SmoothOfRelativeDimension n Y.hom) (j : Y ⟶ X)
      (zY : ComplexPoint Y), Point.map j zY = a ∧
      (∀ yy : ComplexPoint Y, Point.map j yy ∈ cycleComponentAnalyticClosedSupport X x ∧
        Point.map j yy ∈ cycleComponentAnalyticClosedSupport X z) ∧
      ∃ (W : X.left.Opens) (_ : a ∈ Point.overOpen W) (σ : Fin d → Γ(X.left, W))
        (u : Fin n → Γ(X.left, W)) (b : Fin d → Fin n → Γ(X.left, W))
        (α β : Fin d → Γ(X.left, W)),
        (∀ k, Point.evaluate W (σ k) a ≠ 0) ∧
        (∀ k, ∀ pt ∈ Point.overOpen W, pt ∈ (localChart X d a).source →
          Point.evaluate W (σ k) pt * (localChart X d a pt k - localChart X d a a k) =
            ∑ i, Point.evaluate W (b k i) pt *
                (Point.evaluate W (u i) pt - Point.evaluate W (u i) a) +
              Point.evaluate W (α k) pt + Point.evaluate W (β k) pt) ∧
        (∀ k, ∀ pt ∈ Point.overOpen W, pt ∈ cycleComponentAnalyticClosedSupport X x →
          Point.evaluate W (α k) pt = 0) ∧
        (∀ k, ∀ pt ∈ Point.overOpen W, pt ∈ cycleComponentAnalyticClosedSupport X z →
          Point.evaluate W (β k) pt = 0) ∧
        (∀ i, ∀ᶠ v in 𝓝 (localChart Y n zY zY),
          Point.evaluate W (u i) (Point.map j ((localChart Y n zY).symm v)) = v i) := by
  classical
  set I := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left z with hIdef
  set ι := I.subschemeι with hιdef
  -- the point of the intersection scheme over `a`
  have hsupp : ∀ q : X.left, q ∈ (I.support : Set X.left) ↔
      q ∈ closure ({x} : Set X.left) ∧ q ∈ closure ({z} : Set X.left) := by
    intro q
    rw [hIdef, Scheme.IdealSheafData.support_sup]
    change (q ∈ ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ({x} : Set X.left), isClosed_closure⟩).support : Set X.left) ∧
      q ∈ ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ({z} : Set X.left), isClosed_closure⟩).support : Set X.left)) ↔ _
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hamem : a.underlying ∈ Set.range ι := by
    rw [hιdef, Scheme.IdealSheafData.range_subschemeι, hsupp]
    exact ⟨hax, haz⟩
  obtain ⟨v, hv⟩ := hamem
  have hvs : v ∈ (ι ≫ X.hom).smoothLocus :=
    hsm v (by rw [hv]; exact hax') (by rw [hv]; exact haz')
  -- the ambient étale chart at `a`
  let DX := localEtaleCoordinates X d a
  let A := DX.ambientCoordinateOpen
  have haA : a.underlying ∈ A := by
    change a.underlying ∈ DX.neighborhood.ι ''ᵁ ⊤
    rw [Scheme.Opens.ι_image_top]
    exact mem_localEtaleCoordinates X d a
  let T : Fin d → Γ(X.left, A) := DX.ambientCoordinateSection
  have hT : ∀ k, ∀ pt ∈ (localChart X d a).source,
      localChart X d a pt k = Point.evaluate A (T k) pt :=
    fun k pt hpt => localChart_apply_component_eq_evaluate X d a pt hpt k
  -- a standard-smooth affine piece of the smooth locus of the intersection
  let Sm := (ι ≫ X.hom).smoothLocus
  let fS : Sm.toScheme ⟶ Spec ↧ℂ := Sm.ι ≫ ι ≫ X.hom
  have : Smooth fS := Scheme.Hom.smooth_restrict_smoothLocus (ι ≫ X.hom)
  let v' : Sm.toScheme := ⟨v, hvs⟩
  obtain ⟨V, hV, hv'V, hstd⟩ := Smooth.exists_affine_isStandardSmooth fS v'
  obtain ⟨n, hn⟩ := hstd.exists_isStandardSmoothOfRelativeDimension
  let O : Sm.toScheme.Opens := (Sm.ι ≫ ι) ⁻¹ᵁ A
  have hv'O : v' ∈ O := by
    change ι (Sm.ι v') ∈ A
    change ι v ∈ A
    rw [hv]
    exact haA
  obtain ⟨r, hrO, hv'r⟩ := hV.exists_basicOpen_le ⟨v', hv'O⟩ hv'V
  let V' := Sm.toScheme.basicOpen r
  have hV' : IsAffineOpen V' := hV.basicOpen r
  have hn' := isStandardSmoothOfRelativeDimension_appLE_basicOpen fS hV r hn
  have hYsm : SmoothOfRelativeDimension n (V'.ι ≫ fS) :=
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth fS hV' hn'
  -- the smooth complex scheme `Y` and its map to `X`
  let Y : Over (Spec ↧ℂ) := Over.mk (V'.ι ≫ fS)
  have hYinst : SmoothOfRelativeDimension n Y.hom := hYsm
  have : Smooth Y.hom := hYinst.smooth
  let o : Y.left ⟶ I.subscheme := V'.ι ≫ Sm.ι
  let j : Y ⟶ X := Over.homMk (o ≫ ι) (by simp only [Category.assoc]; rfl)
  have hjleft : j.left = o ≫ ι := rfl
  have hjA : ∀ p : Y.left, j.left p ∈ A := fun p => hrO p.2
  have : IsImmersion j.left := by rw [hjleft]; infer_instance
  have ha_range : a ∈ Set.range (Point.map j) := by
    rw [range_map_of_isImmersion (i := j)]
    exact ⟨⟨v', hv'r⟩, hv⟩
  obtain ⟨zY, hzY⟩ := ha_range
  have hjS : ∀ yy : ComplexPoint Y, Point.map j yy ∈ cycleComponentAnalyticClosedSupport X x ∧
      Point.map j yy ∈ cycleComponentAnalyticClosedSupport X z := by
    intro yy
    have hm : (Point.map j yy).underlying ∈ (I.support : Set X.left) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨o yy.underlying, rfl⟩
    exact (hsupp _).mp hm
  -- étale coordinates of `Y` at the point over `a`
  let DY := localEtaleCoordinates Y n zY
  let N := DY.neighborhood
  have hzN : zY ∈ Point.overOpen N := mem_localEtaleCoordinates Y n zY
  let g := DY.coordinateRingHomOnOpen
  have hg : g.Etale := DY.coordinateRingHomOnOpen_etale
  let zN : ComplexPoint (openScheme Y N) := asOpenPoint Y N zY hzN
  have hzNm : Point.map (openInclusion Y N) zN = zY :=
    Over.OverMorphism.ext (liftToOpen_fac Y N zY hzN)
  let φ : Γ(N.toScheme, ⊤) →+* ℂ :=
    (Point.evaluationHom (X := openScheme Y N) ⊤ ⟨zN, trivial⟩).hom
  have hφ : ∀ s, φ s = Point.evaluate ⊤ s zN := fun s => Point.evaluationHom_apply _ _ _
  let hO : openScheme Y N ⟶ X := openInclusion Y N ≫ j
  have hOz : Point.map hO zN = a := by
    simp only [hO, Point.map_comp_apply, hzNm, hzY]
  have hφC : ∀ c, φ (g (MvPolynomial.C c)) = c := by
    intro c
    have e := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      DY.C_comp_coordinateRingHomOnOpen) c
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at e
    rw [hφ]
    change Point.evaluate ⊤ (g (MvPolynomial.C c)) zN = c
    rw [e]
    exact hc9k_evaluate_top_const (openScheme Y N) c zN
  -- the open immersion of the étale chart of `Y` into the intersection scheme
  let om : N.toScheme ⟶ I.subscheme := N.ι ≫ o
  let h : N.toScheme ⟶ X.left := om ≫ ι
  let hO' : openScheme Y N ⟶ X := Over.homMk h (by
    change ((N.ι ≫ V'.ι ≫ Sm.ι) ≫ ι) ≫ X.hom = N.ι ≫ V'.ι ≫ Sm.ι ≫ ι ≫ X.hom
    simp only [Category.assoc])
  have hOO : hO' = hO := by
    apply Over.OverMorphism.ext
    change (N.ι ≫ V'.ι ≫ Sm.ι) ≫ ι = N.ι ≫ (V'.ι ≫ Sm.ι) ≫ ι
    simp only [Category.assoc]
  have hOz' : Point.map hO' zN = a := by rw [hOO]; exact hOz
  -- the unramified relation for each ambient chart coordinate
  have hNA : (⊤ : N.toScheme.Opens) ≤ h ⁻¹ᵁ A := fun p _ => hjA (N.ι p)
  let tS : Fin d → Γ(N.toScheme, ⊤) := fun k => h.appLE A ⊤ hNA (T k)
  let c : Fin d → ℂ := fun k => Point.evaluate A (T k) a
  have htS : ∀ k, φ (tS k) = c k := by
    intro k
    rw [hφ]
    exact (hc9k_evaluate_appLE hO' A ⊤ hNA (T k) zN trivial).trans (by rw [hOz'])
  have hzero_k : ∀ k, φ (tS k - g (MvPolynomial.C (c k))) = 0 := by
    intro k
    rw [map_sub, htS, hφC, sub_self]
  choose σS bS hσS hrelS using fun k =>
    hc9k_etale_point_relation g hg φ hφC (tS k - g (MvPolynomial.C (c k))) (hzero_k k)
  let eS : Fin n → ℂ := fun i => φ (g (MvPolynomial.X i))
  -- lifting the sections to the ambient variety
  let elt : Fin d ⊕ (Fin d × Fin n) ⊕ Fin n → Γ(N.toScheme, ⊤) :=
    Sum.elim σS (Sum.elim (fun ki => bS ki.1 ki.2) (fun i => g (MvPolynomial.X i)))
  let fam : Fin d ⊕ (Fin d × Fin n) ⊕ Fin n → Γ(I.subscheme, om ''ᵁ ⊤) :=
    fun l => (om.appIso ⊤).inv (elt l)
  have hvom : v ∈ om ''ᵁ ⊤ := by
    have hinj : ι (om zN.underlying) = ι v := by
      rw [hv]
      change (Point.map hO' zN).underlying = a.underlying
      rw [hOz']
    exact ⟨zN.underlying, trivial, ι.isEmbedding.injective hinj⟩
  obtain ⟨UX, hUX, hUXom, haUX, rt, hrt⟩ :=
    ι.exists_affine_local_section_lifts (om ''ᵁ ⊤) fam v hvom
  have haUX' : a.underlying ∈ UX := hv ▸ haUX
  obtain ⟨_, ⟨W, hW, rfl⟩, haW, hWle⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show a.underlying ∈ UX ⊓ A from ⟨haUX', haA⟩) (UX ⊓ A).isOpen
  have hWU : W ≤ UX := fun p hp => (hWle hp).1
  have hWA : W ≤ A := fun p hp => (hWle hp).2
  let resW : Γ(X.left, UX) → Γ(X.left, W) := fun s => X.left.presheaf.map (homOfLE hWU).op s
  let σ : Fin d → Γ(X.left, W) := fun k => resW (rt (Sum.inl k))
  let b : Fin d → Fin n → Γ(X.left, W) := fun k i => resW (rt (Sum.inr (Sum.inl (k, i))))
  let u : Fin n → Γ(X.left, W) := fun i => resW (rt (Sum.inr (Sum.inr i)))
  let TW : Fin d → Γ(X.left, W) := fun k => X.left.presheaf.map (homOfLE hWA).op (T k)
  let ρ : Γ(N.toScheme, ⊤) →+* Γ(N.toScheme, h ⁻¹ᵁ W) :=
    (N.toScheme.presheaf.map (homOfLE (le_top : h ⁻¹ᵁ W ≤ ⊤)).op).hom
  have hlift : ∀ l, h.app W (resW (rt l)) = ρ (elt l) := fun l =>
    hc9k_app_lift_restrict om ι UX W hWU hUXom (elt l) (rt l) (hrt l)
  have hTW : ∀ k, h.app W (TW k) = ρ (tS k) := fun k =>
    hc9k_app_restrict_appLE h A W hWA hNA (T k)
  have hconst : ∀ r, h.app W (hc9k_const X W r) = ρ (g (MvPolynomial.C r)) := by
    intro r
    rw [hc9k_app_const X h W r]
    have e := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      DY.C_comp_coordinateRingHomOnOpen) r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at e
    change _ = ρ (g (MvPolynomial.C r))
    rw [e]
    have hhX : h ≫ X.hom = N.ι ≫ Y.hom := by
      change ((N.ι ≫ V'.ι ≫ Sm.ι) ≫ ι) ≫ X.hom =
        N.ι ≫ V'.ι ≫ Sm.ι ≫ ι ≫ X.hom
      simp only [Category.assoc]
    rw [hhX]
  -- the relation holds on the intersection scheme
  let Ψ : Fin d → Γ(X.left, W) := fun k =>
    σ k * (TW k - hc9k_const X W (c k)) - ∑ i, b k i * (u i - hc9k_const X W (eS i))
  have hΨh : ∀ k, h.app W (Ψ k) = 0 := by
    intro k
    have hσl : h.app W (σ k) = ρ (σS k) := hlift (Sum.inl k)
    have hbl : ∀ i, h.app W (b k i) = ρ (bS k i) := fun i => hlift (Sum.inr (Sum.inl (k, i)))
    have hul : ∀ i, h.app W (u i) = ρ (g (MvPolynomial.X i)) := fun i =>
      hlift (Sum.inr (Sum.inr i))
    simp only [Ψ, map_sub, map_mul, map_sum]
    change h.app W (σ k) * (h.app W (TW k) - h.app W (hc9k_const X W (c k))) -
        ∑ i, h.app W (b k i) * (h.app W (u i) - h.app W (hc9k_const X W (eS i))) = 0
    rw [hσl, hTW, hconst]
    simp only [hbl, hul, hconst]
    have h0 : ρ (σS k * (tS k - g (MvPolynomial.C (c k))) -
        ∑ i, bS k i * (g (MvPolynomial.X i) - g (MvPolynomial.C (eS i)))) = 0 := by
      rw [hrelS k, sub_self, map_zero]
    simpa only [map_sub, map_mul, map_sum] using h0
  have hΨ : ∀ k, ι.app W (Ψ k) = 0 := by
    intro k
    have hle : ι ⁻¹ᵁ W ≤ om.opensRange := fun p hp => by
      obtain ⟨q, _, hq⟩ := hUXom (hWU hp)
      exact ⟨q, hq⟩
    apply hc9k_app_injective_of_le_opensRange om (ι ⁻¹ᵁ W) hle
    have k1 : h.app W (Ψ k) = om.app (ι ⁻¹ᵁ W) (ι.app W (Ψ k)) := by
      change (om ≫ ι).app W (Ψ k) = _
      rw [Scheme.Hom.comp_app]
      rfl
    rw [← k1, map_zero]
    exact hΨh k
  -- decomposition into the two prime ideals
  have hmem : ∀ k, Ψ k ∈ (ccm3_primeIdeal X.left x).ideal ⟨W, hW⟩ ⊔
      (ccm3_primeIdeal X.left z).ideal ⟨W, hW⟩ := by
    intro k
    have : Ψ k ∈ I.ideal ⟨W, hW⟩ := by
      rw [← Scheme.IdealSheafData.ker_subschemeι_app]
      exact RingHom.mem_ker.mpr (hΨ k)
    exact this
  choose α hα β hβ hαβ using fun k => Submodule.mem_sup.mp (hmem k)
  -- evaluation of lifted sections at images of points of the étale chart
  have hEV : ∀ l (p : ComplexPoint (openScheme Y N)), Point.map hO' p ∈ Point.overOpen W →
      Point.evaluate W (resW (rt l)) (Point.map hO' p) = Point.evaluate ⊤ (elt l) p := by
    intro l p hp
    have hp' : p ∈ Point.overOpen (h ⁻¹ᵁ W) := (Point.mem_overOpen_map_iff hO' p W).mp hp
    rw [Point.evaluate_map]
    change Point.evaluate (h ⁻¹ᵁ W) (h.app W (resW (rt l))) p = _
    rw [hlift l, Point.evaluate_res (le_top : h ⁻¹ᵁ W ≤ ⊤) (elt l) p hp']
    rfl
  have haW' : Point.map hO' zN ∈ Point.overOpen W := by rw [hOz']; exact haW
  have heS : ∀ i, Point.evaluate W (u i) a = eS i := by
    intro i
    have := hEV (Sum.inr (Sum.inr i)) zN haW'
    rw [hOz'] at this
    change _ = φ (g (MvPolynomial.X i))
    rw [hφ]
    exact this
  refine ⟨n, Y, hYinst, j, zY, hzY, hjS, W, haW, σ, u, b, α, β, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have := hEV (Sum.inl k) zN haW'
    rw [hOz'] at this
    change Point.evaluate W (σ k) a ≠ 0
    rw [this, ← hφ]
    exact hσS k
  · intro k pt hpt hpts
    let E := (Point.evaluationHom W ⟨pt, hpt⟩).hom
    have hE : ∀ s, E s = Point.evaluate W s pt := fun s => Point.evaluationHom_apply _ _ _
    have e1 : E (α k) + E (β k) = E (σ k) * (E (TW k) - E (hc9k_const X W (c k))) -
        ∑ i, E (b k i) * (E (u i) - E (hc9k_const X W (eS i))) := by
      rw [← map_add, hαβ k]
      simp only [Ψ, map_sub, map_mul, map_sum]
    simp only [hE, hc9k_evaluate_const X W _ pt hpt] at e1
    have hTk : Point.evaluate W (TW k) pt = localChart X d a pt k := by
      rw [hT k pt hpts]
      exact (Point.evaluate_res hWA (T k) pt hpt).symm
    have hck : c k = localChart X d a a k := (hT k a (mem_localChart_source X d a)).symm
    rw [hTk, hck] at e1
    simp only [heS]
    linear_combination -e1
  · intro k pt hpt hx
    exact hc9k_evaluate_eq_zero_of_mem_primeIdeal X x W hW (α k) (hα k) pt hpt hx
  · intro k pt hpt hx
    exact hc9k_evaluate_eq_zero_of_mem_primeIdeal X z W hW (β k) (hβ k) pt hpt hx
  · intro i
    let eY := localChart Y n zY
    have hzYs : zY ∈ eY.source := mem_localChart_source Y n zY
    have hv₀t : eY zY ∈ eY.target := eY.map_source hzYs
    have hJt : Tendsto (fun v => Point.map j (eY.symm v)) (𝓝 (eY zY)) (𝓝 a) := by
      have h1 := (Point.continuous_map j).continuousAt.comp (eY.continuousAt_symm hv₀t)
      have h2 : ContinuousAt (fun v => Point.map j (eY.symm v)) (eY zY) := h1
      rw [ContinuousAt, eY.left_inv hzYs, hzY] at h2
      exact h2
    filter_upwards [eY.open_target.mem_nhds hv₀t,
      hJt.eventually ((Point.isOpen_overOpen W).mem_nhds haW)] with v hvt hvW
    have hsrc : eY.symm v ∈ eY.source := eY.map_target hvt
    have hpN : eY.symm v ∈ Point.overOpen N :=
      mem_coordinateNeighborhood_of_mem_localChart_source Y n zY _ hsrc
    let pN := asOpenPoint Y N (eY.symm v) hpN
    have hpNm : Point.map (openInclusion Y N) pN = eY.symm v :=
      Over.OverMorphism.ext (liftToOpen_fac Y N _ hpN)
    have hmapN : Point.map hO' pN = Point.map j (eY.symm v) := by
      rw [hOO]
      simp only [hO, Point.map_comp_apply, hpNm]
    have hW' : Point.map hO' pN ∈ Point.overOpen W := by rw [hmapN]; exact hvW
    have := hEV (Sum.inr (Sum.inr i)) pN hW'
    rw [hmapN] at this
    change Point.evaluate W (u i) (Point.map j (eY.symm v)) = v i
    rw [this]
    change Point.evaluate ⊤ (g (MvPolynomial.X i)) pN = v i
    rw [← evaluate_openEquiv Y N, hpNm]
    change Point.evaluate DY.ambientCoordinateOpen (DY.ambientCoordinateSection i) (eY.symm v) = v i
    rw [← localChart_apply_component_eq_evaluate Y n zY _ hsrc i]
    exact congrFun (eY.right_inv hvt) i

end HodgeLean.Adapters
