import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedLocalNormalCalculation
import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedComponentBase
import HodgeLean.Foundations.Program.SchoenTransferQ3CommonTangentialNeighbourhood
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentIsolatingOpen
import HodgeLean.Foundations.Program.SchoenTransferQ3OpenFiniteType
import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedCoefficients

/-! The actual retained inverse component supplies its generic local normalization. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
open AlgebraicTopology.Singular HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- The retained geometric data construct a generic ambient neighbourhood
where the original pulled class has the actual unreduced cycle normalization. -/
theorem s4_q3_retained_component_open_normal_calculation
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (q : X ⟶ W) [IsFinite q.left] [Surjective q.left] (hq : IsOpenMap q.left)
    (z : AlgebraicCycle W.left ℚ) (k : ℕ)
    (hz : ∀ x ∈ z.support, Order.coheight x = k ∧
      ∃ A : W.left.Opens, x ∈ A ∧ Smooth (A.ι ≫ W.hom))
    (hS : ∀ a, Point.map q a ∈ a3b4_cycleSupport W.hom z →
      a ∈ a3b4_cycleSupport X.hom (ccm3_flatPullback q.left z))
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
      (a3b4_cycleSupport W.hom z)ᶜ) (2 * k))
    (hα : a3b4_IsCycleClass W.hom z k α)
    (x : W.left) (hx : x ∈ z.support)
    (η : (ccm3_inverseIdeal q.left x).subscheme)
    (hη : closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme) :
    let p := (ccm3_inverseIdeal q.left x).subschemeι η
    let γ := ccm3_flatPullback q.left z
    ∃ U : X.left.Opens, p ∈ U ∧
      ∀ a : ComplexPoint X, a.underlying ∈ U → a.underlying ∈ closure ({p} : Set X.left) →
        (∀ s ∈ γ.support, s ≠ p → a.underlying ∉ closure ({s} : Set X.left)) →
        ∃ (r : ℕ)
          (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
          (hflat : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0),
          a ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
          ∃ (N : Set (ComplexPoint X)) (hNe : N ⊆ e.source), IsOpen N ∧ a ∈ N ∧
            relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N (a3b4_cycleSupport X.hom γ))
              (relativeCohomologyMap ℚ (2 * k)
                (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
                  (a3b4_cycleSupport X.hom γ) (a3b4_cycleSupport W.hom z) hS) α) =
            a3b4_multiplicity X.hom γ a • chartNormalProjectionCoclass (Fin r → ℂ) k e
              (a3b4_cycleSupport X.hom γ) hflat N hNe := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  letI : IsNoetherian W.left := {}
  let p := (ccm3_inverseIdeal q.left x).subschemeι η
  let I := ccm3_primeIdeal X.left p
  let J := ccm3_primeIdeal W.left x
  let C₀ : Over (Spec ↧ℂ) := Over.mk (I.subschemeι ≫ X.hom)
  let D₀ : Over (Spec ↧ℂ) := Over.mk (J.subschemeι ≫ W.hom)
  let i₀ : C₀ ⟶ X := Over.homMk I.subschemeι rfl
  let j₀ : D₀ ⟶ W := Over.homMk J.subschemeι rfl
  letI : IsIntegral C₀.left := inferInstanceAs (IsIntegral (cycleComponent X.left p))
  letI : IsIntegral D₀.left := inferInstanceAs (IsIntegral (cycleComponent W.left x))
  letI : IsClosedImmersion i₀.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  letI : IsClosedImmersion j₀.left := inferInstanceAs (IsClosedImmersion J.subschemeι)
  letI : LocallyOfFiniteType C₀.hom := inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ X.hom))
  letI : QuasiCompact C₀.hom := inferInstanceAs (QuasiCompact (I.subschemeι ≫ X.hom))
  letI : IsSeparated C₀.hom := inferInstanceAs (IsSeparated (I.subschemeι ≫ X.hom))
  letI : LocallyOfFiniteType D₀.hom := inferInstanceAs (LocallyOfFiniteType (J.subschemeι ≫ W.hom))
  letI : LocallyOfFinitePresentation D₀.hom := inferInstanceAs (LocallyOfFinitePresentation (J.subschemeι ≫ W.hom))
  letI : QuasiCompact D₀.hom := inferInstanceAs (QuasiCompact (J.subschemeι ≫ W.hom))
  letI : IsSeparated D₀.hom := inferInstanceAs (IsSeparated (J.subschemeι ≫ W.hom))
  obtain ⟨ψ, f₀, hψ, hf₀, hψClosed, hfinite₀, hsurj₀, S₀, hdS₀, hsD₀, he₀, hsC₀, _, hgood⟩ :=
    s4_q3_retained_component_generic_length_base q hq x η hη
  letI : IsFinite f₀.left := hfinite₀
  have hsupport₀ : i₀ ≫ q = f₀ ≫ j₀ := Over.OverMorphism.ext hf₀.symm
  have hmap : q.left p = x := s4_q3_inverse_component_dominates q.left hq x η hη
  have hp : Order.coheight p = k :=
    (s4_q3_coheight_eq_of_open_quasiFinite q.left hq p).trans (by rw [hmap]; exact (hz x hx).1)
  let γ := ccm3_flatPullback q.left z
  let m := genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2
  have hcoeff : γ p = z x * (m : ℚ) := s4_q3_inverse_component_coefficient q hq z x η hη
  have hm : 0 < m := (genericMultiplicity_pos q x η hη).1
  have hγp : p ∈ γ.support := by
    change γ p ≠ 0
    rw [hcoeff]
    exact mul_ne_zero hx (by exact_mod_cast Nat.ne_of_gt hm)
  obtain ⟨A₀, hxA₀, hsA₀⟩ := (hz x hx).2
  obtain ⟨A₁, hxA₁, havoid⟩ := s4_q3_pure_cycle_component_isolating_open W.left z k
    (fun t ht => (hz t ht).1) x hx
  let A := A₀ ⊓ A₁
  have hxA : x ∈ A := ⟨hxA₀, hxA₁⟩
  have hsA : Smooth (A.ι ≫ W.hom) := by
    letI := hsA₀
    have hfac : W.left.homOfLE (show A ≤ A₀ from inf_le_left) ≫ (A₀.ι ≫ W.hom) = A.ι ≫ W.hom := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [← hfac]
    infer_instance
  have hgenI : I.subschemeι (genericPoint C₀.left) = p := by
    change cycleComponentι X.left p (genericPoint (cycleComponent X.left p)) = p
    rw [← cycleComponentGenericPoint_eq_genericPoint, cycleComponentι_genericPoint]
  have hgenTarget : j₀.left (f₀.left (genericPoint C₀.left)) = x := by
    have hh := congrArg (fun a : C₀.left ⟶ W.left => a (genericPoint C₀.left)) hf₀
    change j₀.left (f₀.left (genericPoint C₀.left)) = q.left (I.subschemeι (genericPoint C₀.left)) at hh
    exact hh.trans (by rw [hgenI, hmap])
  have hgenS₀ : genericPoint C₀.left ∈ f₀.left ⁻¹ᵁ S₀ := by
    obtain ⟨t, ht⟩ := hdS₀.nonempty
    obtain ⟨c, hc⟩ := hsurj₀ t
    have hcS : f₀.left c ∈ S₀ := by rw [hc]; exact ht
    exact (genericPoint_specializes c).mem_open (f₀.left ⁻¹ᵁ S₀).isOpen hcS
  let O := (f₀.left ⁻¹ᵁ S₀) ⊓ (f₀.left ⁻¹ᵁ (j₀.left ⁻¹ᵁ A))
  have hgenO : genericPoint C₀.left ∈ O := by
    refine ⟨hgenS₀, ?_⟩
    change j₀.left (f₀.left (genericPoint C₀.left)) ∈ A
    rw [hgenTarget]
    exact hxA
  obtain ⟨S₁, hdS₁, hS₁₀, hpreO, hsD₁, he₁, hsC₁⟩ :=
    s4_q3_smooth_etale_refinement_in_source_open f₀ S₀ hdS₀ he₀ O hgenO
  have hS₁A : S₁ ≤ j₀.left ⁻¹ᵁ A := by
    intro t ht
    obtain ⟨c, hc⟩ := hsurj₀ t
    have hcS : f₀.left c ∈ S₁ := by rw [hc]; exact ht
    have hh := (hpreO hcS).2
    change j₀.left (f₀.left c) ∈ A at hh
    rw [hc] at hh
    exact hh
  obtain ⟨V₀, hV₀A, hV₀S, i₁, j₁, f₁, q₁, hsq₁, hi₁, hj₁, hf₁, hq₁,
    hiClosed₁, hjClosed₁, hfinite₁, heF₁, hsD₁', hsC₁', hcartI₁, hcartJ₁, _, hcartQ₁⟩ :=
    s4_q3_support_open_square i₀ j₀ f₀ q hsupport₀ A S₁ hS₁A hsD₁ he₁
  let C₁ := openScheme C₀ (f₀.left ⁻¹ᵁ S₁)
  let D₁ := openScheme D₀ S₁
  let X₁ := openScheme X (q.left ⁻¹ᵁ V₀)
  let W₁ := openScheme W V₀
  let bC₁ := openInclusion C₀ (f₀.left ⁻¹ᵁ S₁)
  let bD₁ := openInclusion D₀ S₁
  let aX₁ := openInclusion X (q.left ⁻¹ᵁ V₀)
  let aW₁ := openInclusion W V₀
  have hgenS₁ : genericPoint C₀.left ∈ f₀.left ⁻¹ᵁ S₁ := by
    obtain ⟨t, ht⟩ := hdS₁.nonempty
    obtain ⟨c, hc⟩ := hsurj₀ t
    have hcS : f₀.left c ∈ S₁ := by rw [hc]; exact ht
    exact (genericPoint_specializes c).mem_open (f₀.left ⁻¹ᵁ S₁).isOpen hcS
  let c₁ : C₁.left := ⟨genericPoint C₀.left, hgenS₁⟩
  letI : Nonempty C₁.left := ⟨c₁⟩
  letI : Nonempty D₁.left := ⟨f₁.left c₁⟩
  letI : Nonempty X₁.left := ⟨i₁.left c₁⟩
  letI : Nonempty W₁.left := ⟨q₁.left (i₁.left c₁)⟩
  letI : IsIntegral C₁.left := isIntegral_of_isOpenImmersion (f₀.left ⁻¹ᵁ S₁).ι
  letI : IsIntegral D₁.left := isIntegral_of_isOpenImmersion S₁.ι
  letI : IsIntegral X₁.left := isIntegral_of_isOpenImmersion (q.left ⁻¹ᵁ V₀).ι
  letI : IsIntegral W₁.left := isIntegral_of_isOpenImmersion V₀.ι
  letI : Smooth C₁.hom := hsC₁'
  letI : Smooth D₁.hom := hsD₁'
  letI : Smooth X₁.hom := inferInstanceAs (Smooth ((q.left ⁻¹ᵁ V₀).ι ≫ X.hom))
  have hsV₀ : Smooth (V₀.ι ≫ W.hom) := by
    letI := hsA
    have hfac : W.left.homOfLE hV₀A ≫ (A.ι ≫ W.hom) = V₀.ι ≫ W.hom := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [← hfac]
    infer_instance
  letI : Smooth W₁.hom := hsV₀
  letI : IsClosedImmersion i₁.left := hiClosed₁
  letI : IsClosedImmersion j₁.left := hjClosed₁
  letI : IsFinite q₁.left := hfinite₁
  letI : Flat q₁.left := by rw [hq₁]; exact s4_q3_finite_flat_over_smooth_open q V₀ hsV₀
  letI : Etale f₁.left := heF₁
  obtain ⟨r, hr⟩ := Smooth.exists_smoothOfRelativeDimension D₁.hom
  letI : SmoothOfRelativeDimension r D₁.hom := hr
  letI : SmoothOfRelativeDimension r C₁.hom := by
    rw [← Over.w f₁]
    have hh : SmoothOfRelativeDimension (0 + r) (f₁.left ≫ D₁.hom) := inferInstance
    simpa only [Nat.zero_add] using hh
  obtain ⟨C₂, D₂, X₂, W₂, T, bC₂, bD₂, aX₂, aW₂, i₂, j₂, f₂, q₂, H,
    hOpenC₂, hOpenD₂, hOpenX₂, hOpenW₂, hiClosed₂, hjClosed₂, hfinite₂, hflat₂, heF₂,
    hsq₂, _, hsH, hsQH, heJH, heIQH, hsC₂, hsD₂, hsX₂, hsW₂, hsT, hdimT,
    hcartI₂, hcartJ₂, hcartQ₂, cgen, hgen₂⟩ :=
    s4_q3_common_smooth_tangential_support_neighbourhood r i₁ j₁ f₁ q₁ hsq₁
  letI : IsOpenImmersion bC₂.left := hOpenC₂
  letI : IsOpenImmersion bD₂.left := hOpenD₂
  letI : IsOpenImmersion aX₂.left := hOpenX₂
  letI : IsOpenImmersion aW₂.left := hOpenW₂
  letI : IsOpenImmersion bC₁.left := inferInstanceAs (IsOpenImmersion (f₀.left ⁻¹ᵁ S₁).ι)
  letI : IsOpenImmersion bD₁.left := inferInstanceAs (IsOpenImmersion S₁.ι)
  letI : IsOpenImmersion aX₁.left := inferInstanceAs (IsOpenImmersion (q.left ⁻¹ᵁ V₀).ι)
  letI : IsOpenImmersion aW₁.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  let bC := bC₂ ≫ bC₁
  let bD := bD₂ ≫ bD₁
  let aX := aX₂ ≫ aX₁
  let aW := aW₂ ≫ aW₁
  letI : IsOpenImmersion bC.left := inferInstanceAs (IsOpenImmersion (bC₂.left ≫ bC₁.left))
  letI : IsOpenImmersion bD.left := inferInstanceAs (IsOpenImmersion (bD₂.left ≫ bD₁.left))
  letI : IsOpenImmersion aX.left := inferInstanceAs (IsOpenImmersion (aX₂.left ≫ aX₁.left))
  letI : IsOpenImmersion aW.left := inferInstanceAs (IsOpenImmersion (aW₂.left ≫ aW₁.left))
  have hcartI : IsPullback i₂.left bC.left aX.left i₀.left := hcartI₂.paste_vert hcartI₁
  have hcartJ : IsPullback j₂.left bD.left aW.left j₀.left := hcartJ₂.paste_vert hcartJ₁
  have hcartQ : IsPullback q₂.left aX.left aW.left q.left := hcartQ₂.paste_vert hcartQ₁
  have hambient : aX ≫ q = q₂ ≫ aW := Over.OverMorphism.ext hcartQ.w.symm
  letI : Nonempty C₂.left := ⟨cgen⟩
  letI : Nonempty D₂.left := ⟨f₂.left cgen⟩
  letI : Nonempty X₂.left := ⟨i₂.left cgen⟩
  letI : Nonempty W₂.left := ⟨q₂.left (i₂.left cgen)⟩
  letI : IsIntegral C₂.left := isIntegral_of_isOpenImmersion bC₂.left
  letI : IsIntegral D₂.left := isIntegral_of_isOpenImmersion bD₂.left
  letI : IsIntegral X₂.left := isIntegral_of_isOpenImmersion aX₂.left
  letI : IsIntegral W₂.left := isIntegral_of_isOpenImmersion aW₂.left
  letI : Smooth C₂.hom := hsC₂
  letI : Smooth D₂.hom := hsD₂
  letI : Smooth X₂.hom := hsX₂
  letI : Smooth W₂.hom := hsW₂
  letI : Smooth T.hom := hsT
  letI : SmoothOfRelativeDimension r T.hom := hdimT
  letI : SmoothOfRelativeDimension r C₂.hom := by
    rw [← Over.w bC₂]
    have hh : SmoothOfRelativeDimension (0 + r) (bC₂.left ≫ C₁.hom) := inferInstance
    simpa only [Nat.zero_add] using hh
  letI : SmoothOfRelativeDimension r D₂.hom := by
    rw [← Over.w bD₂]
    have hh : SmoothOfRelativeDimension (0 + r) (bD₂.left ≫ D₁.hom) := inferInstance
    simpa only [Nat.zero_add] using hh
  obtain ⟨hftC₂, hqcC₂, hsepC₂, _⟩ := s4_q3_finite_type_instances_of_open_immersion bC
  obtain ⟨hftD₂, hqcD₂, hsepD₂, _⟩ := s4_q3_finite_type_instances_of_open_immersion bD
  obtain ⟨hftX₂, hqcX₂, hsepX₂, _⟩ := s4_q3_finite_type_instances_of_open_immersion aX
  obtain ⟨hftW₂, hqcW₂, hsepW₂, _⟩ := s4_q3_finite_type_instances_of_open_immersion aW
  letI := hftC₂; letI := hqcC₂; letI := hsepC₂
  letI := hftD₂; letI := hqcD₂; letI := hsepD₂
  letI := hftX₂; letI := hqcX₂; letI := hsepX₂
  letI := hftW₂; letI := hqcW₂; letI := hsepW₂
  letI : IsClosedImmersion i₂.left := hiClosed₂
  letI : IsClosedImmersion j₂.left := hjClosed₂
  letI : IsFinite q₂.left := hfinite₂
  letI : Flat q₂.left := hflat₂
  letI : Smooth H.left := hsH
  letI : Smooth (q₂ ≫ H).left := hsQH
  letI : Etale (j₂ ≫ H).left := heJH
  letI : Etale (i₂ ≫ q₂ ≫ H).left := heIQH
  have hiw : i₂ ≫ aX = bC ≫ i₀ := Over.OverMorphism.ext hcartI.w
  have hjw : j₂ ≫ aW = bD ≫ j₀ := Over.OverMorphism.ext hcartJ.w
  have hfcompat : bC ≫ f₀ = f₂ ≫ bD := by
    apply (cancel_mono j₀).mp
    calc
      (bC ≫ f₀) ≫ j₀ = (bC ≫ i₀) ≫ q := by rw [Category.assoc, ← hsupport₀, ← Category.assoc]
      _ = (i₂ ≫ aX) ≫ q := by rw [hiw]
      _ = (i₂ ≫ q₂) ≫ aW := by rw [Category.assoc, hambient, ← Category.assoc]
      _ = (f₂ ≫ j₂) ≫ aW := by rw [hsq₂]
      _ = (f₂ ≫ bD) ≫ j₀ := by rw [Category.assoc, hjw, ← Category.assoc]
  have hlen : ∀ c : ComplexPoint C₂, pointFibreLength q.left
      (Point.map (i₂ ≫ aX) c).underlying = (m : ℕ∞) := by
    intro c
    have hcS₁ : f₀.left (bC.left c.underlying) ∈ S₁ := (bC₂.left c.underlying).property
    have hpointD : f₀.left (bC.left c.underlying) = bD.left (f₂.left c.underlying) :=
      congrArg (fun a : C₂.left ⟶ D₀.left => a c.underlying) (congrArg Over.Hom.left hfcompat)
    have hclosed : IsClosed ({(Point.map f₂ c).underlying} : Set D₂.left) :=
      ((pointEquivClosedPoint D₂.hom) ⟨(Point.map f₂ c).left, Over.w (Point.map f₂ c)⟩).2
    have hco := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := D₂.hom) (d := r) (Point.map f₂ c).underlying hclosed
    rw [Point.underlying_map] at hco
    have hcoD : Order.coheight (f₀.left (bC.left c.underlying)) = r := by
      rw [hpointD, coheight_eq_of_isOpenImmersion (x := f₂.left c.underlying) bD.left]
      exact hco
    have hregular : IsRegularLocalRing (D₀.left.presheaf.stalk (f₀.left (bC.left c.underlying))) :=
      s4_q3_regular_stalk_of_smooth_neighbourhood D₀.hom S₁ hsD₁ _ hcS₁
    have hlength := hgood (bC.left c.underlying) (hS₁₀ hcS₁) r hcoD hregular
    have hpointX : (Point.map (i₂ ≫ aX) c).underlying = I.subschemeι (bC.left c.underlying) := by
      rw [Point.underlying_map]
      exact congrArg (fun a : C₂.left ⟶ X.left => a c.underlying) hcartI.w
    rw [hpointX]
    exact hlength
  have hotherW : ∀ w : W₂.left, ∀ s ∈ z.support, s ≠ x → aW.left w ∉ closure ({s} : Set W.left) := by
    intro w s hs hsx
    exact havoid (aW.left w) (hV₀A (aW₂.left w).property).2 s hs hsx
  letI : IsDominant bC₁.left :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace bC₁.left bC₁.left.isOpenMap⟩
  have hgenOrig : bC.left cgen = genericPoint C₀.left := by
    change bC₁.left (bC₂.left cgen) = genericPoint C₀.left
    rw [hgen₂]
    exact s2_dominant_genericPoint bC₁.left
  have hpRange : p ∈ aX.left.opensRange := by
    refine ⟨i₂.left cgen, ?_⟩
    have hh := congrArg (fun a : C₂.left ⟶ X.left => a cgen) hcartI.w
    change aX.left (i₂.left cgen) = I.subschemeι (bC.left cgen) at hh
    exact hh.trans (by rw [hgenOrig, hgenI])
  obtain ⟨d, hd⟩ := Smooth.exists_smoothOfRelativeDimension X.hom
  letI : SmoothOfRelativeDimension d X.hom := hd
  refine ⟨aX.left.opensRange, hpRange, ?_⟩
  intro a haA haC hother
  obtain ⟨E, hflat, haE, hE, N, hNE, hNo, haN, hN⟩ :=
    s4_q3_retained_neighbourhood_local_normal_calculation X W C₂ D₂ X₂ W₂ T d r k p hp x
      aX aW bC bD i₂ j₂ f₂ q hq q₂ H hsq₂ hambient hcartI hcartJ
      γ z hγp hx m hcoeff hlen hotherW hS α hα a haA haC hother
  exact ⟨r, E, hflat, haE, hE, N, hNE, hNo, haN, hN⟩

end HodgeLean.Foundations.Program
