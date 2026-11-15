import HodgeLean.Foundations.Program.SchoenTransferQ3OpenSmoothSliceNormalization
import HodgeLean.Foundations.Program.SchoenTransferQ3PrimeAnalyticSupport
import HodgeLean.Foundations.Program.SchoenTransferQ3OpenDimensions
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentOpenDimensions
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

/-! Original local normalization from the actual retained support neighbourhood. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
open AlgebraicTopology.Singular HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- The actual retained neighbourhood and its unreduced length calculate
the original pulled class at every isolated component point in that neighbourhood. -/
theorem s4_q3_retained_neighbourhood_local_normal_calculation
    (X W C D X' W' T : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral C.left] [IsIntegral D.left] [IsIntegral X'.left] [IsIntegral W'.left]
    [Smooth C.hom] [Smooth D.hom] [Smooth X'.hom] [Smooth W'.hom] [Smooth T.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom]
    [QuasiCompact D.hom] [IsSeparated D.hom]
    [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [QuasiCompact W'.hom] [IsSeparated W'.hom]
    (d r k : ℕ) [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension r C.hom] [SmoothOfRelativeDimension r D.hom]
    [SmoothOfRelativeDimension r T.hom]
    (p : X.left) (hp : Order.coheight p = k) (t : W.left)
    (aX : X' ⟶ X) (aW : W' ⟶ W) [IsOpenImmersion aX.left] [IsOpenImmersion aW.left]
    (bC : C ⟶ Over.mk ((ccm3_primeIdeal X.left p).subschemeι ≫ X.hom))
    (bD : D ⟶ Over.mk ((ccm3_primeIdeal W.left t).subschemeι ≫ W.hom))
    [IsOpenImmersion bC.left] [IsOpenImmersion bD.left]
    (i : C ⟶ X') (j : D ⟶ W') [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (f : C ⟶ D) (q : X ⟶ W) [IsFinite q.left] (hq : IsOpenMap q.left)
    (q' : X' ⟶ W') [IsFinite q'.left] [Flat q'.left] (h : W' ⟶ T)
    [Smooth h.left] [Smooth (q' ≫ h).left]
    [Etale (j ≫ h).left] [Etale (i ≫ q' ≫ h).left]
    (hsquare : i ≫ q' = f ≫ j) (hambient : aX ≫ q = q' ≫ aW)
    (hcartC : IsPullback i.left bC.left aX.left (ccm3_primeIdeal X.left p).subschemeι)
    (hcartD : IsPullback j.left bD.left aW.left (ccm3_primeIdeal W.left t).subschemeι)
    (γ : AlgebraicCycle X.left ℚ) (δ : AlgebraicCycle W.left ℚ)
    (hγp : p ∈ γ.support) (hδt : t ∈ δ.support) (m : ℕ)
    (hcoeff : γ p = δ t * (m : ℚ))
    (hlen : ∀ c : ComplexPoint C, pointFibreLength q.left
      (Point.map (i ≫ aX) c).underlying = (m : ℕ∞))
    (hotherW : ∀ w : W'.left, ∀ s ∈ δ.support, s ≠ t →
      aW.left w ∉ closure ({s} : Set W.left))
    (hS : ∀ x, Point.map q x ∈ a3b4_cycleSupport W.hom δ → x ∈ a3b4_cycleSupport X.hom γ)
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
      (a3b4_cycleSupport W.hom δ)ᶜ) (2 * k))
    (hα : a3b4_IsCycleClass W.hom δ k α)
    (x : ComplexPoint X) (hxA : x.underlying ∈ Set.range aX.left)
    (hxC : x.underlying ∈ closure ({p} : Set X.left))
    (hotherX : ∀ s ∈ γ.support, s ≠ p → x.underlying ∉ closure ({s} : Set X.left)) :
    ∃ (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
      (hflat : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0),
      x ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
      ∃ (N : Set (ComplexPoint X)) (hNe : N ⊆ e.source), IsOpen N ∧ x ∈ N ∧
        relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap N (a3b4_cycleSupport X.hom γ))
          (relativeCohomologyMap ℚ (2 * k)
            (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
              (a3b4_cycleSupport X.hom γ) (a3b4_cycleSupport W.hom δ) hS) α) =
        a3b4_multiplicity X.hom γ x • chartNormalProjectionCoclass (Fin r → ℂ) k e
          (a3b4_cycleSupport X.hom γ) hflat N hNe := by
  obtain ⟨ZX, sX, rfl⟩ := Over.mk_surjective X
  obtain ⟨ZW, sW, rfl⟩ := Over.mk_surjective W
  let X : Over (Spec ↧ℂ) := Over.mk sX
  let W : Over (Spec ↧ℂ) := Over.mk sW
  let C₀ : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal X.left p).subschemeι ≫ X.hom)
  let D₀ : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal W.left t).subschemeι ≫ W.hom)
  let i₀ : C₀ ⟶ X := Over.homMk (ccm3_primeIdeal X.left p).subschemeι rfl
  let j₀ : D₀ ⟶ W := Over.homMk (ccm3_primeIdeal W.left t).subschemeι rfl
  have hRangeC₀ : Set.range (Point.map i₀) = Point.underlying ⁻¹' closure ({p} : Set X.left) :=
    s4_q3_prime_component_complex_range X p
  have hRangeD₀ : Set.range (Point.map j₀) = Point.underlying ⁻¹' closure ({t} : Set W.left) :=
    s4_q3_prime_component_complex_range W t
  have hRangeI : Set.range (Point.map i) =
      Point.map aX ⁻¹' (Point.underlying ⁻¹' closure ({p} : Set X.left)) := by
    rw [← hRangeC₀]
    exact (s4_q3_cartesian_support_complex_range i bC aX i₀ hcartC).symm
  have hRangeJ : Set.range (Point.map j) =
      Point.map aW ⁻¹' (Point.underlying ⁻¹' closure ({t} : Set W.left)) := by
    rw [← hRangeD₀]
    exact (s4_q3_cartesian_support_complex_range j bD aW j₀ hcartD).symm
  have hxRange : x ∈ Set.range (Point.map i₀) := by rw [hRangeC₀]; exact hxC
  obtain ⟨z₀, hz₀⟩ := hxRange
  obtain ⟨x', hx'⟩ := s0_open_immersion_lift_complex_point aX x hxA
  obtain ⟨c, hic, _⟩ := s4_q3_cartesian_support_point_lift i bC aX i₀ hcartC
    x' z₀ (hx'.trans hz₀.symm)
  have hmarked : Point.map (i ≫ aX) c = x := by
    rw [Point.map_comp_apply, hic, hx']
  have hw : i ≫ aX ≫ q = f ≫ j ≫ aW := by
    rw [hambient, ← Category.assoc, hsquare, Category.assoc]
  have himage : Point.map (j ≫ aW) (Point.map f c) = Point.map q x := by
    calc
      _ = Point.map (f ≫ j ≫ aW) c := (Point.map_comp_apply _ _ _).symm
      _ = Point.map (i ≫ aX ≫ q) c := congrArg (fun a => Point.map a c) hw.symm
      _ = Point.map q (Point.map (i ≫ aX) c) := by rw [← Category.assoc, Point.map_comp_apply]
      _ = _ := by rw [hmarked]
  have hyC : (Point.map q x).underlying ∈ closure ({t} : Set W.left) := by
    rw [← himage, Point.map_comp_apply]
    change Point.map j (Point.map f c) ∈ Point.map aW ⁻¹' (Point.underlying ⁻¹' closure ({t} : Set W.left))
    rw [← hRangeJ]
    exact Set.mem_range_self _
  have hotherY : ∀ s ∈ δ.support, s ≠ t → (Point.map q x).underlying ∉ closure ({s} : Set W.left) := by
    intro s hs hst
    rw [← himage, Point.underlying_map, Point.underlying_map]
    exact hotherW (j.left (f.left c.underlying)) s hs hst
  have hmX := a3b4a_classMultiplicity_eq_component X.hom γ p hγp x hxC hotherX
  have hmW := a3b4a_classMultiplicity_eq_component W.hom δ t hδt (Point.map q x) hyC hotherY
  obtain ⟨OX₀, _, hxOX₀, hOX₀⟩ := a3b4a_classSupport_local_eq_component
    X.hom γ p hγp x hotherX ⊤ (by trivial)
  obtain ⟨OW₀, _, hyOW₀, hOW₀⟩ := a3b4a_classSupport_local_eq_component
    W.hom δ t hδt (Point.map q x) hotherY ⊤ (by trivial)
  change Opens (ComplexPoint X) at OX₀
  change Opens (ComplexPoint W) at OW₀
  let OX := Point.map aX ⁻¹' (OX₀ : Set (ComplexPoint X))
  let OW := Point.map aW ⁻¹' (OW₀ : Set (ComplexPoint W))
  have hOX : IsOpen OX := OX₀.isOpen.preimage (Point.continuous_map aX)
  have hOW : IsOpen OW := OW₀.isOpen.preimage (Point.continuous_map aW)
  have hxOX : Point.map i c ∈ OX := by
    change Point.map aX (Point.map i c) ∈ OX₀
    rw [← Point.map_comp_apply, hmarked]
    exact hxOX₀
  have hyOW : Point.map j (Point.map f c) ∈ OW := by
    change Point.map aW (Point.map j (Point.map f c)) ∈ OW₀
    rw [← Point.map_comp_apply, himage]
    exact hyOW₀
  have hγlocal : ∀ y ∈ OX, Point.map aX y ∈ a3b4_cycleSupport X.hom γ ↔ y ∈ Set.range (Point.map i) := by
    intro y hy
    rw [hRangeI]
    exact hOX₀ (Point.map aX y) hy
  have hδlocal : ∀ y ∈ OW, Point.map aW y ∈ a3b4_cycleSupport W.hom δ ↔ y ∈ Set.range (Point.map j) := by
    intro y hy
    rw [hRangeJ]
    exact hOW₀ (Point.map aW y) hy
  letI : SmoothOfRelativeDimension d X'.hom := by
    rw [← Over.w aX]
    have hh : SmoothOfRelativeDimension (0 + d) (aX.left ≫ X.hom) := inferInstance
    simpa only [Nat.zero_add] using hh
  obtain ⟨e, he⟩ := Smooth.exists_smoothOfRelativeDimension W'.hom
  letI : SmoothOfRelativeDimension e W'.hom := he
  have hqraw : aX.left ≫ q.left = q'.left ≫ aW.left := congrArg Over.Hom.left hambient
  have hopenq' := s4_q3_isOpenMap_of_ambient_open_square aX.left aW.left q.left q'.left hqraw hq
  have hde : d = e := s4_q3_relativeDimensions_eq_of_open_quasiFinite d e q' hopenq' x'
  subst e
  have hr : r = d - k := s4_q3_open_component_relativeDimension_eq X d k p hp r bC c
  have hk : k ≤ d := by
    have hh := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := d) p
    rw [hp] at hh
    exact_mod_cast hh
  have hdiff : d - r = k := by omega
  subst k
  obtain ⟨E, hfE, hxE, hE, N, hNE, hNo, hxN, hN⟩ :=
    s4_q3_open_smooth_tangential_supported_pullback X' W' X W C D T aX aW q
      i j f q' h r d c hsquare hambient γ δ OX OW hOX hOW hxOX hyOW
      hγlocal hδlocal hS α hα
  rw [hmarked] at hxE hxN hN
  have hlenx : pointFibreLength q.left x.underlying = (m : ℕ∞) := by
    rw [← hmarked]
    exact hlen c
  rw [hmW, hlenx, ENat.toNat_natCast, ← hcoeff] at hN
  refine ⟨E, hfE, hxE, hE, N, hNE, hNo, hxN, ?_⟩
  rw [hmX]
  exact hN

end HodgeLean.Foundations.Program
