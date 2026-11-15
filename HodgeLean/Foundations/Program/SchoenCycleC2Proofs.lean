import HodgeLean.Foundations.Program.SchoenCycleC2RetainedConormalHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2RetainedCoheightHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1
import HodgeLean.Foundations.Program.SchoenCyclePushDefs
import HodgeLean.Foundations.Program.SchoenCycleC2DeckTransportHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ComponentClassHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2NormalizedSumHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2LinearHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2NeighbourhoodHelpers

/-! # C2 supported component classes
Implication from an actual branch-free component orbit and its smooth
neighbourhood to locally normalized rational supported classes and their
linear orbit map. The ambient scheme may be singular away from the orbit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

theorem s2e_chain_component_regular_codimension_aux
    (S : g32p_Supplier) (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m)
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ)
    (d₀ : W₀ ⟶ W₀) (hd₀ : d₀ ≫ β₀ = β₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    [∀ i, IsProjective (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i))
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (horder : ∀ i, (End.of (d i)) ^ S.m = 1)
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (eC : C ≃ₜ ComplexPoint C₀) (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hjC : Function.Bijective (homPullback jC 1))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)) ⟶ B (Fin.last r))
    (hℓ : IsClosedImmersion ℓ.left)
    (havoid : ∀ t, Disjoint (Set.range ℓ.left) (D (Fin.last r) t).support)
    (W : Over (Spec ↧ℂ))
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W) (hι : IsClosedImmersion ι.left)
    (hproj : ι ≫ (eWr.inv ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))) =
      eQ.hom ≫ ℓ) :
    let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
    ∀ t : Fin S.m,
      (∃ U : W.left.Opens,
        Set.range (ι ≫ (End.of δ ^ t.val).asHom).left ⊆ U ∧
        Smooth (U.ι ≫ W.hom)) ∧
      (∀ x : Q.left, ∃ U : Q.left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict
          (s2c_conormal (ι ≫ (End.of δ ^ t.val).asHom).left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin P.k) :
            U.toScheme.Modules))) ∧
      (∀ x ∈ (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).support,
        Order.coheight x = P.k) := by
  let : IsClosedImmersion ℓ.left := hℓ
  obtain ⟨U, hU, _, he⟩ :=
    s2e_chain_cover_etale_near_slice S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eWr.symm P.k ℓ havoid
  let β := eWr.inv ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
  let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
  have hδβ : δ ≫ β = β := by
    dsimp only [δ, β]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hd]
  dsimp only
  intro t
  refine ⟨?_, ?_⟩
  · apply s2e_orbit_smooth_neighbourhood_of_etale ι δ β hδβ U
    · rw [hproj]
      rintro _ ⟨x, rfl⟩
      exact hU ⟨eQ.hom.left x, rfl⟩
    · exact he
  · constructor
    · exact s2e_retained_component_conormal_frames S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder P.k hselected ℓ hℓ havoid W eWr Q eQ ι hι hproj t
    · exact s2e_retained_component_coheight S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus ℓ hℓ havoid W eWr Q eQ ι hι hproj t

theorem s2e_chain_component_supported_class_aux
    (Q W : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k) :
    ∃ c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k,
      a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c := by
  exact s2e_componentCycle_normalized_class_of_smooth_open ι U hU hsm k hcodim

theorem s2e_chain_supported_class_deck_transport_aux
    (Q W : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (δ : W ⟶ W) [IsIso δ]
    (k : ℕ) (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (c' : s2e_supportedClass W (s2e_componentCycle (ι ≫ δ) ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (hc' : a3b4_IsCycleClass W.hom (s2e_componentCycle (ι ≫ δ) ℚ) k c') :
    s2e_classToAbsolute W (s2e_componentCycle (ι ≫ δ) ℚ) k c' =
      s2e_pullback ℚ (inv δ) (2 * k)
        (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) := by
  exact s2e_componentCycle_absolute_deck_transport ι δ k U hU hsm hcodim c c' hc hc'

theorem s2e_chain_orbit_class_linear_aux
    (Q W : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (k m : ℕ)
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left))
    (hsm : ∀ t : Fin m, ∃ U : W.left.Opens,
      Set.range (ι ≫ (End.of δ ^ t.val).asHom).left ⊆ U ∧ Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ t : Fin m,
      ∀ x ∈ (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).support,
        Order.coheight x = k)
    (c : ∀ t : Fin m,
      s2e_supportedClass W (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k)
    (hc : ∀ t : Fin m, a3b4_IsCycleClass W.hom
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t)) :
    ∃ cl : (Fin m → ℚ) →ₗ[ℚ]
        AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k),
      (∀ a : Fin m → ℚ, cl a = ∑ t : Fin m, a t •
        s2e_classToAbsolute W (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t)) ∧
      (∀ t : Fin m, cl (Pi.single t 1) =
        s2e_classToAbsolute W (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t)) ∧
      (∀ a : Fin m → ℚ,
        let γ := s2e_rationalOrbitCycle ι δ m a
        (∀ x ∈ γ.support, Order.coheight x = k) ∧
        ∃ b : s2e_supportedClass W γ k,
          a3b4_IsCycleClass W.hom γ k b ∧ s2e_classToAbsolute W γ k b = cl a) := by
  let v := fun t : Fin m => s2e_classToAbsolute W
    (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t)
  refine ⟨s2e_orbitLinearMap v, fun _ => rfl, s2e_orbitLinearMap_single v, ?_⟩
  intro a
  refine ⟨s2e_rationalOrbitCycle_coheight ι δ k m hcodim a, ?_⟩
  exact s2e_rationalOrbitCycle_normalized_sum ι δ k m himm hdisj c hc a

theorem s2e_transformed_cycle_aux
    (S : g32p_Supplier) (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m)
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ)
    (d₀ : W₀ ⟶ W₀) (hd₀ : d₀ ≫ β₀ = β₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    [∀ i, IsProjective (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i))
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (horder : ∀ i, (End.of (d i)) ^ S.m = 1)
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (eC : C ≃ₜ ComplexPoint C₀) (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hjC : Function.Bijective (homPullback jC 1))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)) ⟶ B (Fin.last r))
    (hℓ : IsClosedImmersion ℓ.left)
    (havoid : ∀ t, Disjoint (Set.range ℓ.left) (D (Fin.last r) t).support)
    (W : Over (Spec ↧ℂ))
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W) :
    let β := eWr.inv ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
    let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
    ∃ (hft : LocallyOfFiniteType W.hom) (hqc : QuasiCompact W.hom)
      (hsep : IsSeparated W.hom),
    letI := hft
    letI := hqc
    letI := hsep
    ∃ (Q : Over (Spec ↧ℂ)) (hQ : IsIntegral Q.left),
    letI := hQ
    ∃ (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
      (ι : Q ⟶ W),
      IsClosedImmersion ι.left ∧ ι ≫ β = eQ.hom ≫ ℓ ∧
      (∀ t : Fin S.m, IsClosedImmersion
        (ι ≫ (End.of δ ^ t.val).asHom).left) ∧
      (∀ s t : Fin S.m, s ≠ t → Disjoint
        (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
        (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left)) ∧
      (β.left ⁻¹' Set.range ℓ.left =
        ⋃ t : Fin S.m, Set.range (ι ≫ (End.of δ ^ t.val).asHom).left) ∧
      ∃ cl : (Fin S.m → ℚ) →ₗ[ℚ]
        AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * P.k),
        (∀ t : Fin S.m, ∃ c, a3b4_IsCycleClass W.hom
          (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) P.k c ∧
          s2e_classToAbsolute W
            (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) P.k c =
              cl (Pi.single t 1)) ∧
        (∀ a : Fin S.m → ℚ,
          let γ := s2e_rationalOrbitCycle ι δ S.m a
          (∀ x ∈ γ.support, Order.coheight x = P.k) ∧
          ∃ c, a3b4_IsCycleClass W.hom γ P.k c ∧ s2e_classToAbsolute W γ P.k c = cl a) := by
  obtain ⟨_, hft, hqc, hsep, _⟩ :=
    s2e_chain_final_cover_finite_type S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eWr.symm
  let := hft
  let := hqc
  let := hsep
  let : IsClosedImmersion ℓ.left := hℓ
  obtain ⟨Q, eQ, ι, hι, hproj, himm, hdisj, hexhaust⟩ :=
    s2e_chain_component_orbit S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eWr.symm P.k ℓ havoid
  have hPPIntegral : IsIntegral
      (Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))).left :=
    s0_complex_projective_integral P.k
  have hPPSmooth : Smooth
      (Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))).hom :=
    s0_projective_space_smooth P.k (Spec ↧ℂ)
  have hQIntegral : IsIntegral Q.left := IsIntegral.of_isIso eQ.inv.left
  have hQSmooth : Smooth Q.hom := by
    rw [← Over.w eQ.hom]
    infer_instance
  have hgeometry := s2e_chain_component_regular_codimension_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus ℓ hℓ havoid W eWr Q eQ ι hι hproj
  let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
  have hclasses : ∀ t : Fin S.m,
      ∃ c : s2e_supportedClass W (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) P.k,
        a3b4_IsCycleClass W.hom
          (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) P.k c := by
    intro t
    obtain ⟨U, hU, hsm⟩ := (hgeometry t).1
    let : IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left := himm t
    exact s2e_chain_component_supported_class_aux Q W
      (ι ≫ (End.of δ ^ t.val).asHom) P.k U hU hsm (hgeometry t).2.2
  choose c hc using hclasses
  obtain ⟨cl, hsum, hbasis, hcycles⟩ := s2e_chain_orbit_class_linear_aux Q W ι δ P.k S.m
    himm hdisj (fun t => (hgeometry t).1) (fun t => (hgeometry t).2.2) c hc
  refine ⟨hft, hqc, hsep, Q, hQIntegral, eQ, ι, hι, hproj, himm, hdisj,
    ?_, cl, ?_, hcycles⟩
  · ext w
    simpa only [Set.mem_preimage, Set.mem_iUnion, Iso.symm_hom, Iso.symm_inv] using hexhaust w
  · intro t
    exact ⟨c t, hc t, (hbasis t).symm⟩

end HodgeLean.Foundations.Program
