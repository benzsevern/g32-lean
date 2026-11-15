import HodgeLean.Foundations.WitnessSelection.RetainedHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers
import HodgeLean.Foundations.WitnessSelection.GeometricProofs
import HodgeLean.Foundations.WitnessSelection.Retention
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # Compatible slice and supported basis reselection

All retained morphisms and the original rational primitive basis remain explicit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.WitnessSelection

/-- Genericity and the S2 primitive spanning construction select a compatible slice
for the fixed basis, including zero pairs. Old representatives alone do not
supply this existence argument. Reselect the actual admissible slice and its component orbit while retaining
the same tower, deck maps, primitive basis and original normalized witnesses.
The new representatives have that same absolute basis equation and smooth generic
support on the original cover. No positive pair-count premise is imposed.
Source: Schoen (1988), Lemmas 2.3–2.6 and Theorem 2.0, pp. 14–18;
s4-chain-contract.md:285–303; s2e-chain-contract.md:412–414. -/
theorem compatible_basis_generic_existence_aux
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
    (Wf : Over (Spec ↧ℂ))
    (eFinal : Wf ≅ s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)))
    (φ : Wf ⟶ W₀) [QuasiCompact φ.left]
    (hφ : eFinal.hom ≫ s2e_towerTotalMap
      (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r) = φ)
    (δ : Wf ⟶ Wf) (hδ : δ ≫ eFinal.hom = eFinal.hom ≫ d (Fin.last r))
    (PP : Over (Spec ↧ℂ))
    (ePP : PP ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
    (ℓold : ∀ i, PP ⟶ B i)
    (hℓold :
      (∀ i, IsClosedImmersion (ℓold i).left) ∧
      (∀ i : Fin r, ℓold i.succ ≫ b i = ℓold i.castSucc) ∧
      (∀ i : Fin r, (ℓold i.succ).left.ker =
        s2c_strictTransform (b i).left (ℓold i.castSucc).left.ker
          (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            D i.castSucc ⟨2 * i.val + 1, by omega⟩)) ∧
      (∀ i : Fin r,
        (D 0 ⟨2 * i.val, by omega⟩).comap (ℓold 0).left =
          (D 0 ⟨2 * i.val + 1, by omega⟩).comap (ℓold 0).left) ∧
      (∀ T : Finset (Fin r),
        let I := T.sup (fun i =>
          (D 0 ⟨2 * i.val, by omega⟩).comap (ℓold 0).left)
        (T.card ≤ P.k → Nonempty (s2c_subscheme PP I ≅
          Over.mk (ProjectiveSpace.toBase (Fin (P.k - T.card + 1)) (Spec ↧ℂ)))) ∧
        (P.k < T.card → IsEmpty (s2c_subscheme PP I).left) ∧
        (∀ x : (s2c_subscheme PP I).left,
          ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
                U.toScheme.Modules)))) ∧
      (∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
        Disjoint (Set.range (ℓold i).left) (D i t).support))
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (ι : Q ⟶ Wf) [IsClosedImmersion ι.left]
    (π : Q ⟶ PP) [IsFinite π.left]
    (hπ : Function.Surjective π.left)
    (hcomponent : ι ≫ eFinal.hom ≫
      s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)) = π ≫ ℓold (Fin.last r))
    (bprim : Module.Basis (Fin (Nat.totient S.m)) ℚ
      (LinearMap.ker (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k))
        (Polynomial.cyclotomic S.m ℚ))))
    (aold : Fin (Nat.totient S.m) → Fin S.m → ℚ)
    (αold : ∀ j, s2e_supportedClass W₀
      (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ S.m (aold j))) P.k)
    (hnormalized : ∀ j, a3b4_IsCycleClass W₀.hom
      (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ S.m (aold j))) P.k (αold j))
    (habsolute : ∀ j, s2e_classToAbsolute W₀
      (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ S.m (aold j))) P.k (αold j) =
        (bprim j : AlgebraicTopology.Singular.Cohomology ℚ
          (TopCat.of (ComplexPoint W₀)) (2 * P.k))) :
    ∃ ℓ : ∀ i, PP ⟶ B i,
      (∀ t : Fin (2 * r), ∀ x : PP.left, IsGenericPoint x Set.univ →
        (ℓ 0).left x ∉ (D 0 t).support) ∧
      (∀ i, IsClosedImmersion (ℓ i).left) ∧
      (∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc) ∧
      (∀ i : Fin r, (ℓ i.succ).left.ker =
        s2c_strictTransform (b i).left (ℓ i.castSucc).left.ker
          (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            D i.castSucc ⟨2 * i.val + 1, by omega⟩)) ∧
      (∀ i : Fin r,
        (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left =
          (D 0 ⟨2 * i.val + 1, by omega⟩).comap (ℓ 0).left) ∧
      (∀ T : Finset (Fin r),
        let I := T.sup (fun i =>
          (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left)
        (T.card ≤ P.k → Nonempty (s2c_subscheme PP I ≅
          Over.mk (ProjectiveSpace.toBase (Fin (P.k - T.card + 1)) (Spec ↧ℂ)))) ∧
        (P.k < T.card → IsEmpty (s2c_subscheme PP I).left) ∧
        (∀ x : (s2c_subscheme PP I).left,
          ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
                U.toScheme.Modules)))) ∧
      (∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
        Disjoint (Set.range (ℓ i).left) (D i t).support) ∧
      ∃ (Q' : Over (Spec ↧ℂ)) (hQ' : IsIntegral Q'.left),
        letI := hQ'
        ∃ (ι' : Q' ⟶ Wf) (π' : Q' ⟶ PP)
          (anew : Fin (Nat.totient S.m) → Fin S.m → ℚ),
          IsClosedImmersion ι'.left ∧ IsFinite π'.left ∧ Function.Surjective π'.left ∧
          (ι' ≫ eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)) =
            π' ≫ ℓ (Fin.last r)) ∧
          (∃ (U : W₀.left.Opens),
            Smooth (U.ι ≫ W₀.hom) ∧
            (∀ t : Fin S.m, φ.left ((ι' ≫ (End.of δ ^ t.val).asHom).left
              (genericPoint Q'.left)) ∈ U)) ∧
          ∃ αnew : ∀ j, s2e_supportedClass W₀
            (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι' δ S.m (anew j))) P.k,
            (∀ j, a3b4_IsCycleClass W₀.hom
              (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι' δ S.m (anew j))) P.k
                (αnew j)) ∧
            (∀ j, s2e_classToAbsolute W₀
              (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι' δ S.m (anew j))) P.k
                (αnew j) = (bprim j : AlgebraicTopology.Singular.Cohomology ℚ
                  (TopCat.of (ComplexPoint W₀)) (2 * P.k))) := by
  haveI : IsIntegral PP.left := by
    haveI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))).left := by
      change IsIntegral (ProjectiveSpace (Fin (P.k + 1)) (Spec ↧ℂ))
      exact s0_complex_projective_integral P.k
    exact IsIntegral.of_isIso ePP.inv.left
  have hav : ∀ t : Fin (2 * r), ∀ x : PP.left, IsGenericPoint x Set.univ →
      (ℓold 0).left x ∉ (D 0 t).support := by
    apply paired_generic_avoidance PP P.k r (by omega) ePP (B 0).left
      (ℓold 0).left (D 0) hℓold.2.2.2.1
    intro i
    have hi := (hℓold.2.2.2.2.1 {i}).1 (by simp; omega)
    simp only [Finset.card_singleton, Finset.sup_singleton] at hi
    exact hi
  refine ⟨ℓold, hav, hℓold.1, hℓold.2.1, hℓold.2.2.1, hℓold.2.2.2.1,
    hℓold.2.2.2.2.1, hℓold.2.2.2.2.2, Q, inferInstance, ι, π, aold,
    inferInstance, inferInstance, hπ, hcomponent, ?_, αold, hnormalized, habsolute⟩
  have hmap : ∀ i, s2e_towerTotalMap
      (fun j => s2b_normalizationOver (B j) (η j)) eW.hom w i ≫ β₀ =
      s2b_normalizationMap (B i) (η i) ≫ s2e_towerTotalMap B e₀.hom b i := by
    intro i
    induction i using Fin.induction with
    | zero => exact heW
    | succ j ih =>
      rw [s2e_towerTotalMap_succ, s2e_towerTotalMap_succ, Category.assoc, ih,
        ← Category.assoc, normalization_transition_square _ _ _ _ (b j) (hη j) (w j) (hw j),
        Category.assoc]
  have hslice : ∀ i, ℓold i ≫ s2e_towerTotalMap B e₀.hom b i = ℓold 0 ≫ e₀.hom := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih => rw [s2e_towerTotalMap_succ, ← Category.assoc, hℓold.2.1 j, ih]
  have hc : ι ≫ φ ≫ β₀ = π ≫ ℓold 0 ≫ e₀.hom := by
    rw [← hφ, Category.assoc, hmap]
    calc
      _ = π ≫ ℓold (Fin.last r) ≫ s2e_towerTotalMap B e₀.hom b (Fin.last r) := by
        simpa only [Category.assoc] using congrArg
          (fun f : Q ⟶ B (Fin.last r) => f ≫ s2e_towerTotalMap B e₀.hom b (Fin.last r)) hcomponent
      _ = _ := by rw [hslice]
  have hdeck : δ ≫ φ = φ ≫ d₀ := by
    rw [← hφ, ← Category.assoc, hδ, Category.assoc,
      s2e_towerTotalMap_equivariant _ _ _ d d₀ hdinit hdw, Category.assoc]
  let marks := fun t : Fin (g32p_exponents S).length => Point.map p₀ (eY (y t))
  let U : B₀.left.Opens :=
    ⟨⋂ t, ((s2c_branchIdeal Z B₀ h γ (marks t)).support : Set B₀.left)ᶜ,
      isOpen_iInter_of_finite fun t => (s2c_branchIdeal Z B₀ h γ (marks t)).support.isClosed.isOpen_compl⟩
  have hdorder : End.of d₀ ^ S.m = 1 := by
    have hp := s2e_c1_transport_generator_order eW.symm (d 0) S.m (horder 0)
    have heq : eW.inv ≫ d 0 ≫ eW.hom = d₀ := by rw [hdinit, eW.inv_hom_id_assoc]
    change End.of (eW.inv ≫ d 0 ≫ eW.hom) ^ S.m = 1 at hp
    rwa [heq] at hp
  obtain ⟨het, hsm⟩ := initial_cover_smooth_open S Y Z W₀ B₀ a e ha1 hamul hinj
    p₀ hp₀ hpsurj hporbit (rsq_Quot S.χ.ker C) (Fin (g32p_exponents S).length)
    eY.toEquiv hpointAction marks hbranch h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ
    β₀ hβ₀ d₀ hd₀ hdorder hgenerator U (fun t x hx => Set.mem_iInter.mp hx t)
  haveI : Etale (β₀.left ∣_ U) := het
  have hπgen : IsGenericPoint (π.left (genericPoint Q.left)) Set.univ := by
    simpa only [Set.image_univ, Set.range_eq_univ.mpr hπ, closure_univ] using
      (genericPoint_spec Q.left).image π.left.continuous
  have hgen : (φ ≫ β₀).left (ι.left (genericPoint Q.left)) ∈ U := by
    apply Set.mem_iInter.mpr
    intro t hm
    have havt := hav (σ.symm t) _ hπgen
    apply havt
    rw [hD₀, Scheme.IdealSheafData.support_comap]
    have heq := congrArg (fun f : Q ⟶ B₀ => f.left (genericPoint Q.left)) hc
    change β₀.left (φ.left (ι.left (genericPoint Q.left))) =
      e₀.hom.left ((ℓold 0).left (π.left (genericPoint Q.left))) at heq
    change e₀.hom.left ((ℓold 0).left (π.left (genericPoint Q.left))) ∈
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ (σ.symm t)))))).support
    rw [σ.apply_symm_apply, ← heq]
    exact hm
  have hinv : δ ≫ (φ ≫ β₀) = φ ≫ β₀ := by
    rw [← Category.assoc, hdeck, Category.assoc, hd₀]
  refine ⟨β₀.left ⁻¹ᵁ U, hsm, ?_⟩
  exact (residual_generic_smooth ι δ φ β₀ (φ ≫ β₀) rfl hinv U hgen S.m (fun _ => 0)).1


/-- Reselect the actual admissible slice and its component orbit while retaining
the same tower, deck maps, primitive basis and original normalized witnesses.
The new representatives have that same absolute basis equation and smooth generic
support on the original cover. No positive pair-count premise is imposed.
Source: Schoen (1988), Lemmas 2.3–2.6 and Theorem 2.0, pp. 14–18;
s4-chain-contract.md:285–303; s2e-chain-contract.md:412–414. -/
theorem slice_basis_reselection_aux
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
    (Wf : Over (Spec ↧ℂ))
    (eFinal : Wf ≅ s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)))
    (φ : Wf ⟶ W₀) [QuasiCompact φ.left]
    (hφ : eFinal.hom ≫ s2e_towerTotalMap
      (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r) = φ)
    (δ : Wf ⟶ Wf) (hδ : δ ≫ eFinal.hom = eFinal.hom ≫ d (Fin.last r))
    (PP : Over (Spec ↧ℂ))
    (ePP : PP ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
    (ℓold : ∀ i, PP ⟶ B i)
    (hℓold :
      (∀ i, IsClosedImmersion (ℓold i).left) ∧
      (∀ i : Fin r, ℓold i.succ ≫ b i = ℓold i.castSucc) ∧
      (∀ i : Fin r, (ℓold i.succ).left.ker =
        s2c_strictTransform (b i).left (ℓold i.castSucc).left.ker
          (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            D i.castSucc ⟨2 * i.val + 1, by omega⟩)) ∧
      (∀ i : Fin r,
        (D 0 ⟨2 * i.val, by omega⟩).comap (ℓold 0).left =
          (D 0 ⟨2 * i.val + 1, by omega⟩).comap (ℓold 0).left) ∧
      (∀ T : Finset (Fin r),
        let I := T.sup (fun i =>
          (D 0 ⟨2 * i.val, by omega⟩).comap (ℓold 0).left)
        (T.card ≤ P.k → Nonempty (s2c_subscheme PP I ≅
          Over.mk (ProjectiveSpace.toBase (Fin (P.k - T.card + 1)) (Spec ↧ℂ)))) ∧
        (P.k < T.card → IsEmpty (s2c_subscheme PP I).left) ∧
        (∀ x : (s2c_subscheme PP I).left,
          ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
                U.toScheme.Modules)))) ∧
      (∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
        Disjoint (Set.range (ℓold i).left) (D i t).support))
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (ι : Q ⟶ Wf) [IsClosedImmersion ι.left]
    (π : Q ⟶ PP) [IsFinite π.left]
    (hπ : Function.Surjective π.left)
    (hcomponent : ι ≫ eFinal.hom ≫
      s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)) = π ≫ ℓold (Fin.last r))
    (bprim : Module.Basis (Fin (Nat.totient S.m)) ℚ
      (LinearMap.ker (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k))
        (Polynomial.cyclotomic S.m ℚ))))
    (aold : Fin (Nat.totient S.m) → Fin S.m → ℚ)
    (αold : ∀ j, s2e_supportedClass W₀
      (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ S.m (aold j))) P.k)
    (hnormalized : ∀ j, a3b4_IsCycleClass W₀.hom
      (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ S.m (aold j))) P.k (αold j))
    (habsolute : ∀ j, s2e_classToAbsolute W₀
      (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ S.m (aold j))) P.k (αold j) =
        (bprim j : AlgebraicTopology.Singular.Cohomology ℚ
          (TopCat.of (ComplexPoint W₀)) (2 * P.k))) :
    ∃ ℓ : ∀ i, PP ⟶ B i,
      (∀ t : Fin (2 * r), ∀ x : PP.left, IsGenericPoint x Set.univ →
        (ℓ 0).left x ∉ (D 0 t).support) ∧
      (∀ i, IsClosedImmersion (ℓ i).left) ∧
      (∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc) ∧
      (∀ i : Fin r, (ℓ i.succ).left.ker =
        s2c_strictTransform (b i).left (ℓ i.castSucc).left.ker
          (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            D i.castSucc ⟨2 * i.val + 1, by omega⟩)) ∧
      (∀ i : Fin r,
        (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left =
          (D 0 ⟨2 * i.val + 1, by omega⟩).comap (ℓ 0).left) ∧
      (∀ T : Finset (Fin r),
        let I := T.sup (fun i =>
          (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left)
        (T.card ≤ P.k → Nonempty (s2c_subscheme PP I ≅
          Over.mk (ProjectiveSpace.toBase (Fin (P.k - T.card + 1)) (Spec ↧ℂ)))) ∧
        (P.k < T.card → IsEmpty (s2c_subscheme PP I).left) ∧
        (∀ x : (s2c_subscheme PP I).left,
          ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
                U.toScheme.Modules)))) ∧
      (∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
        Disjoint (Set.range (ℓ i).left) (D i t).support) ∧
      ∃ (Q' : Over (Spec ↧ℂ)) (hQ' : IsIntegral Q'.left),
        letI := hQ'
        ∃ (ι' : Q' ⟶ Wf) (π' : Q' ⟶ PP)
          (anew : Fin (Nat.totient S.m) → Fin S.m → ℚ),
          IsClosedImmersion ι'.left ∧ IsFinite π'.left ∧ Function.Surjective π'.left ∧
          (ι' ≫ eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)) =
            π' ≫ ℓ (Fin.last r)) ∧
          (∃ (U : W₀.left.Opens),
            Smooth (U.ι ≫ W₀.hom) ∧
            (∀ t : Fin S.m, φ.left ((ι' ≫ (End.of δ ^ t.val).asHom).left
              (genericPoint Q'.left)) ∈ U)) ∧
          ∃ αnew : ∀ j, s2e_supportedClass W₀
            (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι' δ S.m (anew j))) P.k,
            (∀ j, a3b4_IsCycleClass W₀.hom
              (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι' δ S.m (anew j))) P.k
                (αnew j)) ∧
            (∀ j, s2e_classToAbsolute W₀
              (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι' δ S.m (anew j))) P.k
                (αnew j) = (bprim j : AlgebraicTopology.Singular.Cohomology ℚ
                  (TopCat.of (ComplexPoint W₀)) (2 * P.k))) ∧
            (∀ j x, x ∈ (a1p_pushforward φ.left
              (s2e_rationalOrbitCycle ι' δ S.m (anew j))).support →
              ∃ U : W₀.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W₀.hom)) := by
  obtain ⟨ℓ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, Q', hQ', hrest⟩ :=
    compatible_basis_generic_existence_aux
    S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus Wf eFinal φ hφ δ hδ PP ePP ℓold hℓold Q ι π hπ hcomponent bprim aold αold hnormalized habsolute

  letI := hQ'
  obtain ⟨ι', π', anew, hi, hp, hsurj, hcomp, hopen, αnew, hnorm, habs⟩ := hrest
  refine ⟨ℓ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, Q', hQ', ι', π', anew,
    hi, hp, hsurj, hcomp, hopen, αnew, hnorm, habs, ?_⟩
  obtain ⟨U, hU, hgeneric⟩ := hopen
  intro j x hx
  obtain ⟨t, rfl⟩ := s4_pushed_orbit_support ι' δ S.m (anew j) φ hx
  exact ⟨U, hgeneric t, hU⟩

end HodgeLean.WitnessSelection
