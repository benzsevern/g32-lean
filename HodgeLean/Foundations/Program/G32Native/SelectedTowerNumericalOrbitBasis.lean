import HodgeLean.Foundations.Program.G32Native.ProjectiveModelInstances
import HodgeLean.Foundations.Program.G32Native.TopHyperplanePower
import Mathlib.CategoryTheory.Conj
import HodgeLean.Foundations.Program.G32Native.QuotientPrimitiveRank
import HodgeLean.Foundations.Program.G32Native.TowerOrbitLinear
import HodgeLean.Foundations.Program.G32Native.SelectedFinalPrimitiveNonzero
import HodgeLean.Foundations.Program.G32Native.SelectedTowerOrbitBasis
import HodgeLean.Foundations.Program.SchoenCycleI2Chain
import HodgeLean.Foundations.Program.SchoenTransferR2PullbackPowers

/-! # T13 from a numerical self-intersection on the retained final component -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- T13 from a nonzero numerical self-intersection on the same final component.
The numerical hypothesis is retained explicitly. No normal-bundle identification is inferred
from projectivity or from the disjointness of the component orbit. -/
theorem selected_tower_numerical_orbit_basis
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
    (hExceptionalPrimitive : ∀ i : Fin r,
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage β j))) n,
        s2b_preimageCohomologyDeck β j (d i.succ) (hd i.succ) n v = ζ • v → v = 0)
    (W : Over (Spec ↧ℂ)) [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom]
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ W₀)
    (hf₀ : f 0 = eW.hom)
    (hf : ∀ i : Fin r, f i.succ = w i ≫ f i.castSucc)
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) P.k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) P.k c)
    (hdis : ∀ s t : Fin S.m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) ^ t.val).asHom).left))
    (degree : AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint Q)) (2 * P.k) →ₗ[ℚ] ℚ)
    (hdegree : degree (s2e_normalEuler ι P.k c) ≠ 0)
    (G : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * P.k) →ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * P.k))
    (hGF : ∀ v, G (s2e_pullback ℚ (eWr.inv ≫ f (Fin.last r)) (2 * P.k) v) = v)
    (hG : ∀ v, G (s2e_pullback ℚ (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) (2 * P.k) v) =
      s2e_pullback ℚ d₀ (2 * P.k) (G v)) :
    let H₀ := AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * P.k)
    ∃ (a : Fin (Nat.totient S.m) → Fin S.m → ℚ)
      (v : Fin (Nat.totient S.m) → H₀),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval (s2e_pullback ℚ d₀ (2 * P.k)) (Polynomial.cyclotomic S.m ℚ)) ∧
      (∀ j, v j = G (∑ t : Fin S.m, a j t •
        s2e_pullback ℚ ((End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) ^
          (S.m - t.val)).asHom) (2 * P.k) (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) P.k c))) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        (∃ u : ℂ ⊗[ℚ] H₀, u ≠ 0 ∧
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] H₀,
          (s2e_pullback ℚ d₀ (2 * P.k)).baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient S.m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j)) := by
  have hnonzero := selected_final_primitive_nonzero S P r B W₀.left.functionField
    η d (horder (Fin.last r)) W eWr Q ι c hdis degree hdegree
  exact selected_tower_orbit_basis S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus hExceptionalPrimitive W eWr f hf₀ hf (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) P.k c) G hGF hG hnonzero

#print axioms selected_tower_numerical_orbit_basis
end HodgeLean.Foundations.Program.G32Native
