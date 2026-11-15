import HodgeLean.Foundations.Program.G32Native.ZeroPairFibres
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist

/-! # Zero-pair component on the retained quotient
Native consumer: SchoenTransferJ2NativeInput.lean:413–424 (U03–U04).
Finite cover descent and zero-pair étaleness remain explicit inputs.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained zero-pair cover supplies the native component orbit. -/
theorem g32n_zeroPairComponent
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ i, Point.map p (eY z) = Point.map p (eY (y i)))
    (hr : r = 0)
    (h : ℕ) (hh : 0 < h + 1)
    (q : g3_power Y (h + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q = q)
    (hq : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ A),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W ⟶ A, q ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ A),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ A, γ ≫ u = f)
    (β : W ⟶ B) [IsFinite β.left] (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
    (hEtale : Etale β.left)
    (k : ℕ)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : IsClosedImmersion ℓ.left) :
    let PP : Over (Spec ↧ℂ) := Over.mk
      (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    ∃ (Q : Over (Spec ↧ℂ)) (hQ : IsIntegral Q.left)
      (hQs : Smooth Q.hom) (hQp : IsProjective Q.hom),
      let := hQ
      let := hQs
      let := hQp
      ∃ (eQ : Q ≅ PP) (ι : Q ⟶ W),
        IsClosedImmersion ι.left ∧ ι ≫ β = eQ.hom ≫ ℓ ∧
        (∀ s t : Fin S.m, s ≠ t → Disjoint
          (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
          (Set.range (ι ≫ (End.of d ^ t.val).asHom).left)) ∧
        (β.left ⁻¹' Set.range ℓ.left =
          ⋃ t : Fin S.m, Set.range (ι ≫ (End.of d ^ t.val).asHom).left) := by
  let PP : Over (Spec ↧ℂ) := Over.mk
    (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  haveI : IsIntegral PP.left := HodgeLean.Adapters.IntersectionProductScaf_projective_integral k
  haveI : Smooth PP.hom := HodgeLean.Adapters.IntersectionProductScaf_projective_smooth k
  haveI : LocallyOfFiniteType PP.hom := inferInstance
  haveI : IsClosedImmersion ℓ.left := hℓ
  haveI : Etale β.left := hEtale
  have hfibre := g32n_zeroPairFibres S Y Z W B a e ha1 hamul p hp hpsurj hporbit
    C eY hpointAction r σ y hbranch hr h hh q hqsurj hqinv hq γ hγsurj hγinv hγ
    β hβ d hd hgenerator
  have hpoints : ∀ x : ComplexPoint PP, ∃ z : ComplexPoint W,
      Point.map β z = Point.map ℓ x := by
    intro x
    obtain ⟨_, z, hz, _, _⟩ := hfibre (Point.map ℓ x)
    exact ⟨z, hz⟩
  haveI : Surjective (pullback.snd β.left ℓ.left) :=
    s2e_c1_pullback_surjective_of_slice_points W B PP β ℓ hpoints
  obtain ⟨x⟩ := s2t_nonempty_complexPoints PP
  have horder := (hfibre (Point.map ℓ x)).1
  obtain ⟨ι, hι, hsquare, _, hdis, hex⟩ :=
    s2e_c1_component_orbit_of_slice_fibres k S.m (NeZero.ne S.m) W B β ℓ d hd horder
      (fun x => (hfibre (Point.map ℓ x)).2)
  refine ⟨PP, inferInstance, inferInstance, inferInstance, Iso.refl PP, ι, hι, ?_, hdis, ?_⟩
  · simpa only [Iso.refl_hom, Category.id_comp] using hsquare
  · ext w
    simpa only [Set.mem_preimage, Set.mem_iUnion] using hex w

end HodgeLean.Foundations.Program
