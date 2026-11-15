import HodgeLean.Foundations.Program.SchoenCycleC1InitialCardHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1BranchComplementHelpers
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist

/-! # Measured initial cover fibres in every nonempty base open -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual initial quotient cover has a fibre of its specified degree
inside every nonempty base open, by the dense unmarked locus. -/
theorem s2e_c1_initial_measured_fibres
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (T I : Type*) [Finite I] [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i)
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
    (β : W ⟶ B) (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ S.m = 1)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
    (U : B.left.Opens) (hU : (U : Set B.left).Nonempty) :
    ∃ b : ComplexPoint B, b.underlying ∈ U ∧ Nat.card ((Point.map β) ⁻¹' {b}) = S.m := by
  obtain ⟨b₀, hb₀⟩ := s2e_c1_exists_initial_base_point_off_branches S Y Z B a ha1 hamul
    hinj p T I eY hpointAction marks hbranch h γ hγsurj hγinv hγ
  let V : B.left.Opens :=
    ⟨⋂ i : I, ((s2c_branchIdeal Z B h γ (marks i)).support : Set B.left)ᶜ,
      isOpen_iInter_of_finite fun i => (s2c_branchIdeal Z B h γ (marks i)).support.isClosed.isOpen_compl⟩
  have hV : (V : Set B.left).Nonempty := ⟨b₀.underlying, Set.mem_iInter.mpr hb₀⟩
  have hUV : ((V ⊓ U : B.left.Opens) : Set B.left).Nonempty := by
    simpa only [Opens.coe_inf, Set.inter_comm] using
      (V.isOpen.dense hV).inter_open_nonempty U U.isOpen hU
  let O := V ⊓ U
  letI : Nonempty O := Set.nonempty_coe_sort.mpr hUV
  haveI : Nonempty (openScheme B O).left := inferInstanceAs (Nonempty O.toScheme)
  haveI : LocallyOfFiniteType (openScheme B O).hom := by
    change LocallyOfFiniteType (O.ι ≫ B.hom)
    infer_instance
  obtain ⟨x⟩ := s2t_nonempty_complexPoints (openScheme B O)
  let b := Point.map (openInclusion B O) x
  have hb : b.underlying ∈ O := (openHomeomorph B O x).property
  refine ⟨b, hb.2, ?_⟩
  apply s2e_c1_initial_fibre_card_off_marks S Y Z W B a e ha1 hamul p hp hpsurj hporbit
    T I eY hpointAction marks hbranch h hh q hqsurj hqinv hq γ hγsurj hγinv hγ
    β hβ d hd horder hgenerator b
  exact Set.mem_iInter.mp hb.1

end HodgeLean.Foundations.Program
