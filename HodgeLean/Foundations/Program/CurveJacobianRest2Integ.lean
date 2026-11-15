import HodgeLean.Foundations.Program.CurveJacobianRest2Cech

/-! # Track B3, lane Rest2: lifting cocycles through an additive covering

Let `π : V → J` be an additive covering map of abelian topological groups, `f : X → J`
continuous and `ℓ : V → ℂ` additive. Every singular simplex `σ` of `X` (a map from a standard
simplex, which is simply connected) has lifts of `f ∘ σ` through `π`, any two differing by a
constant (`b3Rest2_lift_sub_const`). The value of `b3Rest2_LI` on a `1`-simplex is
`ℓ(F(1) - F(0))` for a lift `F`; lifting a `2`-simplex and restricting to its faces gives the
cocycle relation (`b3Rest2_liftCocycle`). For the Abel–Jacobi map of a Riemann surface and the
period functional of a holomorphic form this is its integration cocycle.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter CategoryTheory
open scoped Topology Simplicial

namespace HodgeLean.Foundations.Program

open HodgeLean.Adapters

variable {V J : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
  [AddCommGroup J] [TopologicalSpace J] (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
  {X : Type} [TopologicalSpace X] (f : X → J) (hf : Continuous f) (ℓ : V →+ ℂ)
include hπ hf

theorem b3Rest2_exists_lift {n : ℕ} (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ F : C(Convexity.StdSimplex ℝ (Fin (n + 1)), V), ∀ s, π (F s) = f (σ s) := by
  obtain ⟨e₀, he₀⟩ := hπ.2 (f (σ (Convexity.StdSimplex.single 0)))
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hπ.1.existsUnique_continuousMap_lifts
    ((⟨f, hf⟩ : C(X, J)).comp σ) (Convexity.StdSimplex.single 0) e₀ he₀
  exact ⟨F, fun s ↦ congrFun hF s⟩

/-- **Two lifts of the same map differ by a constant.** -/
theorem b3Rest2_lift_sub_const {n : ℕ} (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X))
    (F F' : C(Convexity.StdSimplex ℝ (Fin (n + 1)), V))
    (hF : ∀ s, π (F s) = f (σ s)) (hF' : ∀ s, π (F' s) = f (σ s))
    (s t : Convexity.StdSimplex ℝ (Fin (n + 1))) : F' t - F' s = F t - F s := by
  set s₀ := Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 1))
  set c := F' s₀ - F s₀
  have hc : π c = 0 := by rw [map_sub, hF, hF', sub_self]
  let G : C(Convexity.StdSimplex ℝ (Fin (n + 1)), V) :=
    ⟨fun x ↦ F x + c, F.continuous.add continuous_const⟩
  have hG : ∀ x, π (G x) = f (σ x) := fun x ↦ by
    show π (F x + c) = _
    rw [map_add, hc, add_zero, hF]
  have huniq := hπ.1.existsUnique_continuousMap_lifts
    ((⟨f, hf⟩ : C(X, J)).comp σ) s₀ (F' s₀) (hF' s₀)
  have hGF' : G = F' := huniq.unique ⟨by simp [G, c], funext hG⟩ ⟨rfl, funext hF'⟩
  rw [← hGF']
  simp only [G, ContinuousMap.coe_mk]
  abel

/-- **The lifted value of a singular `1`-simplex**, `ℓ(F(1) - F(0))` for a lift `F` of `f ∘ σ`. -/
def b3Rest2_LI (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) : ℂ :=
  ℓ ((b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose
      (Convexity.StdSimplex.single 1) -
    (b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose
      (Convexity.StdSimplex.single 0))

theorem b3Rest2_LI_eq (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌)
    (F : C(Convexity.StdSimplex ℝ (Fin 2), V))
    (hF : ∀ s, π (F s) = f ((TopCat.of X).toSSetObjEquiv _ σ s)) :
    b3Rest2_LI π hπ f hf ℓ σ =
      ℓ (F (Convexity.StdSimplex.single 1) - F (Convexity.StdSimplex.single 0)) := by
  rw [b3Rest2_LI, b3Rest2_lift_sub_const π hπ f hf _ F
    (b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose hF
    (b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)).choose_spec]

theorem b3Rest2_LI_face (τ : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌)
    (H : C(Convexity.StdSimplex ℝ (Fin 3), V))
    (hH : ∀ s, π (H s) = f ((TopCat.of X).toSSetObjEquiv _ τ s)) (i : Fin 3) :
    b3Rest2_LI π hπ f hf ℓ ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) =
      ℓ (H (Convexity.StdSimplex.single (i.succAbove 1)) -
        H (Convexity.StdSimplex.single (i.succAbove 0))) := by
  rw [b3Rest2_LI_eq π hπ f hf ℓ _ (H.comp ⟨Convexity.StdSimplex.map i.succAbove,
    Convexity.StdSimplex.continuous_map (R := ℝ) i.succAbove⟩) (fun s ↦ ?_)]
  · show ℓ (H (Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.single 1)) -
      H (Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.single 0))) = _
    rw [Convexity.StdSimplex.map_single, Convexity.StdSimplex.map_single]
  · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hH]
    rfl

theorem b3Rest2_LI_cocycle (τ : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌) :
    b3Rest2_LI π hπ f hf ℓ ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) -
      b3Rest2_LI π hπ f hf ℓ ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) +
      b3Rest2_LI π hπ f hf ℓ ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) = 0 := by
  obtain ⟨H, hH⟩ := b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ τ)
  rw [b3Rest2_LI_face π hπ f hf ℓ τ H hH, b3Rest2_LI_face π hπ f hf ℓ τ H hH,
    b3Rest2_LI_face π hπ f hf ℓ τ H hH]
  have h10 : (1 : Fin 3).succAbove 0 = 0 := rfl
  have h11 : (1 : Fin 3).succAbove 1 = 2 := rfl
  have h20 : (2 : Fin 3).succAbove 0 = 0 := rfl
  have h21 : (2 : Fin 3).succAbove 1 = 1 := rfl
  have h00 : (0 : Fin 3).succAbove 0 = 1 := rfl
  have h01 : (0 : Fin 3).succAbove 1 = 2 := rfl
  rw [h10, h11, h20, h21, h00, h01, map_sub, map_sub, map_sub]
  ring

/-- **The lifted cocycle.** -/
def b3Rest2_liftCocycle :
    AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of X)) 1 :=
  ⟨simplexCochain ℂ _ 1 (b3Rest2_LI π hπ f hf ℓ), by
    refine LinearMap.mem_ker.2 (cochain_ext_simplex_b3Rest2 _ _ fun τ ↦ ?_)
    rw [AlgebraicTopology.Simplicial.coboundary_chainOfSimplex, LinearMap.zero_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, spec_simplexCochain_chainOfSimplex_aux,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.val_zero, Fin.val_one, Fin.val_two,
      Fin.val_succ, pow_zero, pow_one, one_smul, neg_one_sq, neg_smul, add_zero]
    linear_combination b3Rest2_LI_cocycle π hπ f hf ℓ τ⟩

theorem b3Rest2_liftCocycle_apply (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) :
    (b3Rest2_liftCocycle π hπ f hf ℓ).1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) =
      b3Rest2_LI π hπ f hf ℓ σ :=
  spec_simplexCochain_chainOfSimplex_aux ℂ _ 1 _ σ

/-- **The lifted cocycle on a loop**, through a lift of `f ∘ p` on `[0, 1]`. -/
theorem b3Rest2_liftCocycle_loop (p : C(UnitAddCircle, X)) (G : C(unitInterval, V))
    (hG : ∀ t, π (G t) = f (p ((t : ℝ) : UnitAddCircle))) :
    (b3Rest2_liftCocycle π hπ f hf ℓ).1
        (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex p)) = ℓ (G 1 - G 0) := by
  rw [b3Rest2_liftCocycle_apply, b3Rest2_LI_eq π hπ f hf ℓ _
    (G.comp ⟨Convexity.StdSimplex.homeomorphI, Convexity.StdSimplex.homeomorphI.continuous⟩)
    (fun s ↦ ?_)]
  · simp
  · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hG]
    rfl

omit hπ hf in
/-- **A continuous lift along a loop** from a continuous family `A ∘ Γ` of displacements. -/
theorem b3Rest2_exists_loop_lift_gen {W : Type} [TopologicalSpace W] (p : C(UnitAddCircle, X))
    (Γ : ℝ → W) (hΓ : Continuous Γ) (A : W → V) (hA : Continuous A) (v₀ : V)
    (hv₀ : π v₀ = f (p ((0 : ℝ) : UnitAddCircle)))
    (hrel : ∀ t : ℝ, π (A (Γ t)) = f (p (t : UnitAddCircle)) - f (p ((0 : ℝ) : UnitAddCircle))) :
    ∃ G : C(unitInterval, V), (∀ t : unitInterval, π (G t) = f (p ((t : ℝ) : UnitAddCircle))) ∧
      G 1 - G 0 = A (Γ 1) - A (Γ 0) := by
  refine ⟨⟨fun t ↦ v₀ + A (Γ t), continuous_const.add (hA.comp (hΓ.comp continuous_subtype_val))⟩,
    fun t ↦ ?_, ?_⟩
  · show π (v₀ + A (Γ t)) = _
    rw [map_add, hv₀, hrel]
    abel
  · show (v₀ + A (Γ ((1 : unitInterval) : ℝ))) - (v₀ + A (Γ ((0 : unitInterval) : ℝ))) = _
    simp

end HodgeLean.Foundations.Program
