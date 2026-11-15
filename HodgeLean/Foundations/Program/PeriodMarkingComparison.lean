import HodgeLean.Foundations.Program.PeriodMarkingLattice

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

theorem b64b_period_comparison (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t),
      P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (A : b63l_parameterLattice b C hC V hV t →ₗ[ℤ] b63l_parameterLattice b C hC V hV t)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV t x.val) :
    ∃ e : b63l_parameterLattice b C hC V hV t ≃ₗ[ℤ]
      b63l_periodLattice (b63l_parameterFibre b C V hV t),
      (∀ x, (e x).val = P x.val) ∧
      ∀ x, (e (A x)).val = b63d_periodOperator (b63l_parameterFibre b C V hV t) hG (e x).val := by
  classical
  let D := b63l_parameterFibre b C V hV t
  let L := b63l_parameterLattice b C hC V hV t
  obtain ⟨P', hP', _, e, he⟩ := b63l_period_image_comparison D hG
  have hPeq : P'.toLinearMap = P :=
    b6m_homology_linearMap_ext _ _ _ _ (fun γ => (hP' γ).trans (hP γ).symm)
  let e' : L ≃ₗ[ℤ] b63l_periodLattice D := e
  have hev (x : L) : (e' x).val = P x.val := by
    change (e x).val = _
    exact (he x).trans (DFunLike.congr_fun hPeq x.val)
  have hdeck (g : b4b_Group) (x : b6m_H1 D) :
      P (b63d_homologyAct D (fun g => (hG g).continuous) g x) =
        b4_latticeAct ℂ g (P x) := by
    let a := b4_actionHomeomorph hG g
    have hn := b6m_period_push_naturality a (hG g) P' hP' P' hP' x
    have ha : b3A_push a (hG g) = b4_latticeAct ℂ g :=
      b3A_pushforward_unique a (hG g) _ _
        (b3A_push_isPushforward a (hG g)) (b4_latticeAct_isPushforward hG g)
    rw [ha] at hn
    have hm : (b6m_H1Equiv a).toLinearMap =
        b63d_homologyAct D (fun g => (hG g).continuous) g := rfl
    have hh := hn.symm
    change P'.toLinearMap ((b6m_H1Equiv a).toLinearMap x) =
      b4_latticeAct ℂ g (P'.toLinearMap x) at hh
    rw [hm, hPeq] at hh
    exact hh
  have hc (x : b6m_H1 D) :
      P (b63d_centre b C hC V hV t x) = b4b_centreAct D hG (P x) := by
    simp only [b63d_centre, LinearMap.sum_apply, map_sum,
      b4b_centreAct, AddMonoidHom.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs
    · exact hdeck g x
    · simp only [LinearMap.zero_apply, map_zero, AddMonoidHom.zero_apply]
  have hPA (x : L) : P (A x).val = b63d_periodOperator D hG (P x.val) := by
    rw [hA x]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_add, b63d_periodOperator]
    change P x.val + P (2 • b63d_centre b C hC V hV t x.val) =
      P x.val + 2 • b4b_centreAct D hG (P x.val)
    congr 1
    calc
      P ((2 : ℕ) • b63d_centre b C hC V hV t x.val) =
          (2 : ℕ) • P (b63d_centre b C hC V hV t x.val) := map_nsmul P.toAddMonoidHom 2 _
      _ = (2 : ℕ) • b4b_centreAct D hG (P x.val) := congrArg ((2 : ℕ) • ·) (hc x.val)
  refine ⟨e', hev, fun x => ?_⟩
  exact (hev (A x)).trans ((hPA x).trans (congrArg (b63d_periodOperator D hG) (hev x).symm))

end HodgeLean.Foundations.Program
