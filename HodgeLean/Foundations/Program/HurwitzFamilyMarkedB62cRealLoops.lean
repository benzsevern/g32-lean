import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRealSurface
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cPeriodTransport

noncomputable section

namespace HodgeLean.Foundations.Program

open scoped Manifold ContDiff

theorem b6m_velocity_matched_real {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    (e : C → D) (γ : b3_SmoothLoop ℂ C) (δ : b3_SmoothLoop ℂ D)
    (h : ∀ t : ℝ, e (γ.1 t) = δ.1 t) (s : ℝ)
    (hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s)) :
    b3_velocity ℂ D δ.1 s =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) (b3_velocity ℂ C γ.1 s) := by
  have H := mfderiv_comp_apply s hd ((γ.2.2 s).mdifferentiableAt one_ne_zero) 1
  rw [show e ∘ γ.1 = δ.1 from funext h] at H
  exact H

set_option backward.isDefEq.respectTransparency false in
theorem b6m_crossing_sign_matched_real {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    (e : C → D) (γ δ : b3_SmoothLoop ℂ C) (γ' δ' : b3_SmoothLoop ℂ D)
    (hγ : ∀ t : ℝ, e (γ.1 t) = γ'.1 t) (hδ : ∀ t : ℝ, e (δ.1 t) = δ'.1 t)
    (s t : ℝ) (hst : γ.1 s = δ.1 t)
    (hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s))
    (ho : ∀ v w : ℂ, SignType.sign (b3_orient ℂ
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) w)) = SignType.sign (b3_orient ℂ v w)) :
    SignType.sign (b3_orient ℂ (b3_velocity ℂ D γ'.1 s) (b3_velocity ℂ D δ'.1 t)) =
      SignType.sign (b3_orient ℂ (b3_velocity ℂ C γ.1 s) (b3_velocity ℂ C δ.1 t)) := by
  rw [b6m_velocity_matched_real e γ γ' hγ s hd,
    b6m_velocity_matched_real e δ δ' hδ t (hst ▸ hd), ← hst]
  exact ho _ _

theorem b6m_transverse_matched_real {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    (e : C ≃ₜ D) (γ δ : b3_SmoothLoop ℂ C) (γ' δ' : b3_SmoothLoop ℂ D)
    (hγ : ∀ t : ℝ, e (γ.1 t) = γ'.1 t) (hδ : ∀ t : ℝ, e (δ.1 t) = δ'.1 t)
    (hd : ∀ s t, γ.1 s = δ.1 t → MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s))
    (ho : ∀ s t, γ.1 s = δ.1 t → ∀ v w : ℂ, SignType.sign (b3_orient ℂ
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) w)) = SignType.sign (b3_orient ℂ v w))
    (htr : b3_Transverse ℂ γ δ) : b3_Transverse ℂ γ' δ' := by
  intro s t hst hz
  have hst' : γ.1 s = δ.1 t := e.injective ((hγ s).trans (hst.trans (hδ t).symm))
  have H := b6m_crossing_sign_matched_real e γ δ γ' δ' hγ hδ s t hst'
    (hd s t hst') (ho s t hst')
  rw [hz, sign_zero] at H
  exact htr s t hst' (sign_eq_zero_iff.mp H.symm)

theorem b6m_intersection_matched_real {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    (e : C ≃ₜ D) (γ δ : b3_SmoothLoop ℂ C) (γ' δ' : b3_SmoothLoop ℂ D)
    (hγ : ∀ t : ℝ, e (γ.1 t) = γ'.1 t) (hδ : ∀ t : ℝ, e (δ.1 t) = δ'.1 t)
    (hd : ∀ s t, γ.1 s = δ.1 t → MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s))
    (ho : ∀ s t, γ.1 s = δ.1 t → ∀ v w : ℂ, SignType.sign (b3_orient ℂ
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) w)) = SignType.sign (b3_orient ℂ v w)) :
    b3_intersection ℂ γ' δ' = b3_intersection ℂ γ δ := by
  have hc : b3_crossings ℂ γ' δ' = b3_crossings ℂ γ δ := by
    ext p
    change (p.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ γ'.1 p.1 = δ'.1 p.2) ↔ _
    rw [← hγ p.1, ← hδ p.2, e.injective.eq_iff]
    rfl
  unfold b3_intersection
  rw [hc]
  apply finsum_mem_congr rfl
  intro p hp
  exact congrArg (fun s : SignType ↦ (s : ℤ))
    (b6m_crossing_sign_matched_real e γ δ γ' δ' hγ hδ p.1 p.2 hp.2.2
      (hd p.1 p.2 hp.2.2) (ho p.1 p.2 hp.2.2))

theorem b6m_pairing_matched_real {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (e : C ≃ₜ D) (γ δ : b3_SmoothLoop ℂ C) (γ' δ' : b3_SmoothLoop ℂ D)
    (hγ : ∀ t : ℝ, e (γ.1 t) = γ'.1 t) (hδ : ∀ t : ℝ, e (δ.1 t) = δ'.1 t)
    (hd : ∀ s t, γ.1 s = δ.1 t → MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s))
    (ho : ∀ s t, γ.1 s = δ.1 t → ∀ v w : ℂ, SignType.sign (b3_orient ℂ
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (γ.1 s) w)) = SignType.sign (b3_orient ℂ v w))
    (htr : b3_Transverse ℂ γ δ)
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ η : b3_SmoothLoop ℂ C, P (b6m_loopClass C η) = b3_latticePeriod ℂ C η)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (hS : ∀ η : b3_SmoothLoop ℂ D, S (b6m_loopClass D η) = b3_latticePeriod ℂ D η)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    R (S (b6m_H1Equiv e (b6m_loopClass C γ))) (S (b6m_H1Equiv e (b6m_loopClass C δ))) =
      Q (P (b6m_loopClass C γ)) (P (b6m_loopClass C δ)) := by
  rw [b6m_H1Equiv_loopClass e γ γ' hγ, b6m_H1Equiv_loopClass e δ δ' hδ,
    hS γ', hS δ', hP γ, hP δ,
    hR γ' δ' (b6m_transverse_matched_real e γ δ γ' δ' hγ hδ hd ho htr), hQ γ δ htr]
  exact b6m_intersection_matched_real e γ δ γ' δ' hγ hδ hd ho

end HodgeLean.Foundations.Program
