import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRational

noncomputable section

namespace HodgeLean.Foundations.Program

theorem b6m_divide_incidence_relation {F E : Type*} (left right : E → F)
    (c : F →₀ ℤ) (z : E → ℤ) (n : ℤ) (hn : n ≠ 0)
    (h : ∀ e, c (right e) - c (left e) = n * z e) :
    ∃ q : F →₀ ℤ, ∀ e, q (right e) - q (left e) = z e := by
  refine ⟨c.mapRange (fun a ↦ a / n) (Int.zero_ediv n), ?_⟩
  intro e
  simp only [Finsupp.mapRange_apply]
  rw [← Int.sub_ediv_of_dvd_sub (show n ∣ c (right e) - c (left e) from ⟨z e, h e⟩), h e]
  exact Int.mul_ediv_cancel_left (z e) hn

theorem b6m_incidence_range_saturated {F E : Type*} (left right : E → F)
    (d : (F →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ))
    (hd : ∀ c e, d c e = c (right e) - c (left e))
    (n : ℤ) (hn : n ≠ 0) (z : E →₀ ℤ) (hz : n • z ∈ LinearMap.range d) :
    z ∈ LinearMap.range d := by
  obtain ⟨c, hc⟩ := hz
  have h (e : E) : c (right e) - c (left e) = n * z e := by
    rw [← hd, hc]
    simp only [Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨q, hq⟩ := b6m_divide_incidence_relation left right c z n hn h
  refine ⟨q, ?_⟩
  ext e
  exact (hd q e).trans (hq e)

theorem b6m_incidence_cokernel_torsionFree {F E : Type*} (left right : E → F)
    (d : (F →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ))
    (hd : ∀ c e, d c e = c (right e) - c (left e)) :
    Module.IsTorsionFree ℤ ((E →₀ ℤ) ⧸ LinearMap.range d) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  obtain ⟨z, rfl⟩ := (LinearMap.range d).mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply b6m_incidence_range_saturated left right d hd n hn z
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact ((LinearMap.range d).mkQ.map_smul n z).trans hx

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
theorem b6m_homology_torsionFree_of_saturated (R : Type) [CommRing R] [IsDomain R]
    (S : ShortComplex (ModuleCat.{0} R))
    (hsat : ∀ (n : R), n ≠ 0 → ∀ z : S.X₂,
      n • z ∈ LinearMap.range S.f.hom → z ∈ LinearMap.range S.f.hom) :
    Module.IsTorsionFree R S.homology := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  obtain ⟨z, rfl⟩ := S.moduleCatHomologyClass_surjective x
  apply (b6m_homologyClass_zero_iff R S z).mpr
  apply hsat n hn z.1
  apply (b6m_homologyClass_zero_iff R S (n • z)).mp
  exact (S.moduleCatHomologyClass.map_smul n z).trans hx

set_option backward.isDefEq.respectTransparency false in
theorem b6m_incidence_model_homology_torsionFree {F E : Type}
    (S : ShortComplex (ModuleCat.{0} ℤ)) (left right : E → F)
    (faces : S.X₁ ≃ₗ[ℤ] (F →₀ ℤ)) (edges : S.X₂ ≃ₗ[ℤ] (E →₀ ℤ))
    (hd : ∀ c e, edges (S.f.hom c) e = faces c (right e) - faces c (left e)) :
    Module.IsTorsionFree ℤ S.homology := by
  apply b6m_homology_torsionFree_of_saturated ℤ S
  intro n hn z hz
  obtain ⟨c, hc⟩ := hz
  have h (e : E) : faces c (right e) - faces c (left e) = n * edges z e := by
    rw [← hd, hc]
    exact congrArg (fun a : E →₀ ℤ ↦ a e) (edges.map_smul' n z)
  obtain ⟨q, hq⟩ := b6m_divide_incidence_relation left right (faces c) (edges z) n hn h
  refine ⟨faces.symm q, edges.injective ?_⟩
  ext e
  rw [hd, faces.apply_symm_apply]
  exact hq e

theorem b6m_incidence_cycle_lift_mod_int {F E : Type*} (left right : E → F)
    (d : (F →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ))
    (hd : ∀ c e, d c e = c (right e) - c (left e))
    (n : ℤ) (hn : n ≠ 0) (c : F →₀ ℤ) (hc : ∀ e, n ∣ d c e) :
    ∃ w : F →₀ ℤ, d w = 0 ∧ ∃ q : F →₀ ℤ, c - w = n • q := by
  let z : E →₀ ℤ := (d c).mapRange (fun a ↦ a / n) (Int.zero_ediv n)
  have hz : n • z = d c := by
    ext e
    change n * (d c e / n) = d c e
    exact Int.mul_ediv_cancel' (hc e)
  obtain ⟨q, hq⟩ := b6m_incidence_range_saturated left right d hd n hn z ⟨c, hz.symm⟩
  refine ⟨c - n • q, ?_, q, ?_⟩
  · rw [map_sub, map_smul, hq, hz, sub_self]
  · abel

open scoped Manifold ContDiff

theorem b6m_period_comparison_of_incidence_model (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] {F E : Type} (S : ShortComplex (ModuleCat.{0} ℤ))
    (left right : E → F) (faces : S.X₁ ≃ₗ[ℤ] (F →₀ ℤ))
    (edges : S.X₂ ≃ₗ[ℤ] (E →₀ ℤ))
    (hd : ∀ c e, edges (S.f.hom c) e = faces c (right e) - faces c (left e))
    (j : b6m_H1 C →ₗ[ℤ] S.homology) (hj : Function.Injective j) :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ := by
  letI := b6m_incidence_model_homology_torsionFree S left right faces edges hd
  letI : Module.IsTorsionFree ℤ (b6m_H1 C) :=
    Function.Injective.moduleIsTorsionFree j hj (fun n x ↦ j.map_smul' n x)
  exact b6m_period_comparison_of_torsionFree C

end HodgeLean.Foundations.Program
