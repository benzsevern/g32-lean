import HodgeLean.Foundations.QuotientDuality.PersistenceTransportObstruction

/-! Iteration of unique eigenvector preimages along the actual total tower map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_eigen_preimage_comp
    {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (T : Module.End K U) (S : Module.End K V) (R : Module.End K W)
    (f : U →ₗ[K] V) (g : V →ₗ[K] W)
    (hf : ∀ u, f (T u) = S (f u)) (ζ : K)
    (hfl : ∀ v, S v = ζ • v → ∃! u, T u = ζ • u ∧ f u = v)
    (hgl : ∀ w, R w = ζ • w → ∃! v, S v = ζ • v ∧ g v = w)
    (w : W) (hw : R w = ζ • w) :
    ∃! u, T u = ζ • u ∧ (g.comp f) u = w := by
  obtain ⟨v, hv, hv_unique⟩ := hgl w hw
  obtain ⟨u, hu, hu_unique⟩ := hfl v hv.1
  refine ⟨u, ⟨hu.1, ?_⟩, ?_⟩
  · rw [LinearMap.comp_apply, hu.2, hv.2]
  · intro u' hu'
    apply hu_unique
    refine ⟨hu'.1, hv_unique (f u') ⟨?_, hu'.2⟩⟩
    rw [← hf, hu'.1, map_smul]

lemma persistence_tower_cohomology_preimages
    {r : ℕ} (K : Type) [Field K]
    (V : Fin (r + 1) → Over (Spec ↧ℂ)) (X : Over (Spec ↧ℂ))
    (e : V 0 ≅ X) (w : ∀ i : Fin r, V i.succ ⟶ V i.castSucc)
    (d : ∀ i, V i ⟶ V i) (d₀ : X ⟶ X)
    (h₀ : d 0 ≫ e.hom = e.hom ≫ d₀)
    (hw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (n : ℕ) (ζ : K)
    (hl : ∀ (i : Fin r) (v : Cohomology K (TopCat.of (ComplexPoint (V i.succ))) n),
      s2e_pullback K (d i.succ) n v = ζ • v →
      ∃! u : Cohomology K (TopCat.of (ComplexPoint (V i.castSucc))) n,
        s2e_pullback K (d i.castSucc) n u = ζ • u ∧
        s2e_pullback K (w i) n u = v) :
    ∀ (i : Fin (r + 1)) (v : Cohomology K (TopCat.of (ComplexPoint (V i))) n),
      s2e_pullback K (d i) n v = ζ • v →
      ∃! u : Cohomology K (TopCat.of (ComplexPoint X)) n,
        s2e_pullback K d₀ n u = ζ • u ∧
        s2e_pullback K (s2e_towerTotalMap V e.hom w i) n u = v := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro v hv
    have hleft : (s2e_pullback K e.hom n).comp (s2e_pullback K e.inv n) =
        LinearMap.id := by
      rw [← persistence_scheme_pullback_comp, e.hom_inv_id]
      exact cohomologyMap_id K _ n
    have hright : (s2e_pullback K e.inv n).comp (s2e_pullback K e.hom n) =
        LinearMap.id := by
      rw [← persistence_scheme_pullback_comp, e.inv_hom_id]
      exact cohomologyMap_id K _ n
    refine ⟨s2e_pullback K e.inv n v, ⟨?_, ?_⟩, ?_⟩
    · have heq : e.inv ≫ d 0 = d₀ ≫ e.inv := by
        apply (cancel_mono e.hom).mp
        simp only [Category.assoc, h₀, e.inv_hom_id_assoc, e.inv_hom_id,
          Category.comp_id]
      have he := congrArg (fun f => s2e_pullback K f n) heq
      rw [persistence_scheme_pullback_comp, persistence_scheme_pullback_comp] at he
      change ((s2e_pullback K d₀ n).comp (s2e_pullback K e.inv n)) v = _
      rw [← he, LinearMap.comp_apply, hv, map_smul]
    · exact LinearMap.congr_fun hleft v
    · intro u hu
      have he := congrArg (s2e_pullback K e.inv n) hu.2
      exact (LinearMap.congr_fun hright u).symm.trans he
  | succ i ih =>
    intro v hv
    rw [s2e_towerTotalMap_succ, persistence_scheme_pullback_comp]
    apply persistence_eigen_preimage_comp (s2e_pullback K d₀ n)
      (s2e_pullback K (d i.castSucc) n) (s2e_pullback K (d i.succ) n)
      (s2e_pullback K (s2e_towerTotalMap V e.hom w i.castSucc) n)
      (s2e_pullback K (w i) n) ?_ ζ ih (hl i) v hv
    intro u
    have he := congrArg (fun f => s2e_pullback K f n)
      (s2e_towerTotalMap_equivariant V e.hom w d d₀ h₀ hw i.castSucc)
    rw [persistence_scheme_pullback_comp, persistence_scheme_pullback_comp] at he
    exact (LinearMap.congr_fun he u).symm

lemma persistence_cohomology_iso_eigen_preimages
    (K : Type) [Field K] {X Y : Over (Spec ↧ℂ)} (e : X ≅ Y)
    (dX : X ⟶ X) (dY : Y ⟶ Y) (he : dX ≫ e.hom = e.hom ≫ dY)
    (n : ℕ) (ζ : K)
    (v : Cohomology K (TopCat.of (ComplexPoint X)) n)
    (hv : s2e_pullback K dX n v = ζ • v) :
    ∃! u : Cohomology K (TopCat.of (ComplexPoint Y)) n,
      s2e_pullback K dY n u = ζ • u ∧ s2e_pullback K e.hom n u = v := by
  exact persistence_tower_cohomology_preimages K (fun _ : Fin 1 => X) Y e
    (fun i : Fin 0 => i.elim0) (fun _ => dX) dY he
    (fun i : Fin 0 => i.elim0) n ζ (fun i : Fin 0 => i.elim0) 0 v hv

lemma persistence_tower_terminal_cohomology_preimages
    {r : ℕ} (K : Type) [Field K]
    (V : Fin (r + 1) → Over (Spec ↧ℂ)) (X W : Over (Spec ↧ℂ))
    (e₀ : V 0 ≅ X) (w : ∀ i : Fin r, V i.succ ⟶ V i.castSucc)
    (d : ∀ i, V i ⟶ V i) (d₀ : X ⟶ X)
    (h₀ : d 0 ≫ e₀.hom = e₀.hom ≫ d₀)
    (hw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (e : V (Fin.last r) ≅ W) (n : ℕ) (ζ : K)
    (hl : ∀ (i : Fin r) (v : Cohomology K (TopCat.of (ComplexPoint (V i.succ))) n),
      s2e_pullback K (d i.succ) n v = ζ • v →
      ∃! u : Cohomology K (TopCat.of (ComplexPoint (V i.castSucc))) n,
        s2e_pullback K (d i.castSucc) n u = ζ • u ∧
        s2e_pullback K (w i) n u = v)
    (v : Cohomology K (TopCat.of (ComplexPoint W)) n)
    (hv : s2e_pullback K (e.inv ≫ d (Fin.last r) ≫ e.hom) n v = ζ • v) :
    ∃! u : Cohomology K (TopCat.of (ComplexPoint X)) n,
      s2e_pullback K d₀ n u = ζ • u ∧
        s2e_pullback K (e.inv ≫ s2e_towerTotalMap V e₀.hom w (Fin.last r)) n u = v := by
  rw [persistence_scheme_pullback_comp]
  apply persistence_eigen_preimage_comp (s2e_pullback K d₀ n)
    (s2e_pullback K (d (Fin.last r)) n)
    (s2e_pullback K (e.inv ≫ d (Fin.last r) ≫ e.hom) n)
    (s2e_pullback K (s2e_towerTotalMap V e₀.hom w (Fin.last r)) n)
    (s2e_pullback K e.inv n) ?_ ζ
    (persistence_tower_cohomology_preimages K V X e₀ w d d₀ h₀ hw n ζ hl (Fin.last r))
    (persistence_cohomology_iso_eigen_preimages K e.symm _ _ (by
      change (e.inv ≫ d (Fin.last r) ≫ e.hom) ≫ e.inv = e.inv ≫ d (Fin.last r)
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]) n ζ) v hv
  intro u
  have he := congrArg (fun f => s2e_pullback K f n)
    (s2e_towerTotalMap_equivariant V e₀.hom w d d₀ h₀ hw (Fin.last r))
  rw [persistence_scheme_pullback_comp, persistence_scheme_pullback_comp] at he
  exact (LinearMap.congr_fun he u).symm

end HodgeLean.Foundations.QuotientDuality
