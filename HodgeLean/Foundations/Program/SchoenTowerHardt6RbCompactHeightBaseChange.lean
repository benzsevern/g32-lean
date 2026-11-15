import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbHeightLiftGraph
import Mathlib.Topology.Homeomorph.Lemmas

/-! Compact actual height carriers transport through an injective continuous Boolean base map. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_height_base_change {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β A) (hβinj : Set.InjOn β A)
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ A,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (F : s2v_t11b_Formula (n + 1)) (hF : IsCompact F.realize)
    (e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (he0 : ∀ p, e p 0 = p.2) (hes : ∀ p i, e p i.succ = p.1 i)
    (hbase : ∀ z ∈ F.realize, (e.symm z).1 ∈ A) :
    let φ := fun z => e (β (e.symm z).1, (e.symm z).2)
    ∃ h : F.realize ≃ₜ (φ '' F.realize), ∃ J : s2v_t11b_Formula ((n + 1) + (n + 1)),
      (∀ x, (h x).val = φ x.val) ∧
      (∀ z, z ∈ J.realize ↔ ∃ x : F.realize,
        (∀ i, z (Fin.castAdd (n + 1) i) = x.val i) ∧
        (∀ i, z (Fin.natAdd (n + 1) i) = (h x).val i)) := by
  classical
  intro φ
  letI : CompactSpace F.realize := isCompact_iff_compactSpace.mp hF
  have hc : Continuous (fun x : F.realize => φ x.val) :=
    e.continuous.comp ((hβ.comp_continuous (e.symm.continuous.comp continuous_subtype_val).fst
      (fun x => hbase x.val x.property)).prodMk (e.symm.continuous.comp continuous_subtype_val).snd)
  have hinj : Set.InjOn φ F.realize := by
    intro x hx y hy heq
    have hp := e.injective heq
    have hheight := congrArg Prod.snd hp
    have hbaseeq : β (e.symm x).1 = β (e.symm y).1 := congrArg Prod.fst hp
    apply e.symm.injective
    exact Prod.ext (hβinj (hbase x hx) (hbase y hy) hbaseeq) hheight
  let v := Equiv.Set.imageOfInjOn φ F.realize hinj
  let h : F.realize ≃ₜ (φ '' F.realize) :=
    Continuous.homeoOfEquivCompactToT2 (f := v) (hc.subtype_mk _)
  have hh (x : F.realize) : (h x).val = φ x.val := rfl
  have hcoords (x : EuclideanSpace ℝ (Fin (n + 1))) :
      (e.symm x).2 = x 0 ∧ (e.symm x).1 = WithLp.toLp 2 (fun i : Fin n => x i.succ) := by
    constructor
    · exact (he0 (e.symm x)).symm.trans (congrArg (fun z => z 0) (e.apply_symm_apply x))
    · ext i
      exact (hes (e.symm x) i).symm.trans (congrArg (fun z => z i.succ) (e.apply_symm_apply x))
  obtain ⟨R, hR⟩ := s2v_hardt6rb_height_lift_graph A β G hG
  refine ⟨h, R.inter (s2v_hardt1_rename (Fin.castAdd (n + 1)) F), hh, ?_⟩
  intro z
  change (z ∈ R.realize ∧ z ∈ (s2v_hardt1_rename (Fin.castAdd (n + 1)) F).realize) ↔ _
  rw [hR, s2v_hardt1_realize_rename]
  constructor
  · rintro ⟨⟨x, _, hx, ht, hb⟩, hFx⟩
    have heq : WithLp.toLp 2 (fun i => z (Fin.castAdd (n + 1) i)) = x := by ext i; exact hx i
    refine ⟨⟨x, heq ▸ hFx⟩, hx, ?_⟩
    intro i
    rw [hh]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ht.trans ((hcoords x).1.symm.trans (he0 (β (e.symm x).1, (e.symm x).2)).symm)
    · rw [hes, (hcoords x).2]
      exact hb j
  · rintro ⟨x, hx, hy⟩
    refine ⟨⟨x.val, (hcoords x.val).2 ▸ hbase x.val x.property, hx, ?_, ?_⟩, ?_⟩
    · rw [hy, hh, he0, (hcoords x.val).1]
    · intro i
      rw [hy, hh, hes, (hcoords x.val).2]
    · have heq : WithLp.toLp 2 (fun i => z (Fin.castAdd (n + 1) i)) = x.val := by ext i; exact hx i
      exact heq.symm ▸ x.property

end HodgeLean.Foundations.Program
