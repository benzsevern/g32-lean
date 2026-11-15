import HodgeLean.Foundations.Program.SchoenTowerInvariantOrbitSelectors
import HodgeLean.Foundations.Program.SchoenTowerStabilizerTrace
import HodgeLean.Foundations.Program.SchoenTowerFixedAdicEquiv

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- Restricting the original action to a subgroup preserves scalar compatibility. -/
theorem s2t_subgroup_action_smulCommClass {K A G : Type*}
    [CommRing K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A] (H : Subgroup G) :
    letI := MulSemiringAction.compHom A H.subtype
    SMulCommClass H K A := by
  letI := MulSemiringAction.compHom A H.subtype
  constructor
  intro h r a
  exact smul_comm h.val r a

/-- The subgroup stabilizing an orbit factor preserves its actual ideal. -/
theorem s2t_orbitStabilizerIdeal_stable {A G : Type*}
    [CommRing A] [Group G] [MulSemiringAction G A] (q : Ideal A)
    (i : MulAction.orbit G q) (h : MulAction.stabilizer G i) (a : A)
    (ha : a ∈ (i : Ideal A)) : (h : G) • a ∈ (i : Ideal A) := by
  have hfix : (h : G) • (i : Ideal A) = (i : Ideal A) :=
    congrArg (fun j : MulAction.orbit G q => (j : Ideal A)) h.property
  have hm := Ideal.smul_mem_pointwise_smul (h : G) a (i : Ideal A) ha
  rwa [hfix] at hm

/-- Invariants of the actual completed orbit ring identify with stabilizer invariants
of the selected actual factor adic ring. -/
def s2t_completedOrbitStabilizerEquiv {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [IsNoetherianRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (i : MulAction.orbit G q) [Fintype (MulAction.stabilizer G i)] :
    let R₀ := FixedPoints.subalgebra K A G
    let M := (q.under R₀).map (algebraMap R₀ A)
    let H := MulAction.stabilizer G i
    let hM := s2t_extendedIdeal_stable (A := A) (G := G) (q.under R₀)
    let hq := s2t_orbitStabilizerIdeal_stable q i
    letI := MulSemiringAction.compHom A H.subtype
    letI := s2t_subgroup_action_smulCommClass (K := K) (A := A) H
    letI := s2t_adicAction M hM
    letI := s2t_adicAction_smulCommClass (R := K) M hM
    letI := s2t_adicAction (i : Ideal A) hq
    letI := s2t_adicAction_smulCommClass (R := K) (i : Ideal A) hq
    FixedPoints.subalgebra K (AdicCompletion M A) G ≃+*
      FixedPoints.subalgebra K (AdicCompletion (i : Ideal A) A) H := by
  classical
  let R₀ := FixedPoints.subalgebra K A G
  let M := (q.under R₀).map (algebraMap R₀ A)
  let H := MulAction.stabilizer G i
  let hM := s2t_extendedIdeal_stable (A := A) (G := G) (q.under R₀)
  let hq := s2t_orbitStabilizerIdeal_stable q i
  letI := MulSemiringAction.compHom A H.subtype
  letI := s2t_subgroup_action_smulCommClass (K := K) (A := A) H
  letI := s2t_adicAction M hM
  letI := s2t_adicAction_smulCommClass (R := K) M hM
  letI := s2t_adicAction (i : Ideal A) hq
  letI := s2t_adicAction_smulCommClass (R := K) (i : Ideal A) hq
  let hMi := s2t_extended_under_le_orbit (R := R₀) q i
  let F : AdicCompletion M A →ₐ[K] AdicCompletion (i : Ideal A) A :=
    { toRingHom := s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi
      commutes' := fun k => by
        change s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi
          (algebraMap K (AdicCompletion M A) k) = _
        rw [AdicCompletion.algebraMap_apply]
        change s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi
          (AdicCompletion.of M A (algebraMap K A k)) =
          AdicCompletion.of (i : Ideal A) A (algebraMap K A k)
        exact s2t_adicMap_of M (i : Ideal A) (RingHom.id A) hMi (algebraMap K A k) }
  have hsurj : Function.Surjective F := by
    intro c
    refine ⟨(s2t_invariantOrbitAdicEquiv (R := R₀) (G := G) q).symm (Pi.single i c), ?_⟩
    change s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi _ = c
    rw [← s2t_invariantOrbitAdicEquiv_apply (R := R₀) (G := G) q]
    change ((s2t_invariantOrbitAdicEquiv (R := R₀) (G := G) q)
      ((s2t_invariantOrbitAdicEquiv (R := R₀) (G := G) q).symm (Pi.single i c))) i = c
    rw [RingEquiv.apply_symm_apply]
    simp only [Pi.single_eq_same]
  have heq (h : H) (x : AdicCompletion M A) : F ((h : G) • x) = h • F x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ (i : Ideal A) n
      (s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi (s2t_adicActionHom M hM (h : G) x)) =
      AdicCompletion.evalₐ (i : Ideal A) n
        (s2t_adicActionHom (i : Ideal A) hq h (s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi x))
    rw [s2t_adicMap_eval, s2t_adicActionHom_eval M hM (h : G),
      s2t_adicActionHom_eval (i : Ideal A) hq h, s2t_adicMap_eval]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ M n x)
    rw [← ha]
    rfl
  let s := s2t_invariantOrbitSelector (R := R₀) q i
  have hcoord (g : G) : F (g • s) = if i = g • i then 1 else 0 := by
    change s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi
      (s2t_adicActionHom M hM g (s2t_invariantOrbitSelector (R := R₀) q i)) = _
    rw [s2t_invariantOrbitSelector_action]
    rw [← s2t_invariantOrbitAdicEquiv_apply (R := R₀) (G := G) q
      (s2t_invariantOrbitSelector (R := R₀) q (g • i)) i, s2t_invariantOrbitSelector_map]
  have hsel_in (g : G) (hg : g ∈ H) : F (g • s) = 1 := by
    have hgi : g • i = i := hg
    rw [hcoord, if_pos hgi.symm]
  have hsel_out (g : G) (hg : g ∉ H) : F (g • s) = 0 := by
    have hne : i ≠ g • i := fun h => hg h.symm
    rw [hcoord, if_neg hne]
  have hker (a : AdicCompletion M A) (ha : F a = 0) : s * a = 0 := by
    apply s2t_invariantOrbitSelector_mul_of_kernel (R := R₀) (G := G) q i a
    rw [s2t_invariantOrbitAdicEquiv_apply]
    exact ha
  have htrace : ∑ g : G, g • s = (Fintype.card H : K) • (1 : AdicCompletion M A) := by
    change (∑ g : G, s2t_adicActionHom M hM g s) = _
    simpa only [Nat.cast_smul_eq_nsmul] using
      (s2t_invariantOrbitSelector_trace (R := R₀) (G := G) q i)
  exact s2t_stabilizerFixedEquiv H F hsurj heq s hsel_in hsel_out hker htrace

/-- The actual invariant-base adic ring identifies with the stabilizer-fixed adic ring
at any selected maximal ideal in the fibre orbit. -/
def s2t_invariantBaseAdicStabilizerEquiv {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [IsNoetherianRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (i : MulAction.orbit G q) [Fintype (MulAction.stabilizer G i)] :
    let R₀ := FixedPoints.subalgebra K A G
    let H := MulAction.stabilizer G i
    let hq := s2t_orbitStabilizerIdeal_stable q i
    letI := MulSemiringAction.compHom A H.subtype
    letI := s2t_subgroup_action_smulCommClass (K := K) (A := A) H
    letI := s2t_adicAction (i : Ideal A) hq
    letI := s2t_adicAction_smulCommClass (R := K) (i : Ideal A) hq
    AdicCompletion (q.under R₀) R₀ ≃+*
      FixedPoints.subalgebra K (AdicCompletion (i : Ideal A) A) H := by
  let R₀ := FixedPoints.subalgebra K A G
  let H := MulAction.stabilizer G i
  let hq := s2t_orbitStabilizerIdeal_stable q i
  letI := MulSemiringAction.compHom A H.subtype
  letI := s2t_subgroup_action_smulCommClass (K := K) (A := A) H
  letI := s2t_adicAction (i : Ideal A) hq
  letI := s2t_adicAction_smulCommClass (R := K) (i : Ideal A) hq
  exact (s2t_fixedAdicEquiv (K := K) (A := A) (G := G) (q.under R₀)).trans
    (s2t_completedOrbitStabilizerEquiv (K := K) q i)

/-- The completed stabilizer comparison has the actual inclusion-induced adic map as its
underlying forward map. -/
theorem s2t_invariantBaseAdicStabilizerEquiv_apply {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [IsNoetherianRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (i : MulAction.orbit G q) [Fintype (MulAction.stabilizer G i)] :
    let R₀ := FixedPoints.subalgebra K A G
    ∀ x : AdicCompletion (q.under R₀) R₀,
      (s2t_invariantBaseAdicStabilizerEquiv (K := K) q i x).val =
        s2t_adicMap (q.under R₀) (i : Ideal A) (algebraMap R₀ A)
          (Ideal.map_le_iff_le_comap.mp (s2t_extended_under_le_orbit (R := R₀) q i)) x := by
  intro R₀ x
  let M := (q.under R₀).map (algebraMap R₀ A)
  let hMi := s2t_extended_under_le_orbit (R := R₀) q i
  change s2t_adicMap M (i : Ideal A) (RingHom.id A) hMi
    (s2t_adicMap (q.under R₀) M (algebraMap R₀ A) Ideal.le_comap_map x) = _
  rw [s2t_adicMap_comp]
  rfl

end HodgeLean.Foundations.Program
