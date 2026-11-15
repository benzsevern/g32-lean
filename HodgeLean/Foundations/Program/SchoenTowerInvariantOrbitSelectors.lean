import HodgeLean.Foundations.Program.SchoenTowerInvariantOrbitAdic
import HodgeLean.Foundations.Program.SchoenTowerOrbitTrace

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- The actual selecting element in the adic ring along the extended image-point ideal. -/
def s2t_invariantOrbitSelector {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (i : MulAction.orbit G q) : AdicCompletion ((q.under R).map (algebraMap R A)) A :=
  (s2t_invariantOrbitAdicEquiv (R := R) (G := G) q).symm (Pi.single i 1)

/-- Each invariant-orbit selector has its specified factor coordinate. -/
theorem s2t_invariantOrbitSelector_map {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (i j : MulAction.orbit G q) :
    s2t_invariantOrbitAdicEquiv (R := R) (G := G) q (s2t_invariantOrbitSelector (R := R) q i) j =
      if j = i then 1 else 0 := by
  have h := congrArg (fun x : ∀ k : MulAction.orbit G q, AdicCompletion (k : Ideal A) A => x j)
    ((s2t_invariantOrbitAdicEquiv (R := R) (G := G) q).apply_symm_apply (Pi.single i 1))
  change s2t_invariantOrbitAdicEquiv (R := R) (G := G) q
    (s2t_invariantOrbitSelector (R := R) q i) j = _ at h
  rw [h]
  by_cases hij : j = i
  · subst j
    simp only [Pi.single_eq_same, if_pos rfl, ite_true]
  · simp only [Pi.single_eq_of_ne hij, if_neg hij]

/-- The actual adic group action permutes the invariant-orbit selecting elements. -/
theorem s2t_invariantOrbitSelector_action {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (g : G) (i : MulAction.orbit G q) :
    s2t_adicActionHom ((q.under R).map (algebraMap R A))
      (s2t_extendedIdeal_stable (A := A) (G := G) (q.under R)) g
      (s2t_invariantOrbitSelector (R := R) q i) =
      s2t_invariantOrbitSelector (R := R) q (g • i) := by
  let M := (q.under R).map (algebraMap R A)
  let hM := s2t_extendedIdeal_stable (A := A) (G := G) (q.under R)
  apply (s2t_invariantOrbitAdicEquiv (R := R) (G := G) q).injective
  apply funext
  intro j
  let l : MulAction.orbit G q := g⁻¹ • j
  have hj : g • l = j := smul_inv_smul g j
  rw [← hj, s2t_invariantOrbitSelector_map]
  rw [s2t_invariantOrbitAdicEquiv_apply]
  change s2t_adicMap M (g • (l : Ideal A)) (RingHom.id A)
    (s2t_extended_under_le_orbit (R := R) q (g • l))
    (s2t_adicActionHom M hM g (s2t_invariantOrbitSelector (R := R) q i)) =
      if g • l = g • i then 1 else 0
  rw [s2t_adicMap_action_transport M (l : Ideal A) hM g
    (s2t_extended_under_le_orbit (R := R) q l)
    (s2t_extended_under_le_orbit (R := R) q (g • l))]
  rw [← s2t_invariantOrbitAdicEquiv_apply (R := R) (G := G) q
    (s2t_invariantOrbitSelector (R := R) q i) l, s2t_invariantOrbitSelector_map]
  by_cases hli : l = i
  · subst i
    rw [if_pos rfl, map_one, if_pos rfl]
  · have hne : g • l ≠ g • i := by
      intro h
      apply hli
      have hh := congrArg (fun k : MulAction.orbit G q => g⁻¹ • k) h
      simpa only [inv_smul_smul] using hh
    rw [if_neg hli, map_zero, if_neg hne]

/-- The actual invariant-orbit selectors form a partition of one. -/
theorem s2t_invariantOrbitSelector_sum {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)] :
    ∑ i : MulAction.orbit G q, s2t_invariantOrbitSelector (R := R) q i = 1 := by
  apply (s2t_invariantOrbitAdicEquiv (R := R) (G := G) q).injective
  rw [map_sum, map_one]
  apply funext
  intro j
  simp only [Finset.sum_apply, Pi.one_apply, s2t_invariantOrbitSelector_map,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- An actual orbit selector annihilates the kernel of its canonical factor projection. -/
theorem s2t_invariantOrbitSelector_mul_of_kernel {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (i : MulAction.orbit G q)
    (a : AdicCompletion ((q.under R).map (algebraMap R A)) A)
    (ha : s2t_invariantOrbitAdicEquiv (R := R) (G := G) q a i = 0) :
    s2t_invariantOrbitSelector (R := R) q i * a = 0 := by
  apply (s2t_invariantOrbitAdicEquiv (R := R) (G := G) q).injective
  rw [map_mul, map_zero]
  apply funext
  intro j
  change s2t_invariantOrbitAdicEquiv (R := R) (G := G) q
    (s2t_invariantOrbitSelector (R := R) q i) j *
    s2t_invariantOrbitAdicEquiv (R := R) (G := G) q a j = 0
  rw [s2t_invariantOrbitSelector_map]
  by_cases hij : j = i
  · subst j
    rw [if_pos rfl, ha, mul_zero]
  · rw [if_neg hij, zero_mul]

/-- The trace of an actual orbit selector is the order of its actual stabilizer. -/
theorem s2t_invariantOrbitSelector_trace {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal]
    [Fintype (MulAction.orbit G q)] [DecidableEq (MulAction.orbit G q)]
    (i : MulAction.orbit G q) [Fintype (MulAction.stabilizer G i)] :
    ∑ g : G, s2t_adicActionHom ((q.under R).map (algebraMap R A))
      (s2t_extendedIdeal_stable (A := A) (G := G) (q.under R)) g
      (s2t_invariantOrbitSelector (R := R) q i) =
        Fintype.card (MulAction.stabilizer G i) • 1 := by
  have htrans (j : MulAction.orbit G q) : ∃ g : G, g • i = j := by
    obtain ⟨gi, hi⟩ := i.property
    obtain ⟨gj, hj⟩ := j.property
    refine ⟨gj * gi⁻¹, ?_⟩
    apply Subtype.ext
    change (gj * gi⁻¹) • (i : Ideal A) = (j : Ideal A)
    calc
      (gj * gi⁻¹) • (i : Ideal A) = (gj * gi⁻¹) • (gi • q) :=
        congrArg (fun J : Ideal A => (gj * gi⁻¹) • J) hi.symm
      _ = gj • q := by rw [mul_smul, inv_smul_smul]
      _ = (j : Ideal A) := hj
  simp only [s2t_invariantOrbitSelector_action]
  rw [s2t_transitive_orbit_sum i htrans, s2t_invariantOrbitSelector_sum]

end HodgeLean.Foundations.Program
