import HodgeLean.Foundations.Program.RadialTransportSquare
import HodgeLean.Foundations.Program.ComponentTransportNormalized

/-! # Comparison of ambient families with matching tracks

Compactness gives continuous inverses for a family of bijections. Composing these
inverses with a second family gives an endpoint isotopy preserving the labels.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

theorem rtc_family_inverse {T X : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [T2Space T]
    (F : C(T × X, X)) (hF : ∀ t, Function.Bijective (fun z ↦ F (t, z))) :
    ∃ U : C(T × X, X), ∀ t z,
      F (t, U (t, z)) = z ∧ U (t, F (t, z)) = z := by
  let f : T × X → T × X := fun q ↦ (q.1, F q)
  have hc : Continuous f := continuous_fst.prodMk F.continuous
  have hb : Function.Bijective f := by
    constructor
    · rintro ⟨t, x⟩ ⟨s, y⟩ h
      have ht : t = s := congrArg Prod.fst h
      subst s
      exact Prod.ext rfl ((hF t).1 (congrArg Prod.snd h))
    · rintro ⟨t, z⟩
      obtain ⟨w, hw⟩ := (hF t).2 z
      exact ⟨(t, w), Prod.ext rfl hw⟩
  let E := hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hb)
  have he (q : T × X) : E q = (q.1, F q) := rfl
  have ht (t : T) (z : X) : (E.symm (t, z)).1 = t := by
    have h := congrArg Prod.fst (E.apply_symm_apply (t, z))
    simpa only [he] using h
  refine ⟨⟨fun q ↦ (E.symm q).2, continuous_snd.comp E.symm.continuous⟩, ?_⟩
  intro t z
  constructor
  · have h := congrArg Prod.snd (E.apply_symm_apply (t, z))
    change F (E.symm (t, z)) = z at h
    change F ((E.symm (t, z)).1, (E.symm (t, z)).2) = z at h
    rw [ht] at h
    exact h
  · have h := congrArg Prod.snd (E.symm_apply_apply (t, z))
    exact h

theorem rtc_same_tracks {X J : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (H G : C(unitInterval × X, X))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hG : ∀ t, Function.Bijective (fun z ↦ G (t, z)))
    (hH0 : ∀ z, H (0, z) = z) (hG0 : ∀ z, G (0, z) = z)
    (p : J → X) (q : unitInterval → J → X)
    (hHm : ∀ t j, H (t, p j) = q t j)
    (hGm : ∀ t j, G (t, p j) = q t j) :
    ∃ K : C(unitInterval × X, X),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = H (1, z)) ∧
      (∀ z, K (1, z) = G (1, z)) ∧
      (∀ t j, K (t, p j) = q 1 j) := by
  obtain ⟨U, hU⟩ := rtc_family_inverse H hH
  have hUb (t : unitInterval) : Function.Bijective (fun z ↦ U (t, z)) := by
    constructor
    · intro x y h
      simpa only [(hU t x).1, (hU t y).1] using congrArg (fun z ↦ H (t, z)) h
    · intro z
      exact ⟨H (t, z), (hU t z).2⟩
  let K : C(unitInterval × X, X) :=
    ⟨fun w ↦ H (1, U (w.1, G w)),
      H.continuous.comp (continuous_const.prodMk
        (U.continuous.comp (continuous_fst.prodMk G.continuous)))⟩
  refine ⟨K, fun t ↦ (hH 1).comp ((hUb t).comp (hG t)), ?_, ?_, ?_⟩
  · intro z
    change H (1, U (0, G (0, z))) = H (1, z)
    have hu0 : U (0, z) = z := by
      have hu := (hU 0 z).1
      rwa [hH0] at hu
    rw [hG0, hu0]
  · intro z
    exact (hU 1 (G (1, z))).1
  · intro t j
    change H (1, U (t, G (t, p j))) = q 1 j
    rw [hGm, ← hHm, (hU t (p j)).2, hHm]

end HodgeLean.Foundations.Program
