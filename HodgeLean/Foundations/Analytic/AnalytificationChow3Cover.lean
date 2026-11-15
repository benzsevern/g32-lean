import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-! # Chow's lemma: a cover by dense affine opens

A quasi-compact scheme whose underlying space is Noetherian has a finite cover by affine opens
each of which is dense (`AnalytificationChow3_exists_dense_affine_cover`). Enlarge each member `A`
of a finite affine cover by pairwise disjoint affine opens `E_C`, one in each irreducible
component `C` disjoint from `A` and avoiding the other components; the union is affine
(`IsAffineOpen.iSup_of_disjoint`) and contains the generic point of every component. This is the
step that lets Chow's lemma run on all of `X` at once, in place of a reduction to irreducible
components (F4g-C3): the intersection of the cover is then dense.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace HodgeLean.Foundations.Analytic

universe u

/-- **Dense affine covers.** A quasi-compact scheme with Noetherian underlying space has a finite
cover by dense affine opens.
Source: EGA II, proof of Théorème 5.6.1 (reduction to affine opens meeting every component);
Stacks Project, Tag 01ZT (a finite union of disjoint affine opens is affine). -/
theorem AnalytificationChow3_exists_dense_affine_cover (X : Scheme.{u}) [CompactSpace X]
    [NoetherianSpace X] :
    ∃ (k : ℕ) (U : Fin k → X.Opens), (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Dense (U i : Set X)) ∧ ∀ x, ∃ i, x ∈ U i := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h => exact ⟨0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun x ↦ h.elim x⟩
  | inr h => ?_
  set Z := irreducibleComponents X
  have hZ : Z.Finite := NoetherianSpace.finite_irreducibleComponents
  have hgen : ∀ C ∈ Z, ∃ ξ, IsGenericPoint ξ C := fun C hC ↦
    QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  choose! ξ hξ using hgen
  have hZU : ∀ x : X, x ∈ ⋃₀ Z := fun x ↦ by
    rw [sUnion_irreducibleComponents]; trivial
  -- the complement of the other components
  let O : Set X → Set X := fun C ↦ (⋃ D ∈ Z \ {C}, D)ᶜ
  have hO : ∀ C, IsOpen (O C) := fun C ↦
    ((hZ.sdiff).isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1).isOpen_compl
  have hξO : ∀ C ∈ Z, ξ C ∈ O C := by
    intro C hC
    simp only [O, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro D hD hξD
    have hCD : C ⊆ D := by
      rw [← (hξ C hC).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hξD)
        (isClosed_of_mem_irreducibleComponents D hD.1)
    exact hD.2 (Set.eq_of_subset_of_subset (hC.2 hD.1.1 hCD) hCD)
  have hOC : ∀ C, O C ⊆ C := by
    intro C x hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp (hZU x)
    by_cases h : D = C
    · exact h ▸ hxD
    · exact absurd (Set.mem_biUnion (show D ∈ Z \ {C} from ⟨hD, h⟩) hxD) hx
  -- an affine open around each generic point, inside `O C`
  have hE : ∀ C ∈ Z, ∃ E : X.Opens, IsAffineOpen E ∧ ξ C ∈ E ∧ (E : Set X) ⊆ O C := by
    intro C hC
    obtain ⟨_, ⟨E, hE, rfl⟩, hξE, hEO⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hξO C hC) (hO C)
    exact ⟨E, hE, hξE, hEO⟩
  choose! E hEaff hξE hEO using hE
  have hEdisj : ∀ C ∈ Z, ∀ D ∈ Z, C ≠ D → Disjoint (E C : Set X) (E D : Set X) := by
    intro C hC D hD hCD
    refine Set.disjoint_left.mpr fun x hxC hxD ↦ ?_
    have h1 : x ∈ C := hOC C (hEO C hC hxC)
    exact hEO D hD hxD (Set.mem_biUnion (show C ∈ Z \ {D} from ⟨hC, hCD⟩) h1)
  -- a finite affine cover
  have hcov : ∀ x : X, ∃ A : X.Opens, IsAffineOpen A ∧ x ∈ A := fun x ↦ by
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨A, hA, hxA⟩
  choose A hA hxA using hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (A x : Set X))
    (fun x ↦ (A x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxA x⟩)
  let a : Fin t.card → X := fun i ↦ (t.equivFin.symm i : X)
  -- the enlarged opens
  let S : Fin t.card → Type u := fun i ↦ {C : Set X // C ∈ Z ∧ Disjoint (A (a i) : Set X) C}
  let F : ∀ i, Option (S i) → X.Opens := fun i o ↦ o.elim (A (a i)) fun C ↦ E C.1
  have hfin : ∀ i, Finite (Option (S i)) := fun i ↦ by
    have : Finite Z := hZ.to_subtype
    have : Finite (S i) := Finite.of_injective (fun C : S i ↦ (⟨C.1, C.2.1⟩ : Z))
      fun C D h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)
    infer_instance
  refine ⟨t.card, fun i ↦ ⨆ o, F i o, fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩
  · refine IsAffineOpen.iSup_of_disjoint (hU := fun o ↦ ?_) (hU' := ?_)
    · cases o with
      | none => exact hA _
      | some C => exact hEaff C.1 C.2.1
    · rintro (_ | C) (_ | D) hne
      · exact absurd rfl hne
      · rw [Function.onFun, ← Opens.coe_disjoint]
        exact D.2.2.mono_right (fun x hx ↦ hOC D.1 (hEO D.1 D.2.1 hx))
      · rw [Function.onFun, ← Opens.coe_disjoint]
        exact (C.2.2.mono_right (fun x hx ↦ hOC C.1 (hEO C.1 C.2.1 hx))).symm
      · rw [Function.onFun, ← Opens.coe_disjoint]
        exact hEdisj C.1 C.2.1 D.1 D.2.1 fun h ↦ hne (congrArg some (Subtype.ext h))
  · have hgenU : ∀ C ∈ Z, ξ C ∈ (⨆ o, F i o : X.Opens) := by
      intro C hC
      rw [Opens.mem_iSup]
      by_cases hd : Disjoint (A (a i) : Set X) C
      · exact ⟨some ⟨C, hC, hd⟩, hξE C hC⟩
      · refine ⟨none, ((hξ C hC).mem_open_set_iff (A (a i)).isOpen).mpr ?_⟩
        rw [Set.not_disjoint_iff] at hd
        obtain ⟨x, hxA, hxC⟩ := hd
        exact ⟨x, hxC, hxA⟩
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp (hZU x)
    have : C ⊆ closure (⨆ o, F i o : X.Opens) := by
      rw [← (hξ C hC).def]
      exact closure_mono (Set.singleton_subset_iff.mpr (hgenU C hC))
    exact this hxC
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine ⟨t.equivFin ⟨y, hy⟩, Opens.mem_iSup.mpr ⟨none, ?_⟩⟩
    simpa [F, a] using hxy

end HodgeLean.Foundations.Analytic
