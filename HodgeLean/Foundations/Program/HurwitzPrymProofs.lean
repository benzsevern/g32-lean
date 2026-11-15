import HodgeLean.Foundations.Program.HurwitzPrymDefs
import HodgeLean.Foundations.Program.HurwitzPrymCovAlg
import HodgeLean.Foundations.Program.HurwitzPrymCovIsotypic
import HodgeLean.Foundations.Program.HurwitzPrymCovLocal
import HodgeLean.Foundations.Program.HurwitzPrymCovConnected
import HodgeLean.Foundations.Program.HurwitzPrymCovRot
import HodgeLean.Foundations.Program.HurwitzPrymCovDegree
import HodgeLean.Foundations.Program.HurwitzPrymCovGalois
import HodgeLean.Foundations.Program.HurwitzPrymCovLoop
import HodgeLean.Foundations.Program.HurwitzPrymCovHodge
import HodgeLean.Foundations.Program.HurwitzPrymCovSphere
import HodgeLean.Foundations.Program.HurwitzPrymCovInvariant
import HodgeLean.Foundations.Program.HurwitzPrymCovDescent
import HodgeLean.Foundations.Program.HurwitzPrymAlgElliptic
import HodgeLean.Foundations.Program.HurwitzPrymAlg2Torus
import HodgeLean.Foundations.Program.HurwitzPrymRexConj
import HodgeLean.Foundations.Program.HurwitzPrymRexG32
import HodgeLean.Foundations.Program.HurwitzPrymRexCW
import HodgeLean.Foundations.Program.HurwitzPrymRexCoverLocal
import HodgeLean.Foundations.Program.HurwitzPrymRexFillMain
import HodgeLean.Foundations.Program.HurwitzPrymRRExist
import HodgeLean.Foundations.Program.HurwitzPrymRRForm
import HodgeLean.Foundations.Program.RiemannRoch

set_option maxHeartbeats 400000

/-! # Track B4, Hurwitz covers, isotypic Prym factors and Chevalley–Weil: proofs

One `_aux` theorem per statement of the frozen `HurwitzPrym.lean`.
The holomorphic Chevalley–Weil formula follows from Eichler traces, character orthogonality,
and a cyclic root sum. The topological formula follows by the Hodge decomposition.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold TopologicalSpace HodgeLean.Papers
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Adapters
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## Monodromy tuples and Hurwitz components -/

section Tuples

variable {G : Type*} [Group G]

theorem b4_nielsen_conjTuple_iff_aux {r : ℕ} (a : G) (g : Fin r → G) :
    b4_Nielsen (b4_conjTuple a g) ↔ b4_Nielsen g := by
  have prod_conj (l : List G) : (l.map fun x ↦ a * x * a⁻¹).prod = a * l.prod * a⁻¹ := by
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.prod_cons, ih]; group
  have closure_forward (a : G) (g : Fin r → G)
      (hg : Subgroup.closure (Set.range g) = ⊤) :
      Subgroup.closure (Set.range (b4_conjTuple a g)) = ⊤ := by
    apply top_unique
    intro x _
    let K := (Subgroup.closure (Set.range (b4_conjTuple a g))).comap
      (MulAut.conj a).toMonoidHom
    have hle : Subgroup.closure (Set.range g) ≤ K := (Subgroup.closure_le K).mpr (by
      rintro y ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩)
    have hxK : a⁻¹ * x * a ∈ K := by
      rw [hg] at hle
      exact hle trivial
    change a * (a⁻¹ * x * a) * a⁻¹ ∈
      Subgroup.closure (Set.range (b4_conjTuple a g)) at hxK
    convert hxK using 1 <;> group
  constructor
  · rintro ⟨hprod, hclosure⟩
    constructor
    · have hlist : List.ofFn (b4_conjTuple a g) =
          (List.ofFn g).map (fun x ↦ a * x * a⁻¹) := by
        rw [← List.ofFn_comp']; rfl
      rw [hlist, prod_conj] at hprod
      calc
        (List.ofFn g).prod = a⁻¹ * (a * (List.ofFn g).prod * a⁻¹) * a := by group
        _ = 1 := by rw [hprod]; simp
    · have hc := closure_forward a⁻¹ (b4_conjTuple a g) hclosure
      have ht : b4_conjTuple a⁻¹ (b4_conjTuple a g) = g := by
        funext i
        dsimp [b4_conjTuple]
        group
      rwa [ht] at hc
  · rintro ⟨hprod, hclosure⟩
    constructor
    · rw [show List.ofFn (b4_conjTuple a g) =
          (List.ofFn g).map (fun x ↦ a * x * a⁻¹) by
            rw [← List.ofFn_comp']; rfl, prod_conj, hprod]
      simp
    · exact closure_forward a g hclosure

theorem b4_nielsen_braid_iff_aux {r : ℕ} (a b : Fin r) (hab : (b : ℕ) = (a : ℕ) + 1)
    (g : Fin r → G) :
    b4_Nielsen (b4_braid a b g) ↔ b4_Nielsen g := by
  let g' := b4_braid a b g
  have ha : (a : ℕ) < r := a.isLt
  have hb : (b : ℕ) < r := b.isLt
  have hba : b ≠ a := by
    intro h
    subst b
    omega
  have hbeq : b = ⟨(a : ℕ) + 1, by omega⟩ := Fin.ext hab
  have g'_eq (i : Fin r) (hia : i ≠ a) (hib : i ≠ b) : g' i = g i := by
    simp [g', b4_braid, Function.update, hia, hib,
      Equiv.swap_apply_of_ne_of_ne]
  have htake : (List.ofFn g').take (a : ℕ) = (List.ofFn g).take (a : ℕ) := by
    apply List.ext_get (by simp [ha.le])
    intro n hn hn'
    have hnval : n < (a : ℕ) := by simpa [ha.le] using hn
    simp only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn]
    apply g'_eq
    · intro heq
      have := congrArg Fin.val heq
      simp at this
      omega
    · intro heq
      have := congrArg Fin.val heq
      simp [hab] at this
      omega
  have hdrop : (List.ofFn g').drop ((a : ℕ) + 2) =
      (List.ofFn g).drop ((a : ℕ) + 2) := by
    apply List.ext_get (by simp)
    intro n hn hn'
    simp only [List.length_drop, List.length_ofFn] at hn
    have hnval : (a : ℕ) + 2 + n < r := Nat.lt_sub_iff_add_lt'.1 hn
    simp only [List.get_eq_getElem, List.getElem_drop, List.getElem_ofFn]
    apply g'_eq
    · intro heq
      have := congrArg Fin.val heq
      simp at this
      omega
    · intro heq
      have := congrArg Fin.val heq
      simp [hab] at this
      omega
  have hprod : (List.ofFn g').prod = (List.ofFn g).prod := by
    rw [← List.prod_take_mul_prod_drop (List.ofFn g') ((a : ℕ) + 2),
      ← List.prod_take_mul_prod_drop (List.ofFn g) ((a : ℕ) + 2),
      List.prod_take_succ _ ((a : ℕ) + 1) (by simpa [hab] using hb),
      List.prod_take_succ _ (a : ℕ) (by simp [ha]),
      List.prod_take_succ _ ((a : ℕ) + 1) (by simpa [hab] using hb),
      List.prod_take_succ _ (a : ℕ) (by simp [ha]), htake, hdrop]
    simp only [List.getElem_ofFn]
    unfold g' b4_braid
    rw [← hbeq]
    simp [Function.comp_apply, hba]
    group
  have hclosure : Subgroup.closure (Set.range g') = Subgroup.closure (Set.range g) := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).2
      rintro _ ⟨i, rfl⟩
      unfold g' b4_braid
      by_cases hi : i = a
      · subst i
        simp only [Function.update_self]
        exact (Subgroup.closure (Set.range g)).mul_mem
          ((Subgroup.closure (Set.range g)).mul_mem
            (Subgroup.subset_closure ⟨a, rfl⟩) (Subgroup.subset_closure ⟨b, rfl⟩))
          ((Subgroup.closure (Set.range g)).inv_mem (Subgroup.subset_closure ⟨a, rfl⟩))
      · simp only [Function.update, if_neg hi, Function.comp_apply]
        apply Subgroup.subset_closure
        exact ⟨Equiv.swap a b i, by simp [Function.update, hi]⟩
    · apply (Subgroup.closure_le _).2
      rintro _ ⟨i, rfl⟩
      by_cases hi : i = a
      · subst i
        have : g' b ∈ Subgroup.closure (Set.range g') := Subgroup.subset_closure ⟨b, rfl⟩
        simpa [g', b4_braid, hba] using this
      · by_cases hi' : i = b
        · subst i
          have hnew : g' a ∈ Subgroup.closure (Set.range g') :=
            Subgroup.subset_closure ⟨a, rfl⟩
          have hold : g a ∈ Subgroup.closure (Set.range g') := by
            have hbmem : g' b ∈ Subgroup.closure (Set.range g') :=
              Subgroup.subset_closure ⟨b, rfl⟩
            simpa [g', b4_braid, hba] using hbmem
          have := (Subgroup.closure (Set.range g')).mul_mem
            ((Subgroup.closure (Set.range g')).mul_mem
              ((Subgroup.closure (Set.range g')).inv_mem hold) hnew) hold
          have heq : (g a)⁻¹ * g' a * g a = g b := by
            rw [show g' a = g a * g b * (g a)⁻¹ by simp [g', b4_braid]]
            group
          rw [heq] at this
          exact this
        · have : g' i ∈ Subgroup.closure (Set.range g') := Subgroup.subset_closure ⟨i, rfl⟩
          simpa [g', b4_braid, hi, hi', Equiv.swap_apply_of_ne_of_ne] using this
  change ((List.ofFn g').prod = 1 ∧ Subgroup.closure (Set.range g') = ⊤) ↔ _
  rw [hprod, hclosure]
  rfl

theorem b4_classes_braid_aux {r : ℕ} (a b : Fin r) (g : Fin r → G) :
    b4_classes (b4_braid a b g) = b4_classes g := by
  unfold b4_classes b4_braid
  simp only [← List.ofFn_comp']
  have hf : ConjClasses.mk ∘ Function.update (g ∘ Equiv.swap a b) a
        (g a * g b * (g a)⁻¹) = ConjClasses.mk ∘ g ∘ Equiv.swap a b := by
    funext i
    by_cases hi : i = a
    · subst i
      simp only [Function.comp_apply, Function.update_self, Equiv.swap_apply_left]
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      exact (isConj_iff.mpr ⟨g a, rfl⟩).symm
    · simp [Function.update, hi]
  rw [show (fun i ↦ ConjClasses.mk
      (Function.update (g ∘ Equiv.swap a b) a (g a * g b * (g a)⁻¹) i)) =
      (fun i ↦ ConjClasses.mk (g ((Equiv.swap a b) i))) from hf]
  exact Quot.sound (Equiv.Perm.ofFn_comp_perm (Equiv.swap a b)
    (fun i ↦ ConjClasses.mk (g i)))

theorem b4_classes_conjTuple_aux {r : ℕ} (a : G) (g : Fin r → G) :
    b4_classes (b4_conjTuple a g) = b4_classes g := by
  apply congrArg (↑· : List (ConjClasses G) → Multiset (ConjClasses G))
  rw [← List.ofFn_comp', ← List.ofFn_comp']
  apply congrArg List.ofFn
  funext i
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact (isConj_iff.mpr ⟨a, rfl⟩).symm

theorem b4_nielsen_of_sameComponent_aux {r : ℕ} {g g' : Fin r → G}
    (h : b4_SameComponent g g') (hg : b4_Nielsen g) : b4_Nielsen g' := by
  have hi : ∀ {x y : Fin r → G}, b4_SameComponent x y →
      (b4_Nielsen x ↔ b4_Nielsen y) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
        rcases hxy with ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩
        · exact (b4_nielsen_conjTuple_iff_aux a x).symm
        · exact (b4_nielsen_braid_iff_aux a b hab x).symm
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  exact (hi h).mp hg

theorem b4_classes_of_sameComponent_aux {r : ℕ} {g g' : Fin r → G}
    (h : b4_SameComponent g g') : b4_classes g' = b4_classes g := by
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩
      · exact b4_classes_conjTuple_aux a x
      · exact b4_classes_braid_aux a b x
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihyz.trans ihxy

end Tuples

theorem b4_cyc3_nielsen_aux : b4_Nielsen b4_cyc3 := by
  constructor
  · decide
  · apply top_unique
    intro x _
    have hs : Multiplicative.ofAdd (1 : ZMod 3) ∈
        Subgroup.closure (Set.range b4_cyc3) :=
      Subgroup.subset_closure ⟨0, rfl⟩
    fin_cases x
    · exact Subgroup.one_mem _
    · exact hs
    · convert Subgroup.mul_mem _ hs hs using 1 <;> decide

/-! ## Branched covers -/

section Covers

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

theorem b4_ramIndex_eq_one_iff_aux (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x : C) :
    b4_ramIndex E E' f x = 1 ↔ mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 := by
  let s := {n : ℕ | 1 ≤ n ∧ iteratedFDeriv ℂ n
    (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x) ≠ 0}
  have hd : iteratedFDeriv ℂ 1
      (writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') x f) (extChartAt 𝓘(ℂ, E) x x) ≠ 0 ↔
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 := by
    rw [(hf.mdifferentiableAt (by simp)).mfderiv]
    simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
    change iteratedFDeriv ℂ 1 _ _ ≠ 0 ↔ fderiv ℂ _ _ ≠ 0
    rw [← norm_ne_zero_iff, norm_iteratedFDeriv_one, norm_ne_zero_iff]
    exact Iff.rfl
  change sInf s = 1 ↔ _
  constructor
  · intro hs
    have hne : s.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h] at hs
      simp at hs
    have hm := Nat.sInf_mem hne
    rw [hs] at hm
    exact hd.mp hm.2
  · intro h
    have hm : 1 ∈ s := ⟨le_rfl, hd.mpr h⟩
    exact le_antisymm (Nat.sInf_le hm) (le_csInf ⟨1, hm⟩ fun _ hn ↦ hn.1)

theorem b4_ramIndex_pos_aux [T2Space C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    [T2Space Y] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (x : C) :
    1 ≤ b4_ramIndex E E' f x := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  exact b4cov_ramIndex_pos f hf hnc x

theorem b4_ramification_finite_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') :
    {x : C | 2 ≤ b4_ramIndex E E' f x}.Finite := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  refine (b4cov_critical_finite hE f hf hnc).subset fun x hx ↦ ?_
  by_contra h
  have := (b4_ramIndex_eq_one_iff_aux f hf x).2 h
  change 2 ≤ b4_ramIndex E E' f x at hx
  omega

theorem b4_surjective_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') :
    Function.Surjective f := by
  exact b4cov_surjective hE' f hf hnc

theorem b4_card_fiber_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (y : Y)
    (hy : y ∉ b4_branchSet E E' f) :
    Nat.card (f ⁻¹' {y}) = b4_fiberDegree E E' f y := by
  have hram : ∀ x ∈ f ⁻¹' {y}, b4_ramIndex E E' f x = 1 := by
    intro x hx
    have hlt : ¬ 2 ≤ b4_ramIndex E E' f x := by
      intro htwo
      apply hy
      exact ⟨x, htwo, hx⟩
    have hup : b4_ramIndex E E' f x ≤ 1 := by omega
    exact Nat.le_antisymm hup (b4_ramIndex_pos_aux hE hE' f hf hnc x)
  classical
  rw [b4_fiberDegree]
  rw [show Nat.card ↑(f ⁻¹' {y}) = (f ⁻¹' {y}).ncard by simp, ← finsum_one]
  exact finsum_mem_congr rfl fun x hx ↦ (hram x hx).symm

theorem b4_isCoveringMap_restrict_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') :
    IsCoveringMap (b4_restrict E E' f) := by
  have hloc : IsLocalHomeomorphOn f (f ⁻¹' (b4_branchSet E E' f)ᶜ) := by
    refine (b4cov_isLocalHomeomorphOn hE hE' f hf).mono fun x hx ↦ ?_
    have hle : ¬ 2 ≤ b4_ramIndex E E' f x := fun h ↦ hx ⟨x, h, rfl⟩
    have := b4_ramIndex_pos_aux hE hE' f hf hnc x
    exact (b4_ramIndex_eq_one_iff_aux f hf x).1 (by omega)
  have hcov : IsCoveringMapOn f (b4_branchSet E E' f)ᶜ :=
    IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hf.continuous.isClosedMap
      (fun y _ ↦ b4_fiber_finite_aux hE hE' f hf hnc y) hloc
  exact hcov.isCoveringMap_restrictPreimage

theorem b4_monodromy_transitive_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x')
    (y₀ : {y : Y // y ∉ b4_branchSet E E' f}) (x x' : b4_restrict E E' f ⁻¹' {y₀}) :
    ∃ γ, b4_monodromy E E' f y₀ γ x = x' := by
  classical
  have hcov := b4_isCoveringMap_restrict_aux hE hE' f hf hnc
  have hBfin : (b4_branchSet E E' f).Finite :=
    (b4_ramification_finite_aux hE hE' f hf hnc).image f
  have hSfin : (f ⁻¹' b4_branchSet E E' f).Finite :=
    hBfin.preimage' fun y _ ↦ b4_fiber_finite_aux hE hE' f hf hnc y
  have hconn : IsPreconnected (Set.univ \ f ⁻¹' b4_branchSet E E' f) :=
    b4cov_isPreconnected_diff_finite isOpen_univ isPreconnected_univ hSfin
      fun s _ ↦ b4cov_goodPoint hE s
  have hset : Set.univ \ f ⁻¹' b4_branchSet E E' f = {z : C | f z ∉ b4_branchSet E E' f} := by
    ext; simp
  rw [hset] at hconn
  have hopen : IsOpen {z : C | f z ∉ b4_branchSet E E' f} :=
    hBfin.isClosed.isOpen_compl.preimage hf.continuous
  have : ConnectedSpace {z : C | f z ∉ b4_branchSet E E' f} :=
    isConnected_iff_connectedSpace.1 ⟨⟨x.1.1, x.1.2⟩, hconn⟩
  have := ChartedSpace.locallyPathConnectedSpace E C
  have := hopen.locallyPathConnectedSpace
  have hpc : PathConnectedSpace {z : C | f z ∉ b4_branchSet E E' f} :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  let δ : Path x.1 x'.1 := @PathConnectedSpace.somePath _ _ hpc x.1 x'.1
  let Γ : Path.Homotopic.Quotient x.1 x'.1 := Path.Homotopic.Quotient.mk δ
  have hx : b4_restrict E E' f x.1 = y₀ := x.2
  have hx' : b4_restrict E E' f x'.1 = y₀ := x'.2
  let γ : Path.Homotopic.Quotient y₀ y₀ :=
    (Γ.map ⟨b4_restrict E E' f, hcov.continuous⟩).cast hx.symm hx'.symm
  refine ⟨FundamentalGroup.fromPath γ, ?_⟩
  simp only [b4_monodromy, dite_eq_left hcov, IsCoveringMap.coe_monodromyPerm]
  exact hcov.monodromy_eq_of_map_eq Γ (by simp only [γ, Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]; rfl)

theorem b4_riemannHurwitz_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hnc : ∃ x x', f x ≠ f x') (y : Y) :
    2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 =
      b4_fiberDegree E E' f y * (2 * (Module.finrank ℂ (b3_HolForm E' Y) : ℤ) - 2) +
        ∑ᶠ x : C, ((b4_ramIndex E E' f x : ℤ) - 1) := by
  exact b4c_riemannHurwitz hE hE' f hf hnc y

end Covers

/-! ## Finite group actions and Galois covers -/

section Galois

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
variable {G : Type} [Group G] [Finite G] [MulAction G C]

theorem b4_exists_rotGen_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul G C]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (x : C) :
    ∃ h : G, b4_IsRotGen E x h := by
  exact b4cov_exists_rotGen hE hG x

theorem b4_rotGen_unique_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul G C]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (x : C) (h h' : G)
    (hh : b4_IsRotGen E x h) (hh' : b4_IsRotGen E x h') : h = h' := by
  exact b4cov_rotGen_unique hE hG x h h' hh hh'

theorem b4_ramIndex_galois_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    [FaithfulSMul G C] (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) (x : C) :
    b4_ramIndex E E' f x = Nat.card (MulAction.stabilizer G x) := by
  exact b4cov_ramIndex_galois hE hE' hG f hf hgal x

theorem b4_fiberDegree_galois_aux [Nonempty C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    [FaithfulSMul G C] (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) (y : Y) :
    b4_fiberDegree E E' f y = Nat.card G := by
  exact b4cov_fiberDegree_galois hE hE' hG f hf hgal y

theorem b4_invariantForms_galois_aux [Nonempty C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (hE' : Module.finrank ℂ E' = 1)
    [FaithfulSMul G C] (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) :
    Module.finrank ℂ (b4_invariantForms E C G) = Module.finrank ℂ (b3_HolForm E' Y) := by
  exact b4cov_invariantForms_galois hE hE' hG f hf hgal

end Galois

/-! ## The action on the period lattice -/

section Lattice

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [MulAction G C]

private theorem HurwitzPrymAlg_contMDiff_real_one {f : C → C}
    (hf : ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω f) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) 1 f := by
  intro x
  rw [contMDiffAt_iff]
  have hx := hf x
  rw [contMDiffAt_iff] at hx
  refine ⟨hx.1, ?_⟩
  simpa using (hx.2.restrict_scalars ℝ).of_le (by simp)

theorem b4_latticeAct_isPushforward_aux (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (fun x : C ↦ g • x)) (g : G) :
    b3_IsPushforward E E (fun x : C ↦ g • x) (b4_latticeAct E g) := by
  obtain ⟨φ, hφ, -⟩ := b3_exists_pushforward (fun x : C ↦ g • x) (hG g)
  let hex : ∃ φ, b3_IsPushforward E E (fun x : C ↦ g • x) φ := ⟨φ, hφ⟩
  simpa only [b4_latticeAct, hex, dite_true] using hex.choose_spec

theorem b4_latticeAct_one_aux (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (fun x : C ↦ g • x)) :
    b4_latticeAct E (C := C) (1 : G) = AddMonoidHom.id _ := by
  apply b3_pushforward_unique (fun x : C ↦ (1 : G) • x) (hG 1)
  · exact b4_latticeAct_isPushforward_aux hG 1
  · intro γ γ' hγ
    have hloop : γ' = γ := Subtype.ext (funext fun t ↦ by
      simpa only [Function.comp_apply, one_smul] using congrFun hγ t)
    simp [hloop]

theorem b4_latticeAct_mul_aux (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (fun x : C ↦ g • x)) (g h : G) :
    b4_latticeAct E (C := C) (g * h) = (b4_latticeAct E g).comp (b4_latticeAct E h) := by
  apply b3_pushforward_unique (fun x : C ↦ (g * h) • x) (hG (g * h))
  · exact b4_latticeAct_isPushforward_aux hG (g * h)
  · intro γ γ' hγ
    let δ : b3_SmoothLoop E C :=
      ⟨fun t ↦ h • γ.1 t,
        fun t ↦ congrArg (fun x ↦ h • x) (γ.2.1 t),
        (HurwitzPrymAlg_contMDiff_real_one (hG h)).comp γ.2.2⟩
    rw [AddMonoidHom.comp_apply,
      b4_latticeAct_isPushforward_aux hG h γ δ rfl]
    apply b4_latticeAct_isPushforward_aux hG g δ γ'
    funext t
    simpa [δ, mul_smul] using congrFun hγ t

theorem b4_cplxAct_periodF_aux (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (fun x : C ↦ g • x)) (g : G) :
    b3_periodF E C ≤ (b3_periodF E C).comap (b4_cplxAct E g) := by
  obtain ⟨φ, hφ, hφF⟩ := b3_exists_pushforward (fun x : C ↦ g • x) (hG g)
  have heq := b3_pushforward_unique (fun x : C ↦ g • x) (hG g)
    (b4_latticeAct E g) φ (b4_latticeAct_isPushforward_aux hG g) hφ
  simpa only [b4_cplxAct, heq] using hφF

theorem b4_cplxAct_conjF_aux (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (fun x : C ↦ g • x)) (g : G) :
    b2_conjSubmodule _ (b3_periodF E C) ≤
      (b2_conjSubmodule _ (b3_periodF E C)).comap (b4_cplxAct E g) := by
  simpa only [b4_cplxAct] using b2f_conjSubmodule_le_comap (b3_periodF E C)
    (b4_latticeAct E g) (b4_cplxAct_periodF_aux hG g)

theorem b4_intersectionForm_invariant_aux [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (g : G) (x y : b3_periodLattice E C) :
    Q (b4_latticeAct E g x) (b4_latticeAct E g y) = Q x y := by
  let Q' : LinearMap.BilinForm ℤ (b3_periodLattice E C) :=
    Q.compl₁₂ (b4_latticeAct E g).toIntLinearMap (b4_latticeAct E g).toIntLinearMap
  have hQ' : b3_IsIntersectionForm E Q' := by
    intro γ δ hγδ
    have hpush := b4_latticeAct_isPushforward_aux hG g
    show Q (b4_latticeAct E g (b3_latticePeriod E C γ)) (b4_latticeAct E g (b3_latticePeriod E C δ)) =
      b3_intersection E γ δ
    rw [hpush γ (b4cov_mapLoop _ (hG g) γ) rfl, hpush δ (b4cov_mapLoop _ (hG g) δ) rfl,
      hQ _ _ (b4cov_transverse_map hE hG g γ δ hγδ), b4cov_intersection_map hE hG g γ δ]
  have := b3_intersectionForm_unique hE Q' Q hQ' hQ
  exact congrArg (fun R : LinearMap.BilinForm ℤ (b3_periodLattice E C) ↦ R x y) this

variable [Fintype G]

theorem b4_cplxMap_groupEnd_aux (a : G → ℤ) :
    b2_cplxMap (b4_groupEnd E (C := C) a) = ∑ g, (a g : ℂ) • b4_cplxAct E g := by
  rw [b4_groupEnd, b4cov_cplxMap_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [b4cov_cplxMap_zsmul]
  rfl

theorem b4_groupEnd_periodF_aux (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (fun x : C ↦ g • x)) (a : G → ℤ) :
    b3_periodF E C ≤ (b3_periodF E C).comap (b2_cplxMap (b4_groupEnd E a)) := by
  intro v hv
  rw [Submodule.mem_comap, b4_cplxMap_groupEnd_aux, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ ↦ Submodule.smul_mem _ _ (b4_cplxAct_periodF_aux hG g hv)

theorem b4_groupEnd_adjoint_aux [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (a : G → ℤ) (x y : b3_periodLattice E C) :
    Q (b4_groupEnd E a x) y = Q x (b4_groupEnd E (fun g ↦ a g⁻¹) y) := by
  have hinv : ∀ (g : G) (z : b3_periodLattice E C),
      b4_latticeAct E g⁻¹ (b4_latticeAct E g z) = z := by
    intro g z
    rw [← AddMonoidHom.comp_apply, ← b4_latticeAct_mul_aux hG, inv_mul_cancel,
      b4_latticeAct_one_aux hG, AddMonoidHom.id_apply]
  simp only [b4_groupEnd, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, map_sum,
    map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [← Equiv.sum_comp (Equiv.inv G)]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp only [Equiv.inv_apply]
  congr 1
  rw [← b4_intersectionForm_invariant_aux hE hG Q hQ g⁻¹ x (b4_latticeAct E g y), hinv]

end Lattice

/-! ## Chevalley–Weil -/

section ChevalleyWeil

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [Fintype G] [MulAction G C]
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem b4_hodge_eq_holo_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (ρ : Representation ℂ G V) :
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g) (b3_periodF E C)) =
      Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)) := by
  exact b4cov_hodge_eq_holo hE hG (fun g ↦ b4_latticeAct_isPushforward_aux hG g)
    (fun g ↦ b4_cplxAct_periodF_aux hG g) ρ

theorem b4_homG_split_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (ρ : Representation ℂ G V) :
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g) ⊤) =
      Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g) (b3_periodF E C)) +
        Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g)
          (b2_conjSubmodule _ (b3_periodF E C))) := by
  have := b3_periodLattice_finite (C := C) hE
  exact b4cov_finrank_homG_split ρ _ _ _ (b3_isWeightOne hE) (b4_cplxAct_periodF_aux hG)
    (b4_cplxAct_conjF_aux hG)

def b4_formRepresentation
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) :
    Representation ℂ G (b3_HolForm E C) where
  toFun := b4cov_tau hG
  map_one' := b4cov_tau_one hG
  map_mul' := b4cov_tau_mul hG

def b4_homGFormEquiv
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (ρ : Representation ℂ G V) :
    b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C) ≃ₗ[ℂ]
      Representation.IntertwiningMap ρ (b4_formRepresentation hG) where
  toFun φ :=
    ⟨(φ : V →ₗ[ℂ] (TangentBundle 𝓘(ℂ, E) C → ℂ)).codRestrict
      (b3_HolForm E C) φ.2.1, fun g ↦ by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact φ.2.2 g v⟩
  invFun ψ :=
    ⟨(b3_HolForm E C).subtype ∘ₗ ψ.toLinearMap, fun v ↦ (ψ v).2, fun g v ↦ by
      change ((ψ (ρ g v) : b3_HolForm E C) :
        TangentBundle 𝓘(ℂ, E) C → ℂ) = b4_formAct E g (ψ v)
      rw [ψ.isIntertwining]
      rfl⟩
  map_add' φ ψ := by ext; rfl
  map_smul' c φ := by ext; rfl
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

theorem b4_homGForm_character_average [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (ρ : Representation ℂ G V) :
    (Module.finrank ℂ
      (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)) : ℂ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
        (b4_formRepresentation hG).character g * ρ.character g⁻¹ := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  rw [(b4_homGFormEquiv hG ρ).finrank_eq]
  exact (Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    ρ (b4_formRepresentation hG)).symm

def b4_actionHomeomorph
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g : G) : C ≃ₜ C where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := (hG g).continuous
  continuous_invFun := (hG g⁻¹).continuous

theorem b4_actionHomeomorph_iterate_apply
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g : G) (n : ℕ) (x : C) :
    (b4_actionHomeomorph hG g)^[n] x = g ^ n • x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, pow_succ, mul_smul]
      rfl

theorem b4_formRepresentation_character_eq_pullback [T2Space C] [CompactSpace C]
    [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g : G) :
    (b4_formRepresentation hG).character g =
      LinearMap.trace ℂ (b3_HolForm E C)
        (b4c_formPullbackEnd (b4_actionHomeomorph hG g⁻¹) (hG g⁻¹)) := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  congr 1

theorem b4_formRepresentation_character_of_ne_one [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [FaithfulSMul G C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g : G) (hg : g ≠ 1) :
    (b4_formRepresentation hG).character g =
      1 + ∑ᶠ p : C, if (b4_actionHomeomorph hG g⁻¹) p = p then
        b4c_rotation hE (b4_actionHomeomorph hG g⁻¹) p /
          (1 - b4c_rotation hE (b4_actionHomeomorph hG g⁻¹) p) else 0 := by
  classical
  rw [b4_formRepresentation_character_eq_pullback hE hG g]
  have hne : b4_actionHomeomorph hG g⁻¹ ≠ Homeomorph.refl C := by
    intro he
    have hgi : g⁻¹ = 1 := FaithfulSMul.eq_of_smul_eq_smul fun x : C ↦ by
      have hx := congrArg (fun e : C ≃ₜ C ↦ e x) he
      change g⁻¹ • x = x at hx
      simpa only [one_smul] using hx
    exact hg (inv_eq_one.mp hgi)
  have hord : (b4_actionHomeomorph hG g⁻¹)^[Nat.card G] = id := by
    funext x
    rw [b4_actionHomeomorph_iterate_apply]
    simp
  exact b4c_eichler_trace hE (b4_actionHomeomorph hG g⁻¹) (hG g⁻¹)
    hne (Nat.card G) Nat.card_pos hord

theorem b4_rotation_of_rotGen
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (x : C) (g : G) (hg : b4_IsRotGen E x g) :
    b4c_rotation hE (b4_actionHomeomorph hG g) x =
      Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ)) := by
  unfold b4c_rotation
  change (b4cov_lineEquiv hE).symm
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun z : C ↦ g • z) x
      (b4cov_lineEquiv hE 1)) = _
  rw [hg.2.2]
  simp

theorem b4_fixed_element_is_rotGen_power
    (x : C) (k g : G) (hk : b4_IsRotGen E x k) (hg : g • x = x) :
    ∃ m : ℕ, m < orderOf k ∧ g = k ^ m := by
  have hmem : g ∈ MulAction.stabilizer G x := hg
  rw [← RiemannRochTop_rotGen_zpowers x k hk] at hmem
  rw [mem_zpowers_iff_mem_range_orderOf] at hmem
  obtain ⟨m, hm, hmg⟩ := Finset.mem_image.mp hmem
  exact ⟨m, Finset.mem_range.mp hm, hmg.symm⟩

theorem b4_nontrivial_irreducible_invariants_eq_bot
    (rho : Representation ℂ G V) [rho.IsIrreducible]
    (hrho : ∃ (g : G) (v : V), rho g v ≠ v) :
    Representation.invariants rho = ⊥ := by
  let U : Subrepresentation rho :=
    Subrepresentation.mk (Representation.invariants rho) (by
      intro g v hv h
      calc
        rho h (rho g v) = rho (h * g) v := by
          rw [map_mul]
          rfl
        _ = rho (g * (g⁻¹ * h * g)) v := by group
        _ = rho g (rho (g⁻¹ * h * g) v) := by
          rw [map_mul]
          rfl
        _ = rho g v := by rw [hv])
  obtain hU | hU := eq_bot_or_eq_top U
  · exact Submodule.ext fun v ↦ by
      change v ∈ U ↔ _
      rw [hU]
      rfl
  · obtain ⟨g, v, hgv⟩ := hrho
    exfalso
    apply hgv
    have hv : v ∈ U := by rw [hU]; trivial
    exact hv g

theorem b4_nontrivial_irreducible_character_sum_inv
    (rho : Representation ℂ G V) [rho.IsIrreducible]
    (hrho : ∃ (g : G) (v : V), rho g v ≠ v) :
    ∑ g : G, rho.character g⁻¹ = 0 := by
  have hav := Representation.card_inv_mul_sum_char_eq_finrank rho
  rw [b4_nontrivial_irreducible_invariants_eq_bot rho hrho, finrank_bot, Nat.cast_zero] at hav
  have hcard : (Nat.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsum : ∑ g : G, rho.character g = 0 := (mul_eq_zero.mp hav).resolve_left hcard
  calc
    ∑ g : G, rho.character g⁻¹ = ∑ g : G, rho.character g := by
      simpa using Equiv.sum_comp (Equiv.inv G) rho.character
    _ = 0 := hsum

theorem b4_cyclicKernel_step (z : ℂ) (a m : ℕ) (ha : 0 < a) (hm : z ^ m ≠ 1) :
    z ^ m / (1 - z ^ m) * z ^ (a * m) -
        z ^ m / (1 - z ^ m) * z ^ ((a - 1) * m) = -z ^ (a * m) := by
  have hpow : (a - 1) * m + m = a * m := by
    calc
      (a - 1) * m + m = (a - 1) * m + 1 * m := by rw [one_mul]
      _ = ((a - 1) + 1) * m := (Nat.add_mul _ _ _).symm
      _ = a * m := by rw [Nat.sub_add_cancel ha]
  rw [← hpow, pow_add]
  field_simp [sub_ne_zero.mpr hm]
  ring

theorem b4_sum_cyclic_powers_eq_zero {z : ℂ} {n a : ℕ}
    (hz : IsPrimitiveRoot z n) (ha : 0 < a) (han : a < n) :
    ∑ m ∈ Finset.range n, z ^ (a * m) = 0 := by
  have hza : z ^ a ≠ 1 := hz.pow_ne_one_of_pos_of_lt ha.ne' han
  simp_rw [pow_mul]
  rw [geom_sum_eq hza, ← pow_mul, Nat.mul_comm a n, pow_mul, hz.pow_eq_one, one_pow,
    sub_self, zero_div]

theorem b4_sum_cyclic_powers_ne_zero {z : ℂ} {n a : ℕ}
    (hz : IsPrimitiveRoot z n) (hn : 0 < n) (ha : 0 < a) (han : a < n) :
    (∑ m ∈ Finset.range n, if m = 0 then 0 else z ^ (a * m)) = -1 := by
  have htotal := b4_sum_cyclic_powers_eq_zero hz ha han
  have hzero :
      (∑ m ∈ Finset.range n, (if m = 0 then z ^ (a * m) else 0)) = 1 := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hn)]
    simp
  calc
    (∑ m ∈ Finset.range n, (if m = 0 then 0 else z ^ (a * m))) =
        ∑ m ∈ Finset.range n,
          (z ^ (a * m) - (if m = 0 then z ^ (a * m) else 0)) := by
            apply Finset.sum_congr rfl
            intro m hm
            split_ifs <;> ring
    _ = (∑ m ∈ Finset.range n, z ^ (a * m)) -
        ∑ m ∈ Finset.range n, (if m = 0 then z ^ (a * m) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 - 1 := by rw [hzero, htotal]
    _ = -1 := by ring

def b4_cyclicKernel (z : ℂ) (n a : ℕ) : ℂ :=
  ∑ m ∈ Finset.range n,
    if m = 0 then 0 else z ^ m / (1 - z ^ m) * z ^ (a * m)

theorem b4_cyclicKernel_sub_pred {z : ℂ} {n a : ℕ}
    (hz : IsPrimitiveRoot z n) (hn : 0 < n) (ha : 0 < a) (han : a < n) :
    b4_cyclicKernel z n a - b4_cyclicKernel z n (a - 1) = 1 := by
  unfold b4_cyclicKernel
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ m ∈ Finset.range n,
        ((if m = 0 then 0 else z ^ m / (1 - z ^ m) * z ^ (a * m)) -
          if m = 0 then 0 else z ^ m / (1 - z ^ m) * z ^ ((a - 1) * m)) =
        ∑ m ∈ Finset.range n, if m = 0 then 0 else -z ^ (a * m) := by
          apply Finset.sum_congr rfl
          intro m hm
          by_cases hm0 : m = 0
          · simp [hm0]
          rw [if_neg hm0, if_neg hm0, b4_cyclicKernel_step z a m ha
            (hz.pow_ne_one_of_pos_of_lt hm0 (Finset.mem_range.mp hm)), if_neg hm0]
    _ = -(∑ m ∈ Finset.range n, if m = 0 then 0 else z ^ (a * m)) := by
      calc
        (∑ m ∈ Finset.range n, if m = 0 then 0 else -z ^ (a * m)) =
            ∑ m ∈ Finset.range n, -(if m = 0 then 0 else z ^ (a * m)) := by
              apply Finset.sum_congr rfl
              intro m hm
              split_ifs <;> simp
        _ = -(∑ m ∈ Finset.range n, if m = 0 then 0 else z ^ (a * m)) := by
          rw [Finset.sum_neg_distrib]
    _ = 1 := by rw [b4_sum_cyclic_powers_ne_zero hz hn ha han]; ring

theorem b4_cyclicKernel_sub_zero {z : ℂ} {n a : ℕ}
    (hz : IsPrimitiveRoot z n) (hn : 0 < n) (han : a < n) :
    b4_cyclicKernel z n a - b4_cyclicKernel z n 0 = (a : ℂ) := by
  induction a with
  | zero => simp
  | succ a ih =>
      have ha_lt : a < n := Nat.lt_trans (Nat.lt_succ_self a) han
      have hstep := b4_cyclicKernel_sub_pred hz hn (Nat.succ_pos a) han
      rw [Nat.succ_sub_one] at hstep
      rw [show b4_cyclicKernel z n (a + 1) - b4_cyclicKernel z n 0 =
          (b4_cyclicKernel z n (a + 1) - b4_cyclicKernel z n a) +
            (b4_cyclicKernel z n a - b4_cyclicKernel z n 0) by ring,
        hstep, ih ha_lt]
      push_cast
      ring

theorem b4_angle_exp_power {n a : ℕ} (hn : 0 < n) (ha : a < n) :
    g32h_angle (Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) ^ a) =
      (a : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (a : ℝ) < n := by exact_mod_cast ha
  rw [← Complex.exp_nat_mul]
  have hexp : (a : ℂ) * (2 * Real.pi * Complex.I / (n : ℂ)) =
      (((2 * Real.pi * a / n : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [hexp, g32h_angle, Complex.arg_exp_mul_I, toIcoMod_toIocMod]
  rw [(toIcoMod_eq_self Real.two_pi_pos).2]
  · field_simp [Real.pi_ne_zero]
  constructor
  · positivity
  · rw [zero_add]
    apply (div_lt_iff₀' hnR).2
    nlinarith [Real.pi_pos]

theorem b4_rootOfUnity_index {n : ℕ} (hn : 0 < n) {l : ℂ} (hl : l ^ n = 1) :
    ∃ a < n,
      Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) ^ a = l ∧
        g32h_angle l = (a : ℝ) / n := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨a, ha, hal⟩ := hz.eq_pow_of_pow_eq_one hl
  refine ⟨a, ha, hal, ?_⟩
  rw [← hal]
  exact b4_angle_exp_power hn ha

def b4_cyclicRootKernel (z l : ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range n,
    if m = 0 then 0 else z ^ m / (1 - z ^ m) * l ^ m

theorem b4_cyclicRootKernel_sub_one {n : ℕ} (hn : 0 < n) {l : ℂ} (hl : l ^ n = 1) :
    let z := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
    b4_cyclicRootKernel z l n - b4_cyclicRootKernel z 1 n =
      (n : ℂ) * g32h_angle l := by
  dsimp only
  obtain ⟨a, ha, hal, hangle⟩ := b4_rootOfUnity_index hn hl
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hfirst : b4_cyclicRootKernel z l n = b4_cyclicKernel z n a := by
    unfold b4_cyclicRootKernel b4_cyclicKernel
    apply Finset.sum_congr rfl
    intro m hm
    rw [← hal, pow_mul]
  have hone : b4_cyclicRootKernel z 1 n = b4_cyclicKernel z n 0 := by
    unfold b4_cyclicRootKernel b4_cyclicKernel
    apply Finset.sum_congr rfl
    intro m hm
    simp
  rw [hfirst, hone, b4_cyclicKernel_sub_zero hz hn ha, hangle]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

theorem b4_trace_pow_eq_sum_roots {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (hT : Module.End.IsSemisimple T) (m : ℕ) :
    LinearMap.trace ℂ W (T ^ m) = (T.charpoly.roots.map fun l ↦ l ^ m).sum := by
  classical
  let s : Finset ℂ := T.charpoly.roots.toFinset
  let p : s → Submodule ℂ W := fun l ↦ Module.End.eigenspace T l
  have hp_ind : iSupIndep p :=
    (Module.End.eigenspaces_iSupIndep T).comp Subtype.val_injective
  have hp_top : ⨆ l, p l = ⊤ := by
    apply top_unique
    rw [← hT.iSup_eigenspace_eq_top]
    refine iSup_le fun l ↦ ?_
    by_cases hl : Module.End.eigenspace T l ≠ ⊥
    · have hlroot : l ∈ T.charpoly.roots :=
        (Polynomial.mem_roots (LinearMap.charpoly_monic T).ne_zero).2
          ((Module.End.hasEigenvalue_iff_isRoot_charpoly T l).1
            (Module.End.hasEigenvalue_iff.mpr hl))
      exact le_iSup_of_le ⟨l, by simpa [s] using hlroot⟩ (le_rfl)
    · have hbot : Module.End.eigenspace T l = ⊥ := not_ne_iff.mp hl
      simp [hbot]
  let e : (Π₀ l, p l) ≃ₗ[ℂ] W := hp_ind.linearEquiv hp_top
  let bsub : ∀ l, Module.Basis (Module.Free.ChooseBasisIndex ℂ (p l)) ℂ (p l) :=
    fun l ↦ Module.Free.chooseBasis ℂ (p l)
  let b : Module.Basis (Σ l, Module.Free.ChooseBasisIndex ℂ (p l)) ℂ W :=
    (DFinsupp.basis bsub).map e
  have hb_mem (l) (i : Module.Free.ChooseBasisIndex ℂ (p l)) :
      b ⟨l, i⟩ ∈ Module.End.eigenspace T l := by
    have hb : b ⟨l, i⟩ = (bsub l i : W) := by
      change e ((DFinsupp.basis bsub) ⟨l, i⟩) = _
      have hbasis : (DFinsupp.basis bsub) ⟨l, i⟩ = DFinsupp.single l (bsub l i) := by
        ext j
        simp [DFinsupp.basis, bsub]
      rw [hbasis]
      change (DFinsupp.lsum ℕ fun i ↦ (p i).subtype) (DFinsupp.single l (bsub l i)) = _
      rw [DFinsupp.lsum_single]
      rfl
    rw [hb]
    exact (bsub l i).2
  have hpow (l) (i : Module.Free.ChooseBasisIndex ℂ (p l)) :
      (T ^ m) (b ⟨l, i⟩) = (l : ℂ) ^ m • b ⟨l, i⟩ := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Module.End.mul_apply,
          (Module.End.mem_eigenspace_iff.mp (hb_mem l i)), map_smul, ih, smul_smul, pow_succ]
        ring_nf
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, ← Finset.univ_sigma_univ,
    Finset.sum_sigma]
  simp_rw [Matrix.diag, LinearMap.toMatrix_apply, hpow, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, Finsupp.single_eq_same]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hr : (T.charpoly.roots.map fun l ↦ l ^ m).sum =
      ∑ l ∈ T.charpoly.roots.toFinset, T.charpoly.roots.count l • l ^ m := by
    conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq T.charpoly.roots]
    change Multiset.sum ((Multiset.mapAddMonoidHom fun l ↦ l ^ m)
      (∑ l ∈ T.charpoly.roots.toFinset, T.charpoly.roots.count l • {l})) = _
    rw [map_sum]
    change Multiset.sumAddMonoidHom
      (∑ l ∈ T.charpoly.roots.toFinset,
        (Multiset.mapAddMonoidHom fun l ↦ l ^ m) (T.charpoly.roots.count l • {l})) = _
    rw [map_sum Multiset.sumAddMonoidHom]
    apply Finset.sum_congr rfl
    intro l hl
    change (Multiset.map (fun l ↦ l ^ m) (T.charpoly.roots.count l • {l})).sum = _
    rw [Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
      Multiset.sum_singleton, nsmul_eq_mul]
  rw [hr]
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
  have hsums : (∑ l ∈ T.charpoly.roots.toFinset,
      (T.charpoly.roots.count l : ℂ) * l ^ m) =
      ∑ l : s, (T.charpoly.roots.count (l : ℂ) : ℂ) * (l : ℂ) ^ m := by
    symm
    simpa [s] using Finset.sum_attach T.charpoly.roots.toFinset
      (fun l ↦ (T.charpoly.roots.count (l : ℂ) : ℂ) * (l : ℂ) ^ m)
  rw [hsums]
  apply Finset.sum_congr rfl
  intro l hl
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℂ (p l)) =
      T.charpoly.roots.count (l : ℂ) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    change Module.finrank ℂ (Module.End.eigenspace T (l : ℂ)) = _
    exact (HurwitzPrymRex_count_roots hT (l : ℂ)).symm
  rw [hc]

theorem b4_root_pow_of_end_pow {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {T : W →ₗ[ℂ] W} {n : ℕ} (hT : T ^ n = 1) {l : ℂ}
    (hl : l ∈ T.charpoly.roots) : l ^ n = 1 := by
  have hroot := (Polynomial.mem_roots (LinearMap.charpoly_monic T).ne_zero).1 hl
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly T l).2 hroot).exists_hasEigenvector
  have hpow : ∀ k : ℕ, (T ^ k) v = l ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, hv.apply_eq_smul, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have hn := hpow n
  rw [hT, Module.End.one_apply] at hn
  have hz : (l ^ n - 1) • v = 0 := by rw [sub_smul, ← hn, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv.2)

theorem b4_finset_multiset_sum_comm {R α β : Type*} [AddCommMonoid R] (s : Finset α)
    (q : Multiset β) (f : α → β → R) :
    ∑ i ∈ s, (q.map (f i)).sum = (q.map fun x ↦ ∑ i ∈ s, f i x).sum := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons x q ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [← ih, Finset.sum_add_distrib]

theorem b4_cyclic_trace_kernel_eq_root_sum {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (hT : Module.End.IsSemisimple T)
    (z : ℂ) (n : ℕ) :
    ∑ m ∈ Finset.range n, (if m = 0 then 0 else z ^ m / (1 - z ^ m)) *
      LinearMap.trace ℂ W (T ^ m) =
      (T.charpoly.roots.map fun l ↦ b4_cyclicRootKernel z l n).sum := by
  simp_rw [b4_trace_pow_eq_sum_roots T hT]
  calc
    (∑ m ∈ Finset.range n, (if m = 0 then 0 else z ^ m / (1 - z ^ m)) *
        (T.charpoly.roots.map fun l ↦ l ^ m).sum) =
        ∑ m ∈ Finset.range n,
          (T.charpoly.roots.map fun l ↦
            (if m = 0 then 0 else z ^ m / (1 - z ^ m)) * l ^ m).sum := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Multiset.sum_map_mul_left]
    _ = (T.charpoly.roots.map fun l ↦ ∑ m ∈ Finset.range n,
          (if m = 0 then 0 else z ^ m / (1 - z ^ m)) * l ^ m).sum :=
      b4_finset_multiset_sum_comm (Finset.range n) T.charpoly.roots _
    _ = (T.charpoly.roots.map fun l ↦ b4_cyclicRootKernel z l n).sum := by
      congr 2
      funext l
      unfold b4_cyclicRootKernel
      apply Finset.sum_congr rfl
      intro m hm
      split_ifs <;> ring

theorem b4_cyclic_trace_kernel_sub_trivial {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) {n : ℕ} (hn : 0 < n)
    (hTpow : T ^ n = 1) :
    let z := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
    (∑ m ∈ Finset.range n, (if m = 0 then 0 else z ^ m / (1 - z ^ m)) *
        LinearMap.trace ℂ W (T ^ m)) -
      (T.charpoly.roots.map fun _ ↦ b4_cyclicRootKernel z 1 n).sum =
        (n : ℂ) * (b4_age T : ℂ) := by
  dsimp only
  have hsemi := HurwitzPrymRex_isSemisimple hn.ne' hTpow
  rw [b4_cyclic_trace_kernel_eq_root_sum T hsemi]
  rw [← Multiset.sum_map_sub]
  rw [Multiset.map_congr rfl (fun l hl ↦
    b4_cyclicRootKernel_sub_one hn (b4_root_pow_of_end_pow hTpow hl))]
  rw [Multiset.sum_map_mul_left]
  unfold b4_age
  push_cast
  congr 1
  induction T.charpoly.roots using Multiset.induction_on with
  | empty => simp
  | cons l q ih => simp [ih]

theorem b4_formRepresentation_invariants_eq_bot
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (hinv : b4_invariantForms E C G = ⊥) :
    Representation.invariants (b4_formRepresentation hG) = ⊥ := by
  apply bot_unique
  intro v hv
  have hv' : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ∈ b4_invariantForms E C G := by
    refine ⟨v.2, (Submodule.mem_iInf _).mpr fun g ↦ ?_⟩
    change b4_formAct E (C := C) g v.val - v.val = 0
    exact sub_eq_zero.mpr (congrArg Subtype.val (hv g))
  rw [hinv, Submodule.mem_bot] at hv'
  exact Subtype.ext hv'

theorem b4_formRepresentation_character_sum_eq_zero [T2Space C] [CompactSpace C]
    [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (hinv : b4_invariantForms E C G = ⊥) :
    ∑ g : G, (b4_formRepresentation hG).character g = 0 := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  have hav := Representation.card_inv_mul_sum_char_eq_finrank (b4_formRepresentation hG)
  rw [b4_formRepresentation_invariants_eq_bot hG hinv, finrank_bot, Nat.cast_zero] at hav
  exact (mul_eq_zero.mp hav).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))

def b4_fixedKernel (hE : Module.finrank ℂ E = 1) (g : G) (x : C) : ℂ :=
  if g = 1 then 0 else if g • x = x then
    b4cov_lam hE x g / (1 - b4cov_lam hE x g) else 0

theorem b4_fixedKernel_finiteSupport [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [FaithfulSMul G C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (g : G) :
    Function.HasFiniteSupport (b4_fixedKernel (C := C) hE g) := by
  apply (HurwitzPrymRex_fixedPoints_finite hE hG).subset
  intro x hx
  by_cases hg : g = 1
  · simp [b4_fixedKernel, hg] at hx
  by_cases hfix : g • x = x
  · exact ⟨g, hg, hfix⟩
  · simp [b4_fixedKernel, hg, hfix] at hx

theorem b4_lam_rotGen_pow
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (x : C) (k : G) (hk : b4_IsRotGen E x k) (m : ℕ) :
    b4cov_lam hE x (k ^ m) =
      Complex.exp (2 * Real.pi * Complex.I / (orderOf k : ℂ)) ^ m := by
  have hk' : b4cov_lam hE x k =
      Complex.exp (2 * Real.pi * Complex.I / (orderOf k : ℂ)) :=
    b4cov_lam_eq_of_apply hE x k _ hk.2.2
  induction m with
  | zero => simpa using b4cov_lam_one hE (G := G) x
  | succ m ih => rw [pow_succ, b4cov_lam_mul hE hG x _ _ hk.1, ih, hk', pow_succ]

theorem b4_sum_fixed_eq_sum_rotGen_powers {R : Type*} [AddCommMonoid R]
    (x : C) (k : G) (hk : b4_IsRotGen E x k) (f : G → R) :
    (∑ g : G, if g • x = x then f g else 0) =
      ∑ m ∈ Finset.range (orderOf k), f (k ^ m) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun m _ ↦ k ^ m)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (MulAction.stabilizer G x).pow_mem hk.1 m
  · intro a ha b hb hab
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab
  · intro g hg
    obtain ⟨m, hm, hmg⟩ := b4_fixed_element_is_rotGen_power x k g hk
      (Finset.mem_filter.mp hg).2
    exact ⟨m, Finset.mem_range.mpr hm, hmg.symm⟩
  · intro m hm
    rfl

theorem b4_holo_multiplicity_fixedKernel [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [FaithfulSMul G C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (hinv : b4_invariantForms E C G = ⊥)
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hρ : ∃ (g : G) (v : V), ρ g v ≠ v) :
    (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g)
      (b3_HolForm E C)) : ℂ) =
      -(Module.finrank ℂ V : ℂ) + (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, (∑ᶠ x : C, b4_fixedKernel hE g x) *
          (ρ.character g - (Module.finrank ℂ V : ℂ)) := by
  let d : ℂ := Module.finrank ℂ V
  let χ := (b4_formRepresentation hG).character
  have hχ : ∑ g : G, χ g⁻¹ = 0 := by
    calc
      _ = ∑ g : G, χ g := by simpa using Equiv.sum_comp (Equiv.inv G) χ
      _ = 0 := b4_formRepresentation_character_sum_eq_zero hE hG hinv
  have hρsum : ∑ g : G, ρ.character g = 0 := by
    have hs := b4_nontrivial_irreducible_character_sum_inv ρ hρ
    have he : (∑ g : G, ρ.character g⁻¹) = ∑ g : G, ρ.character g := by
      simpa using Equiv.sum_comp (Equiv.inv G) ρ.character
    rw [he] at hs
    exact hs
  have heq (g : G) : χ g⁻¹ * (ρ.character g - d) =
      (ρ.character g - d) + (∑ᶠ x : C, b4_fixedKernel hE g x) *
        (ρ.character g - d) := by
    by_cases hg : g = 1
    · subst g
      simp [d, Representation.char_one]
    · have ht := b4_formRepresentation_character_of_ne_one hE hG g⁻¹
        (inv_ne_one.mpr hg)
      simp only [inv_inv] at ht
      have hkernel : (∑ᶠ x : C, b4_fixedKernel hE g x) =
          ∑ᶠ x : C, if (b4_actionHomeomorph hG g) x = x then
            b4c_rotation hE (b4_actionHomeomorph hG g) x /
              (1 - b4c_rotation hE (b4_actionHomeomorph hG g) x) else 0 := by
        apply finsum_congr
        intro x
        simp only [b4_fixedKernel, if_neg hg]
        rfl
      rw [hkernel, show χ g⁻¹ = _ from ht]
      ring
  have hsum := congrArg (fun f : G → ℂ ↦ ∑ g : G, f g) (funext heq)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub,
    ← Finset.sum_mul, hχ, hρsum, zero_mul, zero_sub, sub_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [b4_homGForm_character_average hE hG ρ]
  have hchange : (∑ g : G, χ g * ρ.character g⁻¹) =
      ∑ g : G, χ g⁻¹ * ρ.character g := by
    simpa only [Equiv.inv_apply, inv_inv] using
      (Equiv.sum_comp (Equiv.inv G) (fun g ↦ χ g * ρ.character g⁻¹)).symm
  change (Nat.card G : ℂ)⁻¹ * (∑ g : G, χ g * ρ.character g⁻¹) = _
  rw [hchange, hsum]
  rw [Nat.card_eq_fintype_card]
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  dsimp only [d]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  field_simp

theorem b4_fixedKernel_character_sum
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (x : C) (k : G) (hk : b4_IsRotGen E x k) (ρ : Representation ℂ G V) :
    (∑ g : G, b4_fixedKernel hE g x *
      (ρ.character g - (Module.finrank ℂ V : ℂ))) =
      (Nat.card (MulAction.stabilizer G x) : ℂ) * (b4_age (ρ k) : ℂ) := by
  let z := Complex.exp (2 * Real.pi * Complex.I / (orderOf k : ℂ))
  have hpow : (ρ k) ^ orderOf k = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hlocal := b4_cyclic_trace_kernel_sub_trivial (ρ k) (orderOf_pos k) hpow
  dsimp only at hlocal
  have hcyc : (∑ m ∈ Finset.range (orderOf k),
      (if m = 0 then 0 else z ^ m / (1 - z ^ m)) *
        (LinearMap.trace ℂ V ((ρ k) ^ m) - (Module.finrank ℂ V : ℂ))) =
      (orderOf k : ℂ) * (b4_age (ρ k) : ℂ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    convert hlocal using 1
    congr 1
    simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
      IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_natDegree]
    unfold b4_cyclicRootKernel
    simp only [one_pow, mul_one]
    rw [mul_comm (Module.finrank ℂ V : ℂ)]
  calc
    (∑ g : G, b4_fixedKernel hE g x *
        (ρ.character g - (Module.finrank ℂ V : ℂ))) =
        ∑ g : G, if g • x = x then b4_fixedKernel hE g x *
          (ρ.character g - (Module.finrank ℂ V : ℂ)) else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hf : g • x = x
      · rw [if_pos hf]
      · simp [b4_fixedKernel, hf]
    _ = ∑ m ∈ Finset.range (orderOf k), b4_fixedKernel hE (k ^ m) x *
          (ρ.character (k ^ m) - (Module.finrank ℂ V : ℂ)) :=
      b4_sum_fixed_eq_sum_rotGen_powers x k hk _
    _ = ∑ m ∈ Finset.range (orderOf k),
        (if m = 0 then 0 else z ^ m / (1 - z ^ m)) *
          (LinearMap.trace ℂ V ((ρ k) ^ m) - (Module.finrank ℂ V : ℂ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hfix : k ^ m • x = x := (MulAction.stabilizer G x).pow_mem hk.1 m
      have hone : k ^ m = 1 ↔ m = 0 := by
        constructor
        · intro he
          exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hm) (orderOf_pos k)
            (he.trans (pow_zero k).symm)
        · rintro rfl
          exact pow_zero k
      simp only [b4_fixedKernel, hone, if_pos hfix, b4_lam_rotGen_pow hE hG x k hk,
        Representation.character, map_pow]
      rfl
    _ = (orderOf k : ℂ) * (b4_age (ρ k) : ℂ) := hcyc
    _ = _ := by rw [hk.2.1]

theorem b4_chevalleyWeil_holo_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul G C]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (hinv : b4_invariantForms E C G = ⊥) (h : C → G) (hh : ∀ x, b4_IsRotGen E x (h x))
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (hρ : ∃ (g : G) (v : V), ρ g v ≠ v) :
    (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)) : ℝ) =
      ∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G * b4_age (ρ (h x)) -
        Module.finrank ℂ V := by
  have hmult := b4_holo_multiplicity_fixedKernel hE hG hinv ρ hρ
  have hfin (g : G) : Function.HasFiniteSupport (fun x : C ↦
      b4_fixedKernel hE g x * (ρ.character g - (Module.finrank ℂ V : ℂ))) := by
    apply (b4_fixedKernel_finiteSupport hE hG g).subset
    intro x hx
    exact fun hz ↦ hx (by dsimp only; rw [hz, zero_mul])
  have hswap : (∑ g : G, (∑ᶠ x : C, b4_fixedKernel hE g x) *
      (ρ.character g - (Module.finrank ℂ V : ℂ))) =
      ∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℂ) * (b4_age (ρ (h x)) : ℂ) := by
    simp_rw [finsum_mul]
    rw [← finsum_sum_comm Finset.univ _ (fun g _ ↦ hfin g)]
    apply finsum_congr
    intro x
    exact b4_fixedKernel_character_sum hE hG x (h x) (hh x) ρ
  rw [hswap, mul_finsum] at hmult
  have hcast := Complex.ofRealHom.toAddMonoidHom.map_finsum_of_injective
    Complex.ofReal_injective (fun x : C ↦
      (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G * b4_age (ρ (h x)))
  change ((∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) /
    Fintype.card G * b4_age (ρ (h x)) : ℝ) : ℂ) = _ at hcast
  have hsum : (∑ᶠ x : C, (Nat.card G : ℂ)⁻¹ *
      ((Nat.card (MulAction.stabilizer G x) : ℂ) * (b4_age (ρ (h x)) : ℂ))) =
      ((∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) /
        Fintype.card G * b4_age (ρ (h x)) : ℝ) : ℂ) := by
    rw [hcast]
    apply finsum_congr
    intro x
    change _ = (((Nat.card (MulAction.stabilizer G x) : ℝ) /
      Fintype.card G * b4_age (ρ (h x)) : ℝ) : ℂ)
    push_cast
    rw [Nat.card_eq_fintype_card]
    ring
  rw [hsum, add_comm, ← sub_eq_add_neg] at hmult
  exact_mod_cast hmult

theorem b4_chevalleyWeil_top_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [FaithfulSMul G C]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (hinv : b4_invariantForms E C G = ⊥) (h : C → G) (hh : ∀ x, b4_IsRotGen E x (h x))
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (hρ : ∃ (g : G) (v : V), ρ g v ≠ v) :
    (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g) ⊤) : ℝ) =
      ∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G *
          Module.finrank ℂ (LinearMap.range (ρ (h x) - LinearMap.id)) -
        2 * Module.finrank ℂ V := by
  set S := {x : C | ∃ k : G, k ≠ 1 ∧ k • x = x}
  have hfin : S.Finite := HurwitzPrymRex_fixedPoints_finite hE hG
  have hh1 : ∀ x, x ∉ S → h x = 1 := fun x hx ↦ by
    by_contra hne
    exact hx ⟨h x, hne, (hh x).1⟩
  set w : C → ℝ := fun x ↦ (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G
  have hA : (Function.support fun x ↦ w x * b4_age (ρ (h x))).Finite :=
    hfin.subset fun x hx ↦ by
      by_contra hxS
      apply hx
      simp only [hh1 x hxS, (HurwitzPrymRex_age_one ρ).1, mul_zero]
  have hB : (Function.support fun x ↦ w x * b4_age (HurwitzPrymRex_barRep ρ (h x))).Finite :=
    hfin.subset fun x hx ↦ by
      by_contra hxS
      apply hx
      simp only [hh1 x hxS, (HurwitzPrymRex_age_one ρ).2, mul_zero]
  have c1 := b4_chevalleyWeil_holo_aux hE hG hinv h hh ρ hρ
  have c2 := b4_chevalleyWeil_holo_aux hE hG hinv h hh (HurwitzPrymRex_barRep ρ)
    (HurwitzPrymRex_barRep_nontrivial ρ hρ)
  rw [HurwitzPrymRex_Bar.finrank_eq] at c2
  have hsplit := b4_homG_split_aux hE hG ρ
  have e1 := b4_hodge_eq_holo_aux hE hG ρ
  have e2 : Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g)
      (b2_conjSubmodule _ (b3_periodF E C))) =
      Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep ρ) (fun g ↦ b4_cplxAct E (C := C) g)
        (b3_periodF E C)) :=
    HurwitzPrymRex_finrank_homG_bar (fun g ↦ b4_latticeAct E (C := C) g) (b3_periodF E C) ρ
  have e3 := b4_hodge_eq_holo_aux hE hG (HurwitzPrymRex_barRep ρ)
  have hsum : ∑ᶠ x : C, w x * (Module.finrank ℂ (LinearMap.range (ρ (h x) - LinearMap.id)) : ℝ) =
      (∑ᶠ x : C, w x * b4_age (HurwitzPrymRex_barRep ρ (h x))) +
        ∑ᶠ x : C, w x * b4_age (ρ (h x)) := by
    rw [← finsum_add_distrib hB hA]
    exact finsum_congr fun x ↦ by rw [← mul_add, HurwitzPrymRex_age_add_bar]
  have hsplit' : (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g) ⊤) : ℝ) =
      Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)) +
        Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep ρ)
          (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)) := by
    exact_mod_cast hsplit.trans (congrArg₂ (· + ·) e1 (e2.trans e3))
  change _ = ∑ᶠ x : C, w x * (Module.finrank ℂ (LinearMap.range (ρ (h x) - LinearMap.id)) : ℝ) -
    2 * (Module.finrank ℂ V : ℝ)
  change _ = ∑ᶠ x : C, w x * b4_age (ρ (h x)) - _ at c1
  change _ = ∑ᶠ x : C, w x * b4_age (HurwitzPrymRex_barRep ρ (h x)) - _ at c2
  rw [hsplit', hsum, c1, c2]
  ring

end ChevalleyWeil

/-! ## Images of endomorphisms and isotypic ranks -/

section Isotypic

theorem b4_finrank_imageQuot_aux {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (f : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap f)) :
    Module.finrank ℂ ((ℂ ⊗[ℤ] f.range) ⧸ b2_imageF F f) =
      Module.finrank ℂ ((b2_conjSubmodule Λ F).map (b2_cplxMap f)) := by
  exact b4cov_finrank_imageQuot F hF f hf

theorem b4_finrank_imageF_aux {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (f : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap f)) :
    Module.finrank ℂ (b2_imageF F f) = Module.finrank ℂ (F.map (b2_cplxMap f)) := by
  exact b4cov_finrank_imageF F hF f hf

theorem b4_finrank_map_isotypic_aux {G : Type} [Group G] [Fintype G]
    {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (σ : Representation ℂ G M) (W : Submodule ℂ M) (hW : ∀ g, W ≤ W.comap (σ g))
    {k : ℕ} {V : Fin k → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (hdist : ∀ i j, i ≠ j → ∀ φ : Representation.IntertwiningMap (ρ i) (ρ j), φ = 0)
    (a : G → ℂ)
    (hkill : ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ G V'), ρ'.IsIrreducible →
        (∀ i, ∀ φ : Representation.IntertwiningMap ρ' (ρ i), φ = 0) → ∑ g, a g • ρ' g = 0) :
    Module.finrank ℂ (W.map (∑ g, a g • σ g)) =
      ∑ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) W) *
        Module.finrank ℂ (LinearMap.range (∑ g, a g • ρ i g)) := by
  exact b4cov_finrank_map_isotypic σ ρ hdist a hkill W hW

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [Fintype G] [MulAction G C]

theorem b4_prym_finrank_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (σ : Representation ℂ G (ℂ ⊗[ℤ] b3_periodLattice E C)) (hσ : ∀ g, σ g = b4_cplxAct E g)
    {k : ℕ} {V : Fin k → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (hdist : ∀ i j, i ≠ j → ∀ φ : Representation.IntertwiningMap (ρ i) (ρ j), φ = 0)
    (a : G → ℤ)
    (hkill : ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ G V'), ρ'.IsIrreducible →
        (∀ i, ∀ φ : Representation.IntertwiningMap ρ' (ρ i), φ = 0) →
          ∑ g, (a g : ℂ) • ρ' g = 0) :
    Module.finrank ℂ ((ℂ ⊗[ℤ] (b4_groupEnd E (C := C) a).range) ⧸ b4_prymF E a) =
      ∑ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) (b2_conjSubmodule _ (b3_periodF E C))) *
        Module.finrank ℂ (LinearMap.range (∑ g, (a g : ℂ) • ρ i g)) := by
  have := b3_periodLattice_finite (C := C) hE
  have := b3_periodLattice_free (E := E) (C := C)
  rw [b4_prymF, b4cov_finrank_imageQuot _ (b3_isWeightOne hE) _ (b4_groupEnd_periodF_aux hG a),
    b4_cplxMap_groupEnd_aux,
    show (∑ g, (a g : ℂ) • b4_cplxAct E (C := C) g) = ∑ g, (a g : ℂ) • σ g from
      Finset.sum_congr rfl fun g _ ↦ by rw [hσ]]
  exact b4cov_finrank_map_isotypic σ ρ hdist (fun g ↦ (a g : ℂ)) hkill _
    fun g ↦ (hσ g).symm ▸ b4_cplxAct_conjF_aux hG g

theorem b4_prymF_finrank_aux [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (σ : Representation ℂ G (ℂ ⊗[ℤ] b3_periodLattice E C)) (hσ : ∀ g, σ g = b4_cplxAct E g)
    {k : ℕ} {V : Fin k → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (hdist : ∀ i j, i ≠ j → ∀ φ : Representation.IntertwiningMap (ρ i) (ρ j), φ = 0)
    (a : G → ℤ)
    (hkill : ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ G V'), ρ'.IsIrreducible →
        (∀ i, ∀ φ : Representation.IntertwiningMap ρ' (ρ i), φ = 0) →
          ∑ g, (a g : ℂ) • ρ' g = 0) :
    Module.finrank ℂ (b4_prymF E (C := C) a) =
      ∑ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) (b3_periodF E C)) *
        Module.finrank ℂ (LinearMap.range (∑ g, (a g : ℂ) • ρ i g)) := by
  have := b3_periodLattice_finite (C := C) hE
  rw [b4_prymF, b4cov_finrank_imageF _ (b3_isWeightOne hE) _ (b4_groupEnd_periodF_aux hG a),
    b4_cplxMap_groupEnd_aux,
    show (∑ g, (a g : ℂ) • b4_cplxAct E (C := C) g) = ∑ g, (a g : ℂ) • σ g from
      Finset.sum_congr rfl fun g _ ↦ by rw [hσ]]
  exact b4cov_finrank_map_isotypic σ ρ hdist (fun g ↦ (a g : ℂ)) hkill _
    fun g ↦ (hσ g).symm ▸ b4_cplxAct_periodF_aux hG g

end Isotypic

/-! ## Riemann existence -/

section Existence

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

theorem b4_exists_genusZero_aux :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace ℂ Y) (_ : IsManifold 𝓘(ℂ, ℂ) ω Y)
      (_ : T2Space Y) (_ : CompactSpace Y) (_ : ConnectedSpace Y) (_ : Nonempty Y),
      Module.finrank ℂ (b3_HolForm ℂ Y) = 0 := by
  exact b4cov_exists_genusZero

theorem b4_exists_galoisCovering_aux [T2Space Y] [ConnectedSpace Y]
    (hE' : Module.finrank ℂ E' = 1) (B : Set Y) (hB : B.Finite) (y₀ : {y : Y // y ∉ B})
    {G : Type} [Group G] [Finite G] (φ : FundamentalGroup {y : Y // y ∉ B} y₀ →* Gᵐᵒᵖ)
    (hφ : Function.Surjective φ) :
    ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction G U) (p : U → {y : Y // y ∉ B})
      (hp : IsQuotientCoveringMap p G),
      ConnectedSpace U ∧ ∃ e : p ⁻¹' {y₀}, hp.fundamentalGroupToMulOpposite e = φ := by
  have := HurwitzPrymRexCover.pathConnectedSpace_compl E' hE' hB y₀
  exact HurwitzPrymRexCover.exists_galoisCovering
    (fun x N hN ↦ HurwitzPrymRexCover.good_nhds E' hB x N hN) φ hφ

theorem b4_extend_galoisCovering_aux (hE : Module.finrank ℂ E = 1)
    [Nonempty Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    (B : Set Y) (hB : B.Finite) {G : Type} [Group G] [Finite G]
    {U : Type} [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (p : U → {y : Y // y ∉ B}) (hp : IsQuotientCoveringMap p G) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace E C) (_ : IsManifold 𝓘(ℂ, E) ω C)
      (_ : T2Space C) (_ : CompactSpace C) (_ : ConnectedSpace C) (_ : Nonempty C)
      (_ : MulAction G C)
      (f : C → Y) (ι : U → C),
      (∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) ∧
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f ∧ b4_IsGaloisCover G f ∧
      Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' Bᶜ ∧
      (∀ u, f (ι u) = p u) ∧ ∀ (g : G) (u : U), ι (g • u) = g • ι u := by
  exact HurwitzPrymRexFill.extend hE hE' B hB p hp

theorem b4_punctured_presentation_aux (hE : Module.finrank ℂ E = 1)
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    (hY : Module.finrank ℂ (b3_HolForm E' Y) = 0)
    {r : ℕ} (b : Fin r → Y) (hb : Function.Injective b) (y₀ : {y : Y // y ∉ Set.range b}) :
    ∃ γ : Fin r → FundamentalGroup {y : Y // y ∉ Set.range b} y₀,
      (List.ofFn γ).prod = 1 ∧
      (∀ (H : Type) [Group H] (k : Fin r → H), (List.ofFn k).prod = 1 →
        ∃! φ : FundamentalGroup {y : Y // y ∉ Set.range b} y₀ →* H, ∀ j, φ (γ j) = k j) ∧
      ∀ (C : Type) [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
        [CompactSpace C] [ConnectedSpace C] (G : Type) [Group G] [Finite G] [MulAction G C]
        [FaithfulSMul G C],
        (∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) →
        ∀ f : C → Y, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f → b4_IsGaloisCover G f →
        (∀ x, f x ∉ Set.range b → MulAction.stabilizer G x = ⊥) →
        ∀ (j : Fin r) (c : Path y₀ y₀), FundamentalGroup.fromPath ⟦c⟧ = γ j →
        ∀ (Γ : C(unitInterval, C)) (k : G), (∀ t, f (Γ t) = (c t : Y)) → Γ 1 = k • Γ 0 →
          ∃ x, f x = b j ∧ b4_IsRotGen E x k := by
  obtain ⟨e, he, heinv⟩ := b4c_genusZero_equiv hE' hY
  let b' : Fin r → OnePoint ℂ := e ∘ b
  have hb' : Function.Injective b' := e.injective.comp hb
  let eB : {y : Y // y ∉ Set.range b} ≃ₜ
      {y : OnePoint ℂ // y ∉ Set.range b'} :=
    e.subtype (fun y ↦ by simp [b', Set.mem_range, Function.comp_def])
  obtain ⟨δ, hp, hu, hm⟩ := b4c_pi1_puncturedSphere b' hb' (eB y₀)
  obtain ⟨g, hg⟩ := RiemannRochTop_homeomorph_pi1_map eB y₀
  refine ⟨fun i ↦ g.symm (δ i), ?_, ?_, ?_⟩
  · have h := congrArg g.symm hp
    simpa only [map_list_prod, List.map_ofFn, Function.comp_def, map_one] using h
  · intro H _ v hv
    obtain ⟨φ, hφ, huniq⟩ := hu H v hv
    refine ⟨φ.comp g.toMonoidHom, ?_, ?_⟩
    · intro i
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, g.apply_symm_apply] using hφ i
    · intro ψ hψ
      have heq : ψ.comp g.symm.toMonoidHom = φ := huniq _ hψ
      ext x
      have hx := congrArg (fun q ↦ q (g x)) heq
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, g.symm_apply_apply] using hx
  · intro C _ _ _ _ _ _ G _ _ _ _ hG f hf hgal hfree i c hc Γ k hΓ hend
    have hgal' : b4_IsGaloisCover G (e ∘ f) := by
      refine ⟨fun l x ↦ congrArg e (hgal.1 l x), ?_⟩
      intro x z hxz
      exact hgal.2 x z (e.injective hxz)
    have hfree' : ∀ x, (e ∘ f) x ∉ Set.range b' →
        MulAction.stabilizer G x = ⊥ := by
      intro x hx
      apply hfree x
      rintro ⟨j, hj⟩
      exact hx ⟨j, congrArg e hj⟩
    have hc' : FundamentalGroup.fromPath ⟦c.map eB.continuous⟧ = δ i := by
      rw [← hg, hc, g.apply_symm_apply]
    obtain ⟨q, hq, hrot⟩ := hm E hE C G hG (e ∘ f) (he.comp hf) hgal' hfree'
      i (c.map eB.continuous) hc' Γ k (fun t ↦ congrArg e (hΓ t)) hend
    exact ⟨q, e.injective hq, hrot⟩

theorem b4_riemannExistence_aux (hE : Module.finrank ℂ E = 1)
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    (hY : Module.finrank ℂ (b3_HolForm E' Y) = 0)
    {G : Type} [Group G] [Finite G] {r : ℕ} (g : Fin r → G) (hg : b4_Nielsen g)
    (b : Fin r → Y) (hb : Function.Injective b) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace E C) (_ : IsManifold 𝓘(ℂ, E) ω C)
      (_ : T2Space C) (_ : CompactSpace C) (_ : ConnectedSpace C) (_ : Nonempty C)
      (_ : MulAction G C)
      (_ : FaithfulSMul G C) (f : C → Y),
      (∀ h : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ h • x)) ∧
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f ∧ b4_IsGaloisCover G f ∧
      (∀ x, f x ∉ Set.range b → MulAction.stabilizer G x = ⊥) ∧
      ∀ j, ∃ x, f x = b j ∧ b4_IsRotGen E x (g j) := by
  set b' : Fin r → Y := b ∘ Fin.rev
  have hb' : Function.Injective b' := hb.comp Fin.rev_injective
  have hrange : Set.range b' = Set.range b := Fin.rev_surjective.range_comp b
  have hBfin : (Set.range b').Finite := Set.finite_range b'
  obtain ⟨y₀, hy₀⟩ := HurwitzPrymRR_exists_not_mem hE' hBfin
  obtain ⟨γ, -, huniv, hlift⟩ :=
    b4_punctured_presentation_aux hE hE' hY b' hb' ⟨y₀, hy₀⟩
  obtain ⟨φ, hφ, -⟩ := huniv Gᵐᵒᵖ (fun j ↦ MulOpposite.op (g j.rev))
    ((HurwitzPrymRR_prod_op_rev g).trans (by rw [hg.1, MulOpposite.op_one]))
  have hφs : Function.Surjective φ := by
    intro z
    have hz : z.unop ∈ Subgroup.closure (Set.range g) := by rw [hg.2]; trivial
    have key : ∀ x ∈ Subgroup.closure (Set.range g), ∃ a, φ a = MulOpposite.op x := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨γ i.rev, by rw [hφ, Fin.rev_rev]⟩
      | one => exact ⟨1, by simp⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨c, hc⟩ := hy
        exact ⟨c * a, by rw [map_mul, ha, hc, MulOpposite.op_mul]⟩
      | inv x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨a⁻¹, by rw [map_inv, ha, MulOpposite.op_inv]⟩
    obtain ⟨a, ha⟩ := key _ hz
    exact ⟨a, by rw [ha, MulOpposite.op_unop]⟩
  obtain ⟨U, _, _, p, hp, hUc, e, he⟩ :=
    b4_exists_galoisCovering_aux hE' (Set.range b') hBfin ⟨y₀, hy₀⟩ φ hφs
  obtain ⟨C, _, _, _, _, _, _, _, _, f, ι, hG, hf, hgal, hι, hιr, hfι, hιeq⟩ :=
    b4_extend_galoisCovering_aux (E := E) hE hE' (Set.range b') hBfin p hp
  have hfree : ∀ (k : G) (u : U), k • u = u → k = 1 := by
    intro k u hku
    obtain ⟨V, hV, hV'⟩ := hp.disjoint u
    exact hV' k ⟨u, ⟨u, mem_of_mem_nhds hV, hku⟩, mem_of_mem_nhds hV⟩
  have hstab : ∀ x, f x ∉ Set.range b' → MulAction.stabilizer G x = ⊥ := by
    intro x hx
    have : x ∈ Set.range ι := by rw [hιr]; exact hx
    obtain ⟨u, rfl⟩ := this
    rw [eq_bot_iff]
    intro k hk
    rw [MulAction.mem_stabilizer_iff, ← hιeq] at hk
    exact hfree k u (hι.injective hk)
  have hfaith : FaithfulSMul G C := by
    refine ⟨fun {k₁ k₂} h ↦ ?_⟩
    obtain ⟨u⟩ : Nonempty U := inferInstance
    have h1 : (k₂⁻¹ * k₁) • ι u = ι u := by rw [mul_smul, h, inv_smul_smul]
    rw [← hιeq] at h1
    have := hfree _ u (hι.injective h1)
    rwa [inv_mul_eq_one, eq_comm] at this
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hfaith, f, hG, hf, hgal,
    fun x hx ↦ hstab x (hrange ▸ hx), fun j ↦ ?_⟩
  obtain ⟨c, hc⟩ := Path.Homotopic.Quotient.mk_surjective (γ j.rev).toPath
  have hc' : FundamentalGroup.fromPath ⟦c⟧ = γ j.rev := congrArg FundamentalGroup.fromPath hc
  have hcov := hp.isCoveringMap
  let L := hcov.liftPath c.toContinuousMap e.1 (c.source.trans e.2.symm)
  have hL1 : L 1 = g j • e.1 := by
    have h1 := hcov.monodromy_eq_apply_one (γ := c) (e := e) (Γ := L) (hcov.liftPath_lifts _ _ _)
      (hcov.liftPath_zero _ _ _)
    have h2 := hp.unop_fundamentalGroupToMulOpposite_smul (e := e) (γ := γ j.rev)
    rw [he, hφ, Fin.rev_rev, MulOpposite.unop_op] at h2
    change L 1 = _
    rw [← h1, h2, show (γ j.rev).asHom = Path.Homotopic.Quotient.mk c from hc.symm]
  obtain ⟨x, hx, hrot⟩ := hlift C G hG f hf hgal hstab j.rev c hc'
    ⟨ι ∘ L, hι.continuous.comp L.continuous⟩ (g j) (fun t ↦ by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hfι]
      exact congrArg Subtype.val (congrFun (hcov.liftPath_lifts _ _ _) t))
    (by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hL1, hιeq]
      exact congrArg (g j • ·) (congrArg ι (hcov.liftPath_zero _ _ _).symm))
  exact ⟨x, by rw [hx]; simp [b'], hrot⟩

end Existence

/-! ## The explicit instance: `μ₄` on `ℂ ⧸ (ℤ + iℤ)` -/

section Elliptic

theorem b4_ellipticRot_contMDiff_aux (g : Multiplicative (ZMod 4)) :
    ContMDiff 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel) ω (fun x : b3_Elliptic ↦ g • x) := by
  exact HurwitzPrymAlg_ellipticScale_contMDiff (Multiplicative.toAdd g).val

theorem b4_ellipticRot_faithful_aux : FaithfulSMul (Multiplicative (ZMod 4)) b3_Elliptic := by
  constructor
  intro g h heq
  have hp : Complex.I ^ (Multiplicative.toAdd g).val =
      Complex.I ^ (Multiplicative.toAdd h).val :=
    HurwitzPrymAlg_ellipticScale_scalar_eq heq
  apply Multiplicative.ext
  apply ZMod.val_injective
  have hg := (Multiplicative.toAdd g).val_lt
  have hh := (Multiplicative.toAdd h).val_lt
  interval_cases (Multiplicative.toAdd g).val <;>
    interval_cases (Multiplicative.toAdd h).val
  all_goals norm_num [Complex.I_sq] at hp
  all_goals try norm_num
  all_goals have hi := congrArg Complex.im hp; norm_num at hi

theorem b4_ellipticRot_invariantForms_aux :
    b4_invariantForms b3_EllipticModel b3_Elliptic (Multiplicative (ZMod 4)) = ⊥ := by
  rw [eq_bot_iff]
  intro θ hθ
  have hhol : θ ∈ b3_HolForm b3_EllipticModel b3_Elliptic := hθ.1
  have hfix : θ ∈ LinearMap.ker
      (b4_formAct b3_EllipticModel (C := b3_Elliptic)
        (Multiplicative.ofAdd (1 : ZMod 4)) - LinearMap.id) := by
    exact (Submodule.mem_iInf _).mp hθ.2 (Multiplicative.ofAdd (1 : ZMod 4))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfix
  apply (Submodule.mem_bot ℂ).mpr
  funext p
  letI : ConnectedSpace b3_Elliptic := b3_elliptic_connectedSpace
  have hform := HurwitzPrymAlg2_torus_form_eq b2_stdF ⟨θ, hhol⟩
  change θ = HurwitzPrymAlg2_invForm b2_stdF (LinearMap.toContinuousLinearMap
    (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)) at hform
  have hp := congrFun hfix p
  change θ ⟨(Multiplicative.ofAdd (1 : ZMod 4))⁻¹ • p.1,
    mfderiv 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel)
      (fun x : b3_Elliptic ↦ (Multiplicative.ofAdd (1 : ZMod 4))⁻¹ • x) p.1 p.2⟩ = θ p at hp
  change θ ⟨_, mfderiv 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel)
    (b4_ellipticScale 3) p.1 p.2⟩ = θ p at hp
  have hd := HurwitzPrymAlg_ellipticScale_mfderiv 3 p.1 p.2
  change mfderiv 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel)
    (b4_ellipticScale 3) p.1 p.2 = Complex.I ^ (3 : ℕ) • p.2 at hd
  rw [congrFun hform _, congrFun hform _] at hp
  change (LinearMap.toContinuousLinearMap
      (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩))
        (mfderiv 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel)
          (b4_ellipticScale 3) p.1 p.2) =
    (LinearMap.toContinuousLinearMap
      (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)) p.2 at hp
  rw [hd] at hp
  have hm := (LinearMap.toContinuousLinearMap
    (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)).map_smul
      (Complex.I ^ (3 : ℕ)) p.2
  have hp' := hm.symm.trans hp
  have hi : Complex.I ^ (3 : ℕ) = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  rw [hi] at hp'
  have hne : (-Complex.I : ℂ) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hv : (LinearMap.toContinuousLinearMap
      (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)) p.2 = 0 :=
    (mul_eq_zero.mp (show
      (-Complex.I - 1) * (LinearMap.toContinuousLinearMap
        (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)) p.2 = 0 by
    calc
      ((-Complex.I - 1) * (LinearMap.toContinuousLinearMap
          (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)) p.2) =
          (-Complex.I) * (LinearMap.toContinuousLinearMap
            (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)) p.2 -
            (LinearMap.toContinuousLinearMap
              (HurwitzPrymAlg2_formFunctional b2_stdF ⟨θ, hhol⟩)) p.2 := by ring
      _ = 0 := sub_eq_zero.mpr hp')).resolve_left hne
  simpa [HurwitzPrymAlg2_invForm] using (congrFun hform p).trans hv

theorem b4_ellipticRot_rotGen_zero_aux :
    b4_IsRotGen b3_EllipticModel (0 : b3_Elliptic) (Multiplicative.ofAdd (1 : ZMod 4)) := by
  have hord : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  refine ⟨by change b4_ellipticScale 1 0 = 0; exact map_zero _, ?_, ?_⟩
  · have hstab : MulAction.stabilizer (Multiplicative (ZMod 4)) (0 : b3_Elliptic) = ⊤ := by
      ext g
      change g • (0 : b3_Elliptic) = 0 ↔ _
      change b4_ellipticScale (Multiplicative.toAdd g).val 0 = 0 ↔ _
      simp
    rw [hstab]
    simpa [Nat.card_eq_fintype_card] using hord
  · intro v
    change mfderiv (modelWithCornersSelf ℂ b3_EllipticModel)
      (modelWithCornersSelf ℂ b3_EllipticModel)
      (b4_ellipticScale 1) 0 v = _
    rw [HurwitzPrymAlg_ellipticScale_mfderiv]
    congr 1
    rw [hord]
    norm_num only [pow_one, Nat.cast_ofNat]
    rw [show 2 * (Real.pi : ℂ) * Complex.I / 4 = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I]
    simp

theorem HurwitzPrymAlg2_formAct_apply (g : Multiplicative (ZMod 4))
    (θ : b3_HolForm b3_EllipticModel b3_Elliptic) :
    b4_formAct b3_EllipticModel (C := b3_Elliptic) g θ =
      Complex.I ^ (Multiplicative.toAdd g⁻¹).val • θ := by
  funext p
  letI : ConnectedSpace b3_Elliptic := b3_elliptic_connectedSpace
  have hform := HurwitzPrymAlg2_torus_form_eq b2_stdF θ
  change (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ) =
    HurwitzPrymAlg2_invForm b2_stdF (LinearMap.toContinuousLinearMap
      (HurwitzPrymAlg2_formFunctional b2_stdF θ)) at hform
  change (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ)
    ⟨_, mfderiv 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel)
      (b4_ellipticScale (Multiplicative.toAdd g⁻¹).val) p.1 p.2⟩ =
    Complex.I ^ (Multiplicative.toAdd g⁻¹).val *
      (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ) p
  rw [congrFun hform _, congrFun hform _]
  change (LinearMap.toContinuousLinearMap (HurwitzPrymAlg2_formFunctional b2_stdF θ))
      (mfderiv 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel)
        (b4_ellipticScale (Multiplicative.toAdd g⁻¹).val) p.1 p.2) = _
  have hd := HurwitzPrymAlg_ellipticScale_mfderiv
    (Multiplicative.toAdd g⁻¹).val p.1 p.2
  change mfderiv 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel)
    (b4_ellipticScale (Multiplicative.toAdd g⁻¹).val) p.1 p.2 =
      Complex.I ^ (Multiplicative.toAdd g⁻¹).val • p.2 at hd
  rw [hd]
  exact map_smul _ _ _

theorem b4_ellipticRot_finrank_forms_aux (a : ℕ) :
    Module.finrank ℂ (b4_HomG (b4_char4 a)
      (fun g ↦ b4_formAct b3_EllipticModel (C := b3_Elliptic) g)
      (b3_HolForm b3_EllipticModel b3_Elliptic)) = if a % 4 = 3 then 1 else 0 := by
  let M := b3_HolForm b3_EllipticModel b3_Elliptic
  let H := b4_HomG (b4_char4 a)
    (fun g ↦ b4_formAct b3_EllipticModel (C := b3_Elliptic) g) M
  have hact := HurwitzPrymAlg2_formAct_apply
  have hdim : Module.finrank ℂ (ℂ →ₗ[ℂ] M) = 1 := by
    rw [Module.finrank_linearMap, b3_elliptic_finrank_holForm]
    simp
  split_ifs with ha
  · have hscalar (g : Multiplicative (ZMod 4)) :
        Complex.I ^ (a * (Multiplicative.toAdd g).val) =
          Complex.I ^ (Multiplicative.toAdd g⁻¹).val := by
      let z := Multiplicative.toAdd g
      change Complex.I ^ (a * z.val) = Complex.I ^ (-z).val
      rw [b4_I_pow_mod, Nat.mul_mod, ha]
      rw [ZMod.neg_val']
      have hz := z.val_lt
      interval_cases z.val <;> norm_num [b4_I_pow_mod, Complex.I_sq]
    let e : H ≃ₗ[ℂ] M :=
      { toFun := fun φ ↦ ⟨φ.1 1, φ.2.1 1⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        invFun := fun θ ↦ ⟨
          { toFun := fun z ↦ z • (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ)
            map_add' := fun x y ↦ by simp [add_smul]
            map_smul' := fun x y ↦ by simp [mul_smul] },
          fun v ↦ M.smul_mem v θ.2,
          fun g v ↦ by
            change (Complex.I ^ (a * (Multiplicative.toAdd g).val) * v) •
                (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ) =
              b4_formAct b3_EllipticModel (C := b3_Elliptic) g
              (v • (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ))
            rw [map_smul, hact]
            rw [smul_smul, hscalar]
            simp [mul_comm] ⟩
        left_inv := fun φ ↦ by
          apply Subtype.ext
          ext v p
          simpa using congrFun (φ.1.map_smul v 1).symm p
        right_inv := fun θ ↦ by
          apply Subtype.ext
          exact one_smul ℂ (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ) }
    change Module.finrank ℂ H = 1
    rw [e.finrank_eq]
    exact b3_elliptic_finrank_holForm
  · have hbot : H = ⊥ := by
      rw [eq_bot_iff]
      intro φ hφ
      apply LinearMap.ext
      intro v
      have heq := hφ.2 (Multiplicative.ofAdd (1 : ZMod 4)) v
      have hv : φ v ∈ M := hφ.1 v
      have hactv := hact (Multiplicative.ofAdd (1 : ZMod 4)) ⟨φ v, hv⟩
      change φ ((b4_char4 a) (Multiplicative.ofAdd (1 : ZMod 4)) v) =
        b4_formAct b3_EllipticModel (C := b3_Elliptic)
          (Multiplicative.ofAdd (1 : ZMod 4)) (φ v) at heq
      rw [hactv] at heq
      change φ ((Complex.I ^ (a * 1)) • v) = Complex.I ^ 3 • φ v at heq
      rw [φ.map_smul] at heq
      simp only [mul_one] at heq
      have hamod : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases hmod : a % 4
      all_goals try contradiction
      all_goals rw [b4_I_pow_mod a, hmod] at heq
      all_goals ext p
      all_goals have hp := congrFun heq p
      all_goals norm_num [Complex.I_sq] at hp ⊢
      all_goals apply Complex.ext
      all_goals
        have hr := congrArg Complex.re hp
        have hi := congrArg Complex.im hp
        simp [Complex.mul_re, Complex.mul_im] at hr hi ⊢
        linarith
    change Module.finrank ℂ H = 0
    rw [hbot]
    simp

theorem b4_ellipticRot_finrank_lattice_aux (a : ℕ) :
    Module.finrank ℂ (b4_HomG (b4_char4 a)
      (fun g ↦ b4_cplxAct b3_EllipticModel (C := b3_Elliptic) g) ⊤) =
      if a % 4 = 1 ∨ a % 4 = 3 then 1 else 0 := by
  let _ : ConnectedSpace b3_Elliptic := b3_elliptic_connectedSpace
  have hE := b3_ellipticModel_finrank
  have hG := b4_ellipticRot_contMDiff_aux
  have := b3_periodLattice_finite (C := b3_Elliptic) hE
  have hconj (g : Multiplicative (ZMod 4)) :
      b4_char4 (3 * a) g = (starRingEnd ℂ) (Complex.I ^ (a * (Multiplicative.toAdd g).val)) •
        LinearMap.id := by
    change (Complex.I ^ (3 * a * (Multiplicative.toAdd g).val)) • LinearMap.id = _
    rw [map_pow, Complex.conj_I, show -Complex.I = Complex.I ^ 3 by
      rw [pow_succ, Complex.I_sq]; ring, ← pow_mul, mul_assoc]
  have h4 : Module.finrank ℂ (b4_HomG (b4_char4 a)
      (fun g ↦ b4_cplxAct b3_EllipticModel (C := b3_Elliptic) g)
      (b2_conjSubmodule _ (b3_periodF b3_EllipticModel b3_Elliptic))) =
      Module.finrank ℂ (b4_HomG (b4_char4 (3 * a))
      (fun g ↦ b4_cplxAct b3_EllipticModel (C := b3_Elliptic) g)
      (b3_periodF b3_EllipticModel b3_Elliptic)) :=
    (HurwitzPrymRex_finrank_homG_char (b4_char4 a)
      (fun g ↦ Complex.I ^ (a * (Multiplicative.toAdd g).val)) (fun g ↦ rfl) _ _).trans
      ((HurwitzPrymRex_finrank_eig_conj
        (fun g ↦ b4_latticeAct b3_EllipticModel (C := b3_Elliptic) g) _ _).trans
        (HurwitzPrymRex_finrank_homG_char _ _ hconj _ _).symm)
  have hsum := congrArg₂ (· + ·)
    ((b4_hodge_eq_holo_aux hE hG (b4_char4 a)).trans (b4_ellipticRot_finrank_forms_aux a))
    (h4.trans ((b4_hodge_eq_holo_aux hE hG (b4_char4 (3 * a))).trans
      (b4_ellipticRot_finrank_forms_aux (3 * a))))
  refine (b4_homG_split_aux hE hG (b4_char4 a)).trans (hsum.trans ?_)
  exact HurwitzPrymRex_char4_count a

end Elliptic

/-! ## The G32 adapter -/

theorem b4_g32_group_realization_aux :
    ∃ (G : Type) (_ : Group G) (_ : Finite G)
      (toMatrix : G → Matrix (Fin 4) (Fin 4) ℂ),
      Function.Injective toMatrix ∧ Set.range toMatrix = (g32h_G : Set _) ∧
      toMatrix 1 = 1 ∧ (∀ g h, toMatrix (g * h) = toMatrix g * toMatrix h) ∧
      Nat.card G = 155520 := by
  exact HurwitzPrymRex_g32_group_realization

#print axioms b4_formRepresentation_invariants_eq_bot
#print axioms b4_formRepresentation_character_sum_eq_zero
#print axioms b4_fixedKernel
#print axioms b4_fixedKernel_finiteSupport
#print axioms b4_lam_rotGen_pow
#print axioms b4_sum_fixed_eq_sum_rotGen_powers
#print axioms b4_holo_multiplicity_fixedKernel
#print axioms b4_fixedKernel_character_sum
#print axioms b4_chevalleyWeil_holo_aux

end HodgeLean.Foundations.Program
