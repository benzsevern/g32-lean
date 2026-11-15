import HodgeLean.Foundations.MatrixAlgGroupLieBasic

/-! # The Zariski identity component of a matrix algebraic group

The Zariski closed sets of `GL_n(k)` are the zero sets of polynomials in the matrix entries, and
left translations are Zariski continuous. Hence the connected component `G°` of `1` in a matrix
algebraic group `G` is a closed subgroup, so it is itself a matrix algebraic group. Since
`GL_n(k)` is a Noetherian space, `G` is a finite union of closed irreducible sets; those missing
`G°` form a closed set `W` with `1 ∉ W` containing `G \ G°`. Multiplying by a polynomial that is
nonzero at `1` and vanishes on `W` shows that `G` and `G°` have the same tangent space at `1`.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial Matrix HodgeLean.Foundations.Program TopologicalSpace

variable {k : Type*} [Field k] {n : ℕ}

set_option warn.classDefReducibility false in
attribute [local instance] g1_zariski

/-- The common zero set in `GL_n(k)` of a set of polynomials in the matrix entries.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 (the closed set `V(S)`). -/
def g1_zeroSet (s : Set (MvPolynomial (Fin n × Fin n) k)) :
    Set (Matrix.GeneralLinearGroup (Fin n) k) :=
  {g | ∀ f ∈ s, eval (g1_coords g) f = 0}

/-- The Zariski closed subsets of `GL_n(k)` are exactly the zero sets of sets of polynomials.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 and §1.6. -/
theorem g1_isClosed_iff (Z : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    IsClosed Z ↔ ∃ s : Set (MvPolynomial (Fin n × Fin n) k), Z = g1_zeroSet s := by
  have hpre : ∀ s : Set (MvPolynomial (Fin n × Fin n) k),
      (fun g : Matrix.GeneralLinearGroup (Fin n) k ↦ (MvPolynomial.pointToPoint (k := k)
        (g1_coords g) : PrimeSpectrum (MvPolynomial (Fin n × Fin n) k))) ⁻¹'
          PrimeSpectrum.zeroLocus s = g1_zeroSet s := by
    intro s
    ext g
    simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, g1_zeroSet, Set.mem_ofPred_eq]
    exact ⟨fun h f hf ↦ (g1_mem_pointToPoint_iff g f).mp (h hf),
      fun h f hf ↦ (g1_mem_pointToPoint_iff g f).mpr (h f hf)⟩
  refine isClosed_induced_iff.trans ⟨?_, ?_⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).mp ht
    exact ⟨s, hpre s⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, PrimeSpectrum.isClosed_zeroLocus s, hpre s⟩

/-- Zero sets are Zariski closed.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1_isClosed_zeroSet (s : Set (MvPolynomial (Fin n × Fin n) k)) :
    IsClosed (g1_zeroSet s) :=
  (g1_isClosed_iff _).mpr ⟨s, rfl⟩

/-- The point set of a matrix algebraic group is Zariski closed.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.1. -/
theorem g1_isClosed_carrier (G : MatrixAlgGroup k n) :
    IsClosed (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) := by
  have : (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) = g1_zeroSet G.equations := by
    ext g
    exact G.equations_iff g
  rw [this]
  exact g1_isClosed_zeroSet _

/-- `GL_n(k)` with its Zariski topology is a Noetherian space.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.3 and AG.1.5. -/
theorem g1_noetherianSpace : NoetherianSpace (Matrix.GeneralLinearGroup (Fin n) k) :=
  (Topology.IsInducing.induced _).noetherianSpace

/-- Left translation by an element of the identity component maps it into itself.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2. -/
theorem g1_inv_mul_mem_identityComponent (G : MatrixAlgGroup k n)
    {a b : Matrix.GeneralLinearGroup (Fin n) k} (ha : a ∈ g1_identityComponent G)
    (hb : b ∈ g1_identityComponent G) : a⁻¹ * b ∈ g1_identityComponent G := by
  have haG : a ∈ G.carrier := connectedComponentIn_subset _ _ ha
  have himG : (fun g ↦ a⁻¹ * g) '' (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) =
      G.carrier := by
    rw [Set.image_mul_left']
    ext g
    exact G.carrier.mul_mem_cancel_left haG
  have hsub := (g1_continuous_mul_left a⁻¹).continuousOn.image_connectedComponentIn_subset
    (s := (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k))) haG
  rw [himG, inv_mul_cancel] at hsub
  have hcomp : g1_identityComponent G =
      connectedComponentIn (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) a :=
    connectedComponentIn_eq ha
  rw [hcomp] at hb
  exact hsub ⟨b, hb, rfl⟩

/-- The identity component as a subgroup of `GL_n(k)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2. -/
def g1_identityComponentSubgroup (G : MatrixAlgGroup k n) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) k) where
  carrier := g1_identityComponent G
  one_mem' := mem_connectedComponentIn G.carrier.one_mem
  mul_mem' {a b} ha hb := by
    have hinv : a⁻¹ ∈ g1_identityComponent G := by
      simpa using g1_inv_mul_mem_identityComponent G ha
        (mem_connectedComponentIn G.carrier.one_mem)
    simpa using g1_inv_mul_mem_identityComponent G hinv hb
  inv_mem' {a} ha := by
    simpa using g1_inv_mul_mem_identityComponent G ha (mem_connectedComponentIn G.carrier.one_mem)

/-- The identity component is Zariski closed.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2. -/
theorem g1_isClosed_identityComponent (G : MatrixAlgGroup k n) :
    IsClosed (g1_identityComponent G) := by
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin n) k) ∈ g1_identityComponent G :=
    mem_connectedComponentIn G.carrier.one_mem
  have hcl : closure (g1_identityComponent G) ⊆ G.carrier :=
    closure_minimal (connectedComponentIn_subset _ _) (g1_isClosed_carrier G)
  refine closure_subset_iff_isClosed.mp ?_
  exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
    (subset_closure h1) hcl

/-- The identity component is the point set of a matrix algebraic group.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2; Humphreys, *Linear Algebraic Groups*,
§7.3. -/
theorem g1_exists_identityComponent_of_closed (G : MatrixAlgGroup k n) :
    ∃ I : MatrixAlgGroup k n, (I.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) =
      g1_identityComponent G := by
  obtain ⟨s, hs⟩ := (g1_isClosed_iff _).mp (g1_isClosed_identityComponent G)
  refine ⟨g1_ofEquations s (g1_identityComponentSubgroup G) fun g ↦ ?_, rfl⟩
  change g ∈ g1_identityComponent G ↔ _
  rw [hs]
  rfl

/-- The part of `G` outside its identity component lies in a Zariski closed set missing `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2 (`G°` is open in `G`). -/
theorem g1_exists_isClosed_compl_identityComponent (G : MatrixAlgGroup k n) :
    ∃ W : Set (Matrix.GeneralLinearGroup (Fin n) k), IsClosed W ∧ 1 ∉ W ∧
      ∀ g ∈ G.carrier, g ∉ g1_identityComponent G → g ∈ W := by
  have := g1_noetherianSpace (k := k) (n := n)
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (g1_isClosed_carrier G)
  refine ⟨⋃ t ∈ {t ∈ S | Disjoint t (g1_identityComponent G)}, t,
    (hSf.subset (Set.sep_subset _ _)).isClosed_biUnion fun t ht ↦ hSc t ht.1, ?_, ?_⟩
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
    rintro t ⟨_, hdis⟩ h1t
    exact Set.disjoint_left.mp hdis h1t (mem_connectedComponentIn G.carrier.one_mem)
  · intro g hg hgC
    have hgS : g ∈ ⋃₀ S := hSU ▸ hg
    obtain ⟨t, htS, hgt⟩ := hgS
    refine Set.mem_biUnion ⟨htS, Set.disjoint_left.mpr fun x hxt hxC ↦ hgC ?_⟩ hgt
    have htG : t ⊆ G.carrier := hSU ▸ Set.subset_sUnion_of_mem htS
    have hcomp : g1_identityComponent G =
        connectedComponentIn (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) x :=
      connectedComponentIn_eq hxC
    rw [hcomp]
    exact (hSi t htS).2.isPreconnected.subset_connectedComponentIn hxt htG hgt

/-- Leibniz rule at a zero: if `f(1) = 0` then `d(f h)_1 = h(1) d f_1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1_differential_mul_of_eval_eq_zero (f h : MvPolynomial (Fin n × Fin n) k)
    (hf : eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) f = 0)
    (X : Matrix (Fin n) (Fin n) k) :
    g1_differential (f * h) X =
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) h * g1_differential f X := by
  rw [g1_differential_apply, g1_differential_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hf]
  ring

/-- **Locality of the tangent space.** The identity component and the group have the same
tangent space at `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2 (`G°` is open in `G`) and §3.5. -/
theorem g1_lieOfSet_identityComponent (G : MatrixAlgGroup k n) :
    g1_lieOfSet (g1_identityComponent G) = g1_lieAlgebra G := by
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin n) k) ∈ g1_identityComponent G :=
    mem_connectedComponentIn G.carrier.one_mem
  have hsub : g1_identityComponent G ⊆ G.carrier := connectedComponentIn_subset _ _
  refine le_antisymm ?_ ?_
  · -- a smaller set has a larger vanishing ideal
    refine le_iInf₂ fun f hf ↦ iInf₂_le f ?_
    exact vanishingIdeal_anti_mono (Set.image_mono hsub) hf
  · obtain ⟨W, hWc, h1W, hW⟩ := g1_exists_isClosed_compl_identityComponent G
    obtain ⟨s, rfl⟩ := (g1_isClosed_iff W).mp hWc
    obtain ⟨h, hs, hh1⟩ : ∃ h ∈ s, eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))
        h ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h1W hcon
    refine le_iInf₂ fun f hf ↦ ?_
    intro X hX
    have hf' : ∀ g ∈ g1_identityComponent G, eval (g1_coords g) f = 0 :=
      fun g hg ↦ (mem_vanishingIdeal_iff.mp hf) _ ⟨g, hg, rfl⟩
    have hfh : f * h ∈ g1_vanishingIdeal G := by
      refine mem_vanishingIdeal_iff.mpr ?_
      rintro _ ⟨g, hg, rfl⟩
      change eval (g1_coords g) (f * h) = 0
      rw [map_mul]
      by_cases hgC : g ∈ g1_identityComponent G
      · rw [hf' g hgC, zero_mul]
      · rw [hW g hg hgC h hs, mul_zero]
    have hX' : g1_differential (f * h) X = 0 := by
      have := (Submodule.mem_iInf _).mp hX (f * h)
      exact (Submodule.mem_iInf _).mp this hfh
    rw [g1_differential_mul_of_eval_eq_zero f h (hf' 1 h1)] at hX'
    exact (mul_eq_zero.mp hX').resolve_left hh1

end HodgeLean.Foundations
