import HodgeLean.Blocks.Weil.WeilTheorem
import HodgeLean.Blocks.HodgeStructure.HodgeClass
import HodgeLean.Blocks.HodgeStructure.ExteriorPower

/-! # Weil classes in rational exterior powers -/

open scoped TensorProduct

noncomputable section

namespace HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

set_option maxHeartbeats 4000000 in
-- Elaborating the alternating-map scalar restriction traverses two scalar towers.
/-- The structure literal involves two scalar towers and needs extra elaboration heartbeats.
Complexify every factor of a rational exterior power. -/
def complexifyWedge (n : ℕ) : ⋀[ℚ]^n V →ₗ[ℚ] ⋀[ℂ]^n (ℂ ⊗[ℚ] V) :=
  exteriorPower.alternatingMapLinearEquiv
    (({ toMultilinearMap :=
          (exteriorPower.ιMulti ℂ n).toMultilinearMap.restrictScalars ℚ
        map_eq_zero_of_eq' :=
          (exteriorPower.ιMulti ℂ n).map_eq_zero_of_eq' } :
        (ℂ ⊗[ℚ] V) [⋀^Fin n]→ₗ[ℚ] ⋀[ℂ]^n (ℂ ⊗[ℚ] V)).compLinearMap
      (complexify V))

@[simp] theorem complexifyWedge_ιMulti (n : ℕ) (v : Fin n → V) :
    complexifyWedge n (exteriorPower.ιMulti ℚ n v) =
      exteriorPower.ιMulti ℂ n (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) := by
  rw [complexifyWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Complexifying an exterior power commutes with the exterior power of a rational linear map. -/
theorem complexifyWedge_exteriorPower_map {W : Type*} [AddCommGroup W] [Module ℚ W]
    (n : ℕ) (f : V →ₗ[ℚ] W) (w : ⋀[ℚ]^n V) :
    complexifyWedge n (exteriorPower.map n f w) =
      exteriorPower.map n (f.baseChange ℂ) (complexifyWedge n w) := by
  let F : ⋀[ℚ]^n V →ₗ[ℚ] ⋀[ℂ]^n (ℂ ⊗[ℚ] W) :=
    (complexifyWedge n).comp (exteriorPower.map n f)
  let G : ⋀[ℚ]^n V →ₗ[ℚ] ⋀[ℂ]^n (ℂ ⊗[ℚ] W) :=
    (exteriorPower.map n (f.baseChange ℂ)).restrictScalars ℚ |>.comp
      (complexifyWedge n)
  change F w = G w
  apply LinearMap.congr_fun
  apply LinearMap.ext_on (exteriorPower.ιMulti_span ℚ n V)
  rintro _ ⟨v, rfl⟩
  simp only [F, G, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    complexifyWedge_ιMulti]
  rw [show exteriorPower.map n f (exteriorPower.ιMulti ℚ n v) =
      exteriorPower.ιMulti ℚ n (f ∘ v) by
    exact DFunLike.congr_fun (exteriorPower.map_comp_ιMulti f) v]
  rw [complexifyWedge_ιMulti]
  rw [show exteriorPower.map n (f.baseChange ℂ)
      (exteriorPower.ιMulti ℂ n (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i)) =
      exteriorPower.ιMulti ℂ n
        (fun i => f.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℚ] v i)) by
    exact DFunLike.congr_fun (exteriorPower.map_comp_ιMulti (f.baseChange ℂ)) _]
  congr 1

/-- A concrete degree-one check: the formula has the advertised value and distinguishes the
wedge of `1` from the wedge of `0`. -/
example :
    complexifyWedge 1 (exteriorPower.ιMulti ℚ 1 (fun _ => (1 : ℚ))) =
        exteriorPower.ιMulti ℂ 1 (fun _ => (1 : ℂ) ⊗ₜ[ℚ] (1 : ℚ)) ∧
      complexifyWedge 1 (exteriorPower.ιMulti ℚ 1 (fun _ => (1 : ℚ))) ≠
        complexifyWedge 1 (exteriorPower.ιMulti ℚ 1 (fun _ => (0 : ℚ))) := by
  constructor
  · exact complexifyWedge_ιMulti 1 _
  · intro h
    have h' := congrArg (exteriorPower.oneEquiv ℂ (ℂ ⊗[ℚ] ℚ)) h
    simpa using h'

namespace WeilAction

variable [Module.Finite ℚ V] {M : QHodgeStructure 1 V} {d : ℚ}
  (A : WeilAction M d)

/-- Every eigenspace of a Hodge-preserving endomorphism splits along an exhaustive pair of
Hodge summands. -/
theorem eigenspace_eq_sup (ω : ℂ)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) :
    Module.End.eigenspace A.Jc ω =
      (Module.End.eigenspace A.Jc ω ⊓ M.H (1, 0)) ⊔
        (Module.End.eigenspace A.Jc ω ⊓ M.H (0, 1)) := by
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ M.H (1, 0) ⊔ M.H (0, 1) := by rw [hH]; trivial
    rcases Submodule.mem_sup.mp hxH with ⟨x10, hx10, x01, hx01, rfl⟩
    have hJ10 : A.Jc x10 ∈ M.H (1, 0) := A.preserves (1, 0) ⟨x10, hx10, rfl⟩
    have hJ01 : A.Jc x01 ∈ M.H (0, 1) := A.preserves (0, 1) ⟨x01, hx01, rfl⟩
    have heig := Module.End.mem_eigenspace_iff.mp hx
    have hz : (A.Jc x10 - ω • x10) + (A.Jc x01 - ω • x01) = 0 := by
      rw [map_add, smul_add] at heig
      calc
        _ = (A.Jc x10 + A.Jc x01) - (ω • x10 + ω • x01) := by abel
        _ = 0 := sub_eq_zero.mpr heig
    have h10mem : A.Jc x10 - ω • x10 ∈ M.H (1, 0) :=
      sub_mem hJ10 ((M.H (1, 0)).smul_mem ω hx10)
    have h01mem : A.Jc x01 - ω • x01 ∈ M.H (0, 1) :=
      sub_mem hJ01 ((M.H (0, 1)).smul_mem ω hx01)
    have hdis : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
      M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
    have hz10 : A.Jc x10 - ω • x10 = 0 := by
      have hother : A.Jc x10 - ω • x10 ∈ M.H (0, 1) := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact (M.H (0, 1)).neg_mem h01mem
      have hb := hdis.le_bot ⟨h10mem, hother⟩
      rw [Submodule.mem_bot] at hb
      exact hb
    have hz01 : A.Jc x01 - ω • x01 = 0 := by
      rw [hz10, zero_add] at hz
      exact hz
    apply Submodule.add_mem
    · apply Submodule.mem_sup_left
      exact ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hz10), hx10⟩
    · apply Submodule.mem_sup_right
      exact ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hz01), hx01⟩
  · exact sup_le inf_le_left inf_le_left

/-- The conjugate Weil eigenspace also splits along the two weight-one Hodge pieces. -/
theorem Vsbar_eq_sup (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) :
    A.Vsbar = (A.Vsbar ⊓ M.H (1, 0)) ⊔ (A.Vsbar ⊓ M.H (0, 1)) := by
  exact A.eigenspace_eq_sup (-omegaC d) hH

/-- Conjugation preserves the complex dimension of a subspace. -/
theorem finrank_map_sigmaQ (P : Submodule ℂ (ℂ ⊗[ℚ] V)) :
    Module.finrank ℂ (P.map (sigmaQ V)) = Module.finrank ℂ P := by
  let e := Submodule.equivMapOfInjective (sigmaQ V)
    (fun x y h => by simpa only [sigmaQ_involutive V] using congrArg (sigmaQ V) h) P
  unfold Module.finrank
  congr 1
  symm
  exact rank_eq_of_equiv_equiv Complex.conjAe.toRingEquiv e.toAddEquiv
    Complex.conjAe.toRingEquiv.bijective (fun c x => LinearEquiv.map_smulₛₗ e c x)

/-- Conjugation exchanges the two intersections of the Weil eigenspaces with Hodge pieces. -/
theorem map_inf_Vs_H10_sigmaQ :
    (A.Vs ⊓ M.H (1, 0)).map (sigmaQ V) = A.Vsbar ⊓ M.H (0, 1) := by
  rw [Submodule.map_inf (sigmaQ V)
    (fun x y h => by simpa only [sigmaQ_involutive V] using congrArg (sigmaQ V) h)]
  rw [A.map_Vs_sigmaQ, M.conj_symm]

/-- The opposite intersection is likewise exchanged by conjugation. -/
theorem map_inf_Vs_H01_sigmaQ :
    (A.Vs ⊓ M.H (0, 1)).map (sigmaQ V) = A.Vsbar ⊓ M.H (1, 0) := by
  rw [Submodule.map_inf (sigmaQ V)
    (fun x y h => by simpa only [sigmaQ_involutive V] using congrArg (sigmaQ V) h)]
  rw [A.map_Vs_sigmaQ, M.conj_symm]

/-- Under the Weil balance condition, the two Hodge intersections of the conjugate eigenspace
have equal dimension.  Conjugation swaps both the eigenspace and the Hodge labels. -/
theorem finrank_inf_H10_eq_inf_H01
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) :
    Module.finrank ℂ ↥(A.Vsbar ⊓ M.H (1, 0)) =
      Module.finrank ℂ ↥(A.Vsbar ⊓ M.H (0, 1)) := by
  calc
    Module.finrank ℂ ↥(A.Vsbar ⊓ M.H (1, 0)) =
        Module.finrank ℂ ↥((A.Vs ⊓ M.H (0, 1)).map (sigmaQ V)) := by
          rw [A.map_inf_Vs_H01_sigmaQ]
    _ = Module.finrank ℂ ↥(A.Vs ⊓ M.H (0, 1)) := finrank_map_sigmaQ _
    _ = Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) :=
      A.finrank_inf_H01_eq_inf_H10 hH hWeil
    _ = Module.finrank ℂ ↥((A.Vs ⊓ M.H (1, 0)).map (sigmaQ V)) :=
      (finrank_map_sigmaQ _).symm
    _ = Module.finrank ℂ ↥(A.Vsbar ⊓ M.H (0, 1)) := by
      rw [A.map_inf_Vs_H10_sigmaQ]

/-- The top exterior power of the conjugate Weil eigenspace has wedge type `(k,k)`, with the
same `k` used for the distinguished eigenspace. -/
theorem top_wedge_Vsbar_mem_wedgeType
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) :
    LinearMap.range (exteriorPower.map
        (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
          Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
        (Submodule.subtype A.Vsbar)) ≤
      wedgeType (A.Vsbar ⊓ M.H (1, 0)) (A.Vsbar ⊓ M.H (0, 1))
        (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
        (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  have hk10 : Module.finrank ℂ ↥(A.Vsbar ⊓ M.H (1, 0)) = k := by
    calc
      Module.finrank ℂ ↥(A.Vsbar ⊓ M.H (1, 0)) =
          Module.finrank ℂ ↥((A.Vs ⊓ M.H (0, 1)).map (sigmaQ V)) := by
            rw [A.map_inf_Vs_H01_sigmaQ]
      _ = Module.finrank ℂ ↥(A.Vs ⊓ M.H (0, 1)) := finrank_map_sigmaQ _
      _ = k := A.finrank_inf_H01_eq_inf_H10 hH hWeil
  have hdis : (A.Vsbar ⊓ M.H (1, 0)) ⊓ (A.Vsbar ⊓ M.H (0, 1)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hd : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
      M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
    exact hd.le_bot ⟨hx.1.2, hx.2.2⟩
  calc
    LinearMap.range (exteriorPower.map (k + k) A.Vsbar.subtype) =
        LinearMap.range (exteriorPower.map (k + k)
          ((A.Vsbar ⊓ M.H (1, 0)) ⊔ (A.Vsbar ⊓ M.H (0, 1))).subtype) :=
      exteriorPower_map_subtype_range_eq_of_eq _ _ _ (A.Vsbar_eq_sup hH)
    _ ≤ wedgeType (A.Vsbar ⊓ M.H (1, 0)) (A.Vsbar ⊓ M.H (0, 1)) k k := by
      rw [← hk10]
      exact topExteriorPower_sup_le_wedgeType _ _ hdis
        (A.finrank_inf_H10_eq_inf_H01 hH hWeil).symm

/-- The rational Weil-class space, following van Geemen, §4.2: the two conjugate
one-dimensional spaces `∧^{2n} Z_κ` and `∧^{2n} Z_κ̄` define `W_K`, with
`W_K ⊗_ℚ K = ∧^{2n} Z_κ ⊕ ∧^{2n} Z_κ̄`.

Precisely, this definition is the `ℚ`-subspace of rational wedges whose image under
`complexifyWedge` lies in the span of the two complex top exterior lines.  It is expressed as a
`comap`; no stronger descent equality identifying the scalar extension of this subspace with
that span is proved here.  The hypotheses make the name meaningful for the downstream
Weil-type theorem, although the two top-wedge ranges themselves are defined unconditionally. -/
def weilClasses (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) :
    Submodule ℚ
      (⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) :=
  Submodule.comap (complexifyWedge _)
    ((LinearMap.range (exteriorPower.map _ A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map _ A.Vsbar.subtype)).restrictScalars ℚ)

/-- Every rational Weil class has complex `(k,k)` wedge type after applying
`complexifyWedge`, where `k` is the dimension of the `(1,0)` part of the distinguished Weil
eigenspace.

Here “Hodge class” is disclosed directly as `(k,k)`-type membership, rather than as the
layer-1 `IsHodgeClass` predicate.  **UPDATED (hodge-LEAN15, 2026-09-24):** this project now has
`QHodgeStructure.exteriorPower` (hodge-LEAN13) and `IsHodgeClass` reaches a genuinely proved,
explicitly named sub-family below — `isHodgeClass_exteriorPower_mixed` and
`isHodgeClass_exteriorPower_of_mem_mixedWedgeSpan` — but NOT `weilClasses` itself: no theorem
connects an arbitrary element of `weilClasses` (the `comap`-defined submodule above) to that
sub-family or to `IsHodgeClass`, so this direct type-membership statement remains the only fact
proved for a general element of `weilClasses`.  This is the classical linear-algebra statement
for an abstract weight-one rational Hodge structure with a Weil-type action.  It constructs no
geometric object and is not a universal statement of progress toward the Hodge conjecture. -/
theorem weilClasses_mem_wedgeType
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType)
    {w : ⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V}
    (hw : w ∈ A.weilClasses hH hWeil) :
    complexifyWedge _ w ∈
      wedgeType (A.Vs ⊓ M.H (1, 0)) (A.Vs ⊓ M.H (0, 1))
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) ⊔
        wedgeType (A.Vsbar ⊓ M.H (1, 0)) (A.Vsbar ⊓ M.H (0, 1))
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) := by
  apply (sup_le_sup (A.top_wedge_Vs_mem_wedgeType hH hWeil)
    (A.top_wedge_Vsbar_mem_wedgeType hH hWeil))
  exact hw

/-! ## Mixed decomposable wedges as Hodge classes -/

/-- Transport a Hodge structure along an equality of weights.  This local version is needed
because the corresponding implementation detail in `ExteriorPower.lean` is private. -/
def weightCast {n m : ℤ} (h : n = m) (N : QHodgeStructure n V) :
    QHodgeStructure m V :=
  h ▸ N

@[simp] theorem weightCast_H {n m : ℤ} (h : n = m) (N : QHodgeStructure n V) :
    (weightCast (V := V) h N).H = N.H := by
  subst m
  rfl

/-- A decomposable wedge with `k` factors of type `(1,0)` followed by `k` factors of type
`(0,1)` is a Hodge class in the middle piece of the rational exterior power. -/
theorem isHodgeClass_exteriorPower_mixed (M : QHodgeStructure 1 V) (k : ℕ)
    (v : Fin (k + k) → V)
    (hv1 : ∀ i : Fin k, complexify V (v (Fin.castAdd k i)) ∈ M.H (1, 0))
    (hv2 : ∀ i : Fin k, complexify V (v (Fin.natAdd k i)) ∈ M.H (0, 1)) :
    IsHodgeClass (p := (k : ℤ))
      (weightCast (V := ⋀[ℚ]^(k + k) V) (by omega)
        (M.exteriorPower (V := V) (k + k)))
      (exteriorPower.ιMulti ℚ (k + k) v) := by
  classical
  let K := LinearMap.ker (tensorPowerAltC V (k + k))
  let e := QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC (V := V) (k + k)
  let d : Fin (k + k) → ℤ × ℤ :=
    Fin.append (fun _ : Fin k => ((1 : ℤ), (0 : ℤ)))
      (fun _ : Fin k => ((0 : ℤ), (1 : ℤ)))
  have hd : d ∈ (totalBidegree (k + k)) ⁻¹' {((k : ℤ), (k : ℤ))} := by
    change totalBidegree (k + k) d = ((k : ℤ), (k : ℤ))
    apply Prod.ext <;>
      simp [totalBidegree, d, Fin.sum_univ_add, Fin.append, Fin.addCases, Fin.cast]
  have hvi : ∀ i, complexify V (v i) ∈ M.H (d i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [d, Fin.append, Fin.addCases, Fin.cast] using hv1 j
    · intro j
      simpa [d, Fin.append, Fin.addCases, Fin.cast] using hv2 j
  have hfine :
      PiTensorProduct.tprod ℂ (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) ∈
        M.tensorFinePiece (V := V) (k + k) d := by
    refine ⟨PiTensorProduct.tprod ℂ
      (fun i => (⟨(1 : ℂ) ⊗ₜ[ℚ] v i, hvi i⟩ : M.H (d i))), ?_⟩
    rw [PiTensorProduct.map_tprod]
    rfl
  have hsum :
      PiTensorProduct.tprod ℂ (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i) ∈
        ⨆ d' ∈ (totalBidegree (k + k)) ⁻¹' {((k : ℤ), (k : ℤ))},
          M.tensorFinePiece (V := V) (k + k) d' :=
    Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd hfine)
  have hflat :
      (1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v ∈
        (M.tensorPowerFlat (V := V) (k + k)).H ((k : ℤ), (k : ℤ)) := by
    change (1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v ∈
      (⨆ d' ∈ (totalBidegree (k + k)) ⁻¹' {((k : ℤ), (k : ℤ))},
        M.tensorFinePiece (V := V) (k + k) d').map
          (tensorPowerBaseChange V (k + k)).symm.toLinearMap
    rw [Submodule.mem_map_equiv]
    simp only [LinearEquiv.symm_symm]
    rw [tensorPowerBaseChange_tmul_tprod]
    simpa using hsum
  have hquot : K.mkQ ((1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v) ∈
      ((M.tensorPowerFlat (V := V) (k + k)).H ((k : ℤ), (k : ℤ))).map K.mkQ :=
    Submodule.mem_map_of_mem hflat
  have himage :
      e (K.mkQ ((1 : ℂ) ⊗ₜ[ℚ] PiTensorProduct.tprod ℚ v)) =
        (1 : ℂ) ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ (k + k) v := by
    dsimp [e, K]
    rw [QHodgeStructure.tensorPowerAltC_quot_equiv_exteriorPowerC_mk]
    rw [LinearMap.baseChange_tmul]
    rw [tensorPowerToExteriorPower_tprod]
  have htarget :
      complexify (⋀[ℚ]^(k + k) V) (exteriorPower.ιMulti ℚ (k + k) v) ∈
        M.exteriorPowerH (V := V) (k + k) ((k : ℤ), (k : ℤ)) := by
    rw [complexify_apply, QHodgeStructure.exteriorPowerH]
    rw [← himage]
    exact Submodule.mem_map_of_mem hquot
  change complexify (⋀[ℚ]^(k + k) V) (exteriorPower.ιMulti ℚ (k + k) v) ∈
    (weightCast (V := ⋀[ℚ]^(k + k) V) _
      (M.exteriorPower (V := V) (k + k))).H ((k : ℤ), (k : ℤ))
  rw [weightCast_H]
  exact htarget

/-- The rational span of decomposable mixed wedges.  This is the precise generator hypothesis
needed to extend `isHodgeClass_exteriorPower_mixed` by linearity.  **No theorem in this file
shows `A.weilClasses hH hWeil ≤ mixedWedgeSpan M k`** (or any other relation between the two) —
that inclusion is exactly the open non-vacuity/descent gap (see `weilClasses_mem_wedgeType`'s
docstring), so `isHodgeClass_exteriorPower_of_mem_mixedWedgeSpan` below does not yet apply to a
general element of `weilClasses`. -/
def mixedWedgeSpan (M : QHodgeStructure 1 V) (k : ℕ) :
    Submodule ℚ (⋀[ℚ]^(k + k) V) :=
  Submodule.span ℚ {w | ∃ v : Fin (k + k) → V,
    (∀ i : Fin k, complexify V (v (Fin.castAdd k i)) ∈ M.H (1, 0)) ∧
    (∀ i : Fin k, complexify V (v (Fin.natAdd k i)) ∈ M.H (0, 1)) ∧
    w = exteriorPower.ιMulti ℚ (k + k) v}

/-- Every rational linear combination of decomposable mixed wedges is a Hodge class. -/
theorem isHodgeClass_exteriorPower_of_mem_mixedWedgeSpan (M : QHodgeStructure 1 V) (k : ℕ)
    {w : ⋀[ℚ]^(k + k) V} (hw : w ∈ mixedWedgeSpan M k) :
    IsHodgeClass (p := (k : ℤ))
      (weightCast (V := ⋀[ℚ]^(k + k) V) (by omega)
        (M.exteriorPower (V := V) (k + k))) w := by
  rw [mixedWedgeSpan] at hw
  induction hw using Submodule.span_induction with
  | mem _ h =>
    rcases h with ⟨v, hv1, hv2, rfl⟩
    exact isHodgeClass_exteriorPower_mixed M k v hv1 hv2
  | zero => simp [IsHodgeClass]
  | add x y _ _ hx hy =>
    simp only [IsHodgeClass, map_add] at hx hy ⊢
    exact Submodule.add_mem _ hx hy
  | smul q x _ hx =>
    simp only [IsHodgeClass, map_smul] at hx ⊢
    exact Submodule.smul_mem _ (q : ℂ) hx

end WeilAction

#print axioms complexifyWedge
#print axioms complexifyWedge_ιMulti
#print axioms complexifyWedge_exteriorPower_map
#print axioms WeilAction.eigenspace_eq_sup
#print axioms WeilAction.Vsbar_eq_sup
#print axioms WeilAction.finrank_map_sigmaQ
#print axioms WeilAction.map_inf_Vs_H10_sigmaQ
#print axioms WeilAction.map_inf_Vs_H01_sigmaQ
#print axioms WeilAction.finrank_inf_H10_eq_inf_H01
#print axioms WeilAction.top_wedge_Vsbar_mem_wedgeType
#print axioms WeilAction.weilClasses
#print axioms WeilAction.weilClasses_mem_wedgeType
#print axioms WeilAction.weightCast
#print axioms WeilAction.weightCast_H
#print axioms WeilAction.isHodgeClass_exteriorPower_mixed
#print axioms WeilAction.mixedWedgeSpan
#print axioms WeilAction.isHodgeClass_exteriorPower_of_mem_mixedWedgeSpan

end HodgeBlocks
