import HodgeLean.Foundations.Program.CoverDictionaryDefs

/-! # The cover dictionary, stage 3: the regular-locus covering (definitions)

The regular locus of a fibre as a sub-`G`-set, the base `ℂ` minus the poles, the `s`-projection
of the regular locus onto the base, and the property that the transport of a Fuchsian system on
the base is conjugate, by one operator, to the column monodromy of that projection along every
loop at one base point. No statement is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- **The regular locus as a sub-`G`-set** of the fibre over `t`: the carrier is `b65g_good`,
which is invariant under the deck group because the projection is (`D.hgal`).
Source: G32 v0.16, §5.3 (the complement of the poles) and Definition 3.5 (Galois cover);
`b65g_good`, `b4_IsGaloisCover`. -/
def b65g_goodSub {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) :
    SubMulAction b4b_Group (b65z_fibre c D.C t) where
  carrier := b65g_good D t a b poles
  smul_mem' h x hx := by
    obtain ⟨z, hz, h1, h2⟩ := hx
    exact ⟨z, ((D.hgal t).1 h x).trans hz, h1, h2⟩

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) (x : b65z_fibre c D.C t) :
    x ∈ b65g_goodSub D t a b poles ↔ x ∈ b65g_good D t a b poles := Iff.rfl

/-- **The base**: the `s`-plane minus the poles.
Source: G32 v0.16, §5.3 (the Fuchsian system on `ℙ¹ − P`); `b65p_coefficient`. -/
def b65g_U (poles : Fin 4 ⊕ Fin 12 → ℂ) : Set ℂ := (Set.range poles)ᶜ

example (poles : Fin 4 ⊕ Fin 12 → ℂ) (q : Fin 4 ⊕ Fin 12) : poles q ∉ b65g_U poles :=
  fun h ↦ h ⟨q, rfl⟩

/-- **The `s`-projection of the regular locus** onto the base: `x ↦ s(x)`. Its values avoid the
poles by the definition of `b65g_good`.
Source: G32 v0.16, §5.5 (the covers `C_θ` over `ℙ¹_s`); `b65g_sFun`. -/
def b65g_sProj {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) :
    b65g_goodSub D t a b poles → b65g_U poles :=
  fun x ↦ ⟨b65g_sFun D t a b x.val, by
    obtain ⟨z, hz, -, hpole⟩ := x.property
    simpa only [b65g_sFun, b65g_U, Set.mem_compl_iff, hz] using hpole⟩

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (x : b65g_goodSub D t a b poles) :
    (b65g_sProj D t a b poles x : ℂ) = b65g_sFun D t a b x.val := rfl

/-- The deck action on the regular locus is the action on the fibre. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ) (h : b4b_Group)
    (x : b65g_goodSub D t a b poles) :
    ((h • x : b65g_goodSub D t a b poles) : b65z_fibre c D.C t) = h • (x : b65z_fibre c D.C t) :=
  rfl

/-- **All-loop transfer at one base point.** For a quotient-covering proof `hπ` of the
`s`-projection, there are a base point `x`, a point `u` of the regular locus over it and an
invertible operator `C` such that, for every loop `η` at `x` in the base, the transport of the
Fuchsian system with poles `poles` and residues `R` along `η` is `C` times the column monodromy
of `η` (`b65s_column` of the deck monodromy at `u`) times `C⁻¹`. This is the shape of the
identification `hT` of `b65g_cover_solutions`, on the actual fibre and in the `s`-coordinate.
Source: G32 v0.16, §5.5 (The direction: "the system at `θ` is the `ρ`-local system of the cover
`C_θ`"); Mathlib `IsQuotientCoveringMap.fundamentalGroupToMulOpposite`; `b65f_transport`,
`b65s_column`. -/
def b65g_loopTransfer {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (R : Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (hπ : IsQuotientCoveringMap (b65g_sProj D t a b poles) b4b_Group) : Prop :=
  ∃ (x : b65g_U poles) (u : b65g_sProj D t a b poles ⁻¹' {x})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ), ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) (b65p_coefficient (Fin 4 → ℂ) poles R)
          (fun v ↦ (η.extend v).val) =
        C.val * (b65s_column (hπ.fundamentalGroupToMulOpposite u)
          (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (R : Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (hπ : IsQuotientCoveringMap (b65g_sProj D t a b poles) b4b_Group) :
    b65g_loopTransfer D t a b poles R hπ ↔
      ∃ (x : b65g_U poles) (u : b65g_sProj D t a b poles ⁻¹' {x})
        (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ), ∀ η : Path x x,
          b65f_transport (Fin 4 → ℂ) (b65p_coefficient (Fin 4 → ℂ) poles R)
              (fun v ↦ (η.extend v).val) =
            C.val * (b65s_column (hπ.fundamentalGroupToMulOpposite u)
              (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val := Iff.rfl

end HodgeLean.Foundations.Program
