import HodgeLean.Foundations.Program.G32SelectedRealizationSurjectiveFibres

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_orbit_inversion_equiv {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (x : X) (g : G)
    (hg : MulAction.stabilizer G x = Subgroup.zpowers g) :
    ∃ e : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) ≃
        Quotient (MulAction.orbitRel H (MulAction.orbit G x)),
      ∀ a : G, e (Quotient.mk'' (a : G ⧸ H)) = Quotient.mk''
        (⟨a⁻¹ • x, MulAction.mem_orbit_iff.mpr ⟨a⁻¹, rfl⟩⟩ : MulAction.orbit G x) := by
  classical
  let Y := MulAction.orbit G x
  let Q₁ := Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))
  let Q₂ := Quotient (MulAction.orbitRel H Y)
  let y : G → Y := fun a ↦ ⟨a⁻¹ • x, MulAction.mem_orbit_iff.mpr ⟨a⁻¹, rfl⟩⟩
  let p : G → Q₁ := fun a ↦ Quotient.mk'' (a : G ⧸ H)
  let q : G → Q₂ := fun a ↦ Quotient.mk'' (y a)
  have hp : Function.Surjective p := by
    intro z
    refine ⟨z.out.out, ?_⟩
    change (Quotient.mk'' (Quotient.mk'' z.out.out : G ⧸ H) : Q₁) = z
    rw [Quotient.out_eq', Quotient.out_eq']
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp z.out.property
    refine ⟨b⁻¹, ?_⟩
    have he : y b⁻¹ = z.out := by
      apply Subtype.ext
      change (b⁻¹)⁻¹ • x = z.out.val
      rw [inv_inv]
      exact hb
    change (Quotient.mk'' (y b⁻¹) : Q₂) = z
    rw [he, Quotient.out_eq']
  have hker (a b : G) : p a = p b ↔ q a = q b := by
    change (Quotient.mk'' (a : G ⧸ H) : Q₁) = Quotient.mk'' (b : G ⧸ H) ↔
      (Quotient.mk'' (y a) : Q₂) = Quotient.mk'' (y b)
    simp only [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨z, hz⟩
      have hm : a⁻¹ * (z : G) * b ∈ H := by
        have hh : (((z : G) * b : G) : G ⧸ H) = (a : G ⧸ H) := hz
        simpa only [mul_assoc] using QuotientGroup.eq.mp hh.symm
      let h : H := ⟨a⁻¹ * (z : G) * b, hm⟩
      refine ⟨h, ?_⟩
      apply Subtype.ext
      change (a⁻¹ * (z : G) * b) • (b⁻¹ • x) = a⁻¹ • x
      have hf : (z : G) • x = x := by
        exact Eq.mpr (congrArg (fun K : Subgroup G ↦ (z : G) ∈ K) hg) z.property
      simp only [mul_smul, smul_inv_smul, hf]
    · rintro ⟨h, hh⟩
      have he : (h : G) • (b⁻¹ • x) = a⁻¹ • x := congrArg Subtype.val hh
      let z : G := a * (h : G) * b⁻¹
      have hz : z ∈ Subgroup.zpowers g := by
        rw [← hg]
        change z • x = x
        have hc := congrArg (fun v : X ↦ a • v) he
        simpa only [z, mul_smul, smul_inv_smul] using hc
      refine ⟨⟨z, hz⟩, ?_⟩
      change ((z * b : G) : G ⧸ H) = (a : G ⧸ H)
      apply Eq.symm
      apply QuotientGroup.eq.mpr
      have hk : a⁻¹ * (z * b) = (h : G) := by dsimp [z]; group
      rw [hk]
      exact h.property
  refine ⟨g32y_equiv_of_surjective_fibres p q hp hq hker, ?_⟩
  intro a
  exact g32y_equiv_of_surjective_fibres_apply p q hp hq hker a

end HodgeLean.Foundations.Program
