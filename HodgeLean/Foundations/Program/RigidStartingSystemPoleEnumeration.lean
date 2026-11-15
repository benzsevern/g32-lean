import HodgeLean.Foundations.Program.RigidStartingSystemSourceCharts
import HodgeLean.Foundations.Program.RiemannRochProofs

noncomputable section
open Set
namespace HodgeLean.Foundations.Program

def b65r_sourcePoles : Set ℂ := {0,5,-7}

theorem b65r_sourcePoles_finite : b65r_sourcePoles.Finite := by
  simp [b65r_sourcePoles]

theorem b65r_sourcePoles_domain : {z : ℂ | z ∉ b65r_sourcePoles} = b65r_sourceDomain := by
  ext z
  simp [b65r_sourcePoles,b65r_sourceDomain]

def b65r_sourcePole (i : Fin 3) : b65r_sourcePoles :=
  ⟨b65r_centres i,by fin_cases i <;> norm_num [b65r_centres,b65r_sourcePoles]⟩

theorem b65r_sourcePole_bijective : Function.Bijective b65r_sourcePole := by
  constructor
  · intro i j hij
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> norm_num [b65r_sourcePole,b65r_centres] at h
    all_goals rfl
  · rintro ⟨z,hz⟩
    simp only [b65r_sourcePoles,mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with h | h | h
    · exact ⟨2,Subtype.ext h.symm⟩
    · exact ⟨0,Subtype.ext h.symm⟩
    · exact ⟨1,Subtype.ext h.symm⟩

def b65r_sourcePoleEquiv : Fin 3 ≃ b65r_sourcePoles :=
  Equiv.ofBijective b65r_sourcePole b65r_sourcePole_bijective

theorem b65r_sourcePoles_re_inj : Set.InjOn Complex.re b65r_sourcePoles := by
  intro z hz w hw h
  simp only [b65r_sourcePoles,mem_insert_iff,mem_singleton_iff] at hz hw
  rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> norm_num at h
  all_goals rfl

theorem b65r_sourcePoles_card (n : ℕ) (e : Fin (n+1) ≃ b65r_sourcePoles) : n = 2 := by
  have hc := Nat.card_congr (e.trans b65r_sourcePoleEquiv.symm)
  simp only [Nat.card_fin] at hc
  omega

def b65r_punctureLabel : Fin 4 → Option b65r_sourcePoles :=
  ![some (b65r_sourcePole 0),some (b65r_sourcePole 1),some (b65r_sourcePole 2),none]

theorem b65r_punctureLabel_bijective : Function.Bijective b65r_punctureLabel := by
  constructor
  · intro i j hij
    have h := congrArg (Option.map Subtype.val) hij
    fin_cases i <;> fin_cases j <;>
      norm_num [b65r_punctureLabel,b65r_sourcePole,b65r_centres] at h
    all_goals rfl
  · intro a
    cases a with
    | none => exact ⟨3,rfl⟩
    | some a =>
      obtain ⟨i,hi⟩ := b65r_sourcePole_bijective.surjective a
      refine ⟨i.castSucc,?_⟩
      fin_cases i <;> simpa [b65r_punctureLabel] using congrArg some hi

def b65r_punctureLabelEquiv : Fin 4 ≃ Option b65r_sourcePoles :=
  Equiv.ofBijective b65r_punctureLabel b65r_punctureLabel_bijective

end HodgeLean.Foundations.Program
