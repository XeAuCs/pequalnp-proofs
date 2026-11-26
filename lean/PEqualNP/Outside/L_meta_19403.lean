import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19403.Build
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

variable {n k : ℕ}
variable (B : Fin k → Finset (Fin n))
variable (F : Fin k → Fin 2 → Finset (Finset (Fin n)))

def reject (i : Fin k) : Finset (Finset (Fin n)) := F i 0 ∪ F i 1

def bare (i : Fin k) (s : Fin 2) : Finset (Fin n) :=
  (B i).filter fun a => ∀ I ∈ F i s, a ∉ I

def earlier (i : Fin k) (s : Fin 2) : Finset (Fin k) :=
  Finset.univ.filter fun j => j < i ∧ F i s ⊆ reject F j

theorem mem_earlier (i j : Fin k) (s : Fin 2) :
    j ∈ earlier F i s ↔ j < i ∧ F i s ⊆ reject F j := by
  simp [earlier]

def outputs (D : Finset (Finset (Fin n))) : Finset (Fin k) :=
  Finset.univ.filter (fun j => D ⊆ reject F j)

theorem mem_outputs (D : Finset (Finset (Fin n))) (i : Fin k) :
    i ∈ outputs F D ↔ D ⊆ reject F i := by
  simp [outputs]

def make (D : Finset (Finset (Fin n))) : AndCountCircuit n :=
  ⟨k, (fun i => bare B F i 0), (fun i => earlier F i 0),
    (fun i => bare B F i 1), (fun i => earlier F i 1),
    ∅, outputs F D⟩

def Compatible (Y : Fin k → Finset (Finset (Fin n))) : Prop :=
  ∀ (i : Fin k), ∀ P ∈ Y i, ∀ s : Fin 2,
    (∃ a ∈ B i, a ∈ P ∧ ∀ I ∈ F i s, a ∉ I) ∨
      ∃ j < i, P ∈ Y j ∧ F i s ⊆ reject F j

theorem gate_eval (D : Finset (Finset (Fin n))) (Y : Fin k → Finset (Finset (Fin n)))
    (h : Compatible B F Y) : ∀ d (i : Fin k), i.val < d →
      (∀ I ∈ reject F i, (make B F D).gateValFuel I d i = false) ∧
      (∀ P ∈ Y i, ∀ U : Finset (Fin n), P ⊆ U → (make B F D).gateValFuel U d i = true) := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    have hfalse (I : Finset (Fin n)) (s : Fin 2) (hI : I ∈ F i s) :
        sideTrue I (bare B F i s) (earlier F i s) i ((make B F D).gateValFuel I d) = false := by
      simp only [sideTrue, decide_eq_false_iff_not]
      rintro (⟨a, ha, hai⟩ | ⟨j, hj, hji, hval⟩)
      · exact (Finset.mem_filter.mp ha).2 I hI hai
      · have hsub : F i s ⊆ reject F j := ((mem_earlier F i j s).mp hj).2
        have hlt : j.val < d := by
          change j.val < i.val at hji
          omega
        rw [(ih j hlt).1 I (hsub hI)] at hval
        cases hval
    have htrue (P : Finset (Fin n)) (hP : P ∈ Y i) (U : Finset (Fin n)) (hPU : P ⊆ U)
        (s : Fin 2) : sideTrue U (bare B F i s) (earlier F i s) i ((make B F D).gateValFuel U d) = true := by
      simp only [sideTrue, decide_eq_true_eq]
      rcases h i P hP s with ⟨a, haB, haP, haF⟩ | ⟨j, hji, hPj, hsub⟩
      · exact Or.inl ⟨a, Finset.mem_filter.mpr ⟨haB, haF⟩, hPU haP⟩
      · have hlt : j.val < d := by
          change j.val < i.val at hji
          omega
        exact Or.inr ⟨j, (mem_earlier F i j s).mpr ⟨hji, hsub⟩, hji, (ih j hlt).2 P hPj U hPU⟩
    constructor
    · intro I hI
      change (sideTrue I (bare B F i 0) (earlier F i 0) i ((make B F D).gateValFuel I d) &&
        sideTrue I (bare B F i 1) (earlier F i 1) i ((make B F D).gateValFuel I d)) = false
      rcases Finset.mem_union.mp hI with hx | hx
      · rw [hfalse I 0 hx]; rfl
      · rw [hfalse I 1 hx]; simp
    · intro P hP U hPU
      change (sideTrue U (bare B F i 0) (earlier F i 0) i ((make B F D).gateValFuel U d) &&
        sideTrue U (bare B F i 1) (earlier F i 1) i ((make B F D).gateValFuel U d)) = true
      rw [htrue P hP U hPU 0, htrue P hP U hPU 1]
      rfl

theorem assemble (D : Finset (Finset (Fin n))) (Y : Fin k → Finset (Finset (Fin n)))
    (h : Compatible B F Y) :
      (make B F D).WellFormed ∧
      (∀ a : Fin n,
        (Finset.univ.filter (fun i => a ∈ (make B F D).leftVars i ∨ a ∈ (make B F D).rightVars i)).card ≤
          (Finset.univ.filter (fun i => a ∈ B i)).card) ∧
      (∀ I ∈ D, (make B F D).eval I = false) ∧
      (∀ i : Fin k, D ⊆ reject F i → ∀ P ∈ Y i, ∀ U : Finset (Fin n), P ⊆ U → (make B F D).eval U = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    constructor <;> intro j hj
    · exact ((mem_earlier F i j 0).mp hj).1
    · exact ((mem_earlier F i j 1).mp hj).1
  · intro a
    change (Finset.univ.filter (fun i : Fin k => a ∈ bare B F i 0 ∨ a ∈ bare B F i 1)).card ≤
      (Finset.univ.filter (fun i : Fin k => a ∈ B i)).card
    apply Finset.card_le_card
    intro i hi
    have hs : a ∈ bare B F i 0 ∨ a ∈ bare B F i 1 := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hs.elim (fun h0 => (Finset.mem_filter.mp h0).1) (fun h1 => (Finset.mem_filter.mp h1).1)
  · intro I hI
    simp only [eval, decide_eq_false_iff_not]
    rintro (⟨a, ha, _⟩ | ⟨i, hi, hei⟩)
    · exact Finset.notMem_empty _ ha
    · have hsub : D ⊆ reject F i := (mem_outputs F D i).mp hi
      have he : (make B F D).gateVal I i = false := (gate_eval B F D Y h k i i.isLt).1 I (hsub hI)
      rw [he] at hei
      cases hei
  · intro i hi P hP U hPU
    simp only [eval, decide_eq_true_eq]
    exact Or.inr ⟨i, (mem_outputs F D i).mpr hi, (gate_eval B F D Y h k i i.isLt).2 P hP U hPU⟩

end PEqualNP.Outside.L_meta_19403.Build


theorem PEqualNP.Outside.L_meta_19403 :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1))) (x4 : Fin x2 → Finset (Fin x1)) (x5 : Fin x2 → Fin (2 : ℕ) → Finset (Finset (Fin x1))) (x6 : Fin x2 → Finset (Finset (Fin x1))),   have x7 : Finset (Fin x2) := Finset.univ;   have x8 : Fin x2 → Finset (Finset (Fin x1)) := fun (x8 : Fin x2) => x5 x8 (0 : Fin (2 : ℕ)) ∪ x5 x8 (1 : Fin (2 : ℕ));   (∀ (x9 : Fin x2), ∀ x10 ∈ x6 x9, ∀ (x12 : Fin (2 : ℕ)), (∃ x13 ∈ x4 x9, x13 ∈ x10 ∧ ∀ x14 ∈ x5 x9 x12, x13 ∉ x14) ∨ ∃ x13 < x9, x10 ∈ x6 x13 ∧ x5 x9 x12 ⊆ x8 x13) →     ∃ (x10 : PEqualNP.AndCount.AndCountCircuit x1),       x10.WellFormed ∧         x10.size = x2 ∧           (have x11 : Finset (Fin x10.size) := Finset.univ;             ∀ (x12 : Fin x1), {x13 ∈ x11 | x12 ∈ x10.leftVars x13 ∨ x12 ∈ x10.rightVars x13}.card ≤ {x13 ∈ x7 | x12 ∈ x4 x13}.card) ∧             (∀ x11 ∈ x3, x10.eval x11 = Bool.false) ∧ ∀ (x11 : Fin x2), x3 ⊆ x8 x11 → ∀ x13 ∈ x6 x11, ∀ (x15 : Finset (Fin x1)), x13 ⊆ x15 → x10.eval x15 = Bool.true := by
  intro n k D B F Y
  dsimp only
  intro hyp
  let C := PEqualNP.Outside.L_meta_19403.Build.make B F D
  have h := PEqualNP.Outside.L_meta_19403.Build.assemble B F D Y hyp
  exact ⟨C, h.1, rfl, h.2⟩
