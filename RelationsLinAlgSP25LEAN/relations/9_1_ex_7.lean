-- LEAN proofs of example 7 from Rosen. 9.1
-- includes Def. 3 -- reflexive

universe u

def Refl {A : Type u} (r : A → A → Prop) := ∀ x : A, r x x

def Relation (A : Type u) (B : Type u) := A → B → Prop


def R1 (x y : Fin 4) := match x with
  | 0 => y = 0 ∨ y = 1
  | 1 => y = 0 ∨ y = 1
  | 2 => y = 3
  | 3 => y = 0 ∨ y = 3

def R2 (x y : Fin 4) := match x with
  | 0 => y = 0 ∨ y = 1
  | 1 => y = 0
  | _ => false

def R3 (x y : Fin 4) := match x with
  | 0 => y = 0 ∨ y = 1 ∨ y = 3
  | 1 => y = 0 ∨ y = 1
  | 2 => y= 2
  | 3 => y = 0 ∨ y = 3

def R4 (x y : Fin 4) := match x with
  | 1 => y = 0
  | 2 => y = 0 ∨ y = 1
  | 3 => y = 0 ∨ y = 1 ∨ y = 2
  | _ => false

def R5 (x y : Fin 4) := match x with
  | 0 => y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3
  | 1 => y = 1 ∨ y = 2 ∨ y = 3
  | 2 => y = 2 ∨ y = 3
  | 3 => y = 3


def R6 (x y : Fin 4) := match x with
  | 2 => y = 3
  | _ => false


example: ¬ (Refl R1) := by
intro h
simp[Refl, R1] at h
have := h 2
simp at this

example: ¬ (Refl R2) := by
intro h
simp[Refl, R2] at h
have := h 2
simp at this

example: Refl R3 := by
  simp [Refl, R3]
  intro x
  match x with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl
  | 2 => rfl
  | 3 => exact Or.inr rfl

example: ¬(Refl R4) := by
intro h
simp[Refl, R4] at h
have := h 1
simp at this

example: Refl R5 := by
  simp [Refl, R5]
  intro x
  match x with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inl rfl
  | 2 => exact Or.inl rfl
  | 3 => rfl

example: ¬(Refl R6) := by
intro h
simp[Refl, R6] at h
have := h 0
simp at this
