universe u

abbrev Relation (A : Type u) (B : Type u) := A → B → Prop

abbrev Symm {A : Type u} (r : Relation A A) := ∀ x y : A, r x y → r y x

abbrev AntiSym {A : Type u} (r : Relation A A) := ∀ x y : A, r x y → r y x → x = y

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



example: ¬(Symm R1) := by
intro h
simp[Symm, R1] at h
have := h 2
simp at this

example: ¬(AntiSym R1) := by
intro h
simp[AntiSym, R1] at h
have := h 0
simp at this


-- Unwrapping some of the simp tacticts processes
theorem h_20 : (2: Fin 4) = (0 : Fin 4) → False := by
intro h
apply Fin.noConfusion h
intro h2
repeat rw[Nat.mod_succ] at h2
rw[Nat.zero_mod] at h2
apply Nat.noConfusion h2

theorem h_24 : 2 % 4 = 2 := by
rfl

theorem h_21 : (2: Fin 4) = (1 : Fin 4) → False := by
intro h
apply Fin.noConfusion h
intro h2
repeat rw[Nat.mod_succ] at h2
rw[Nat.one_mod] at h2
rw[h_24] at h2
simp_all

example: Symm R2 := by
simp[Symm, R2]
intro x y h
match x with
  | 0 =>
    match y with
    | 0 => exact h
    | 1 => exact rfl
    | 2 => exact
    (Or.elim h (λ h20 => h_20 h20) (λ h21 => h_21 h21))
    | 3 => simp at h
  | 1 =>
    match y with
    | 0 => exact (Or.inr rfl)
    | 1 => exact (h)
    | 2 => simp at h
    | 3 => simp at h
  | 2 => simp at h
  | 3 => simp at h



example: ¬(AntiSym R2) := by
intro h
simp[AntiSym, R2] at h
have := h 0
simp at this

example: Symm R3 := by
simp[Symm, R3]
intro x y
match x with
  | 0 =>
    match y with
    | 0 => exact (λ h => h)
    | 1 => exact (λ h => Or.inl rfl)
    | 2 => simp
    | 3 => exact (λ h => Or.inl rfl)
  | 1 =>
    match y with
      | 0 => exact (λ h => Or.inr (Or.inl rfl))
      | 1 => exact (λ h => h)
      | 2 => simp
      | 3 => simp
  | 2 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => exact (λ h => h)
      | 3 => simp
  | 3 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => exact (λ h => h)

example: ¬(AntiSym R3) := by
intro h
simp[AntiSym, R3] at h
have := h 0
simp at this

example: ¬(Symm R4) := by
intro h
simp[Symm, R4] at h
have := h 2
simp at this

example: AntiSym R4 := by
simp[AntiSym, R4]
intro x y
match x with
  | 0 =>
    match y with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | 3 => simp
  | 1 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp
  | 2 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp
  | 3 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp

example: ¬(Symm R5) := by
intro h
simp[Symm, R5] at h
have := h 0
simp at this

example: AntiSym R5 := by
simp[AntiSym, R5]
intro x y
match x with
  | 0 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp
  | 1 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp
  | 2 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp
  | 3 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp

example: ¬(Symm R6) := by
intro h
simp[Symm, R6] at h
have := h 2
simp at this

example: AntiSym R6 := by
simp[AntiSym, R6]
intro x y
match x with
  | 0 => simp
  | 1 => simp
  | 2 =>
    match y with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | 3 => simp
  | 3 => simp
