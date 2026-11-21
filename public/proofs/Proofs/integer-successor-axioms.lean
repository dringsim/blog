inductive Z : Type
| _0 : Z
| S  : Z → Z
| P  : Z → Z
open Z
def _1 := S _0
def _2 := S _1
variable (a b c d : Z)
@[simp]
axiom PSZ : P (S a) = a
@[simp]
axiom SPZ : S (P a) = a

example : P a = S (P (P a)) := (SPZ (P a)).symm

instance : Add Z where
  add a b := _add a b
    where _add a b := match b with
    | _0   => a
    | S b' => S (_add a b')
    | P b' => P (_add a b')

theorem add_unique
  (add' : Z → Z → Z)
  (h1 : add' a _0 = a)
  (h2 : ∀ b, add' a (S b) = S (add' a b))
  (h3 : ∀ b, add' a (P b) = P (add' a b)) :
  add' a b = a + b := by
    induction b with
    | _0      => calc
      add' a _0 = a      := by rw[h1]
      _         = a + _0 := by rfl
    | S b' ih => calc
      add' a (S b') = S (add' a b') := by rw[h2 b']
      _             = S (a + b')    := by rw[ih]
      _             = a + S b'      := by rfl
    | P b' ih => calc
      add' a (P b') = P (add' a b') := by rw[h3 b']
      _             = P (a + b')    := by rw[ih]
      _             = a + P b'      := by rfl

@[simp]
theorem add_zero : a + _0 = a := by
  rfl

@[simp]
theorem zero_add : _0 + a = a := by
  induction a with
  | _0      => rfl
  | S a' ih => calc
    _0 + S a' = S (_0 + a') := by rfl
    _         = S a'        := by rw[ih]
  | P a' ih => calc
    _0 + P a' = P (_0 + a') := by rfl
    _         = P a'        := by rw[ih]

@[simp]
theorem add_succ : a + S b = S (a + b) := by
  rfl

@[simp]
theorem succ_add : S a + b = S (a + b) := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    S a + S b' = S (S a + b')   := by rfl
    _          = S (S (a + b')) := by rw[ih]
  | P b' ih => calc
    S a + P b' = P (S a + b')   := by rfl
    _          = P (S (a + b')) := by rw[ih]
    _          = S (P (a + b')) := by rw[PSZ,SPZ]

@[simp]
theorem add_pred : a + P b = P (a + b) := by
  rfl

@[simp]
theorem pred_add : P a + b = P (a + b) := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    P a + S b' = S (P a + b')   := by rfl
    _          = S (P (a + b')) := by rw[ih]
    _          = P (S (a + b')) := by rw[SPZ,PSZ]
  | P b' ih => calc
    P a + P b' = P (P a + b')   := by rfl
    _          = P (P (a + b')) := by rw[ih]

@[simp]
theorem add_comm : a + b = b + a := by
  induction b with
  | _0 => rw[add_zero, zero_add]
  | S b' ih => calc
    a + S b' = S (a + b') := by rfl
    _        = S (b' + a) := by rw[ih]
    _        = S b' + a   := by rw[succ_add]
  | P b' ih => calc
    a + P b' = P (a + b') := by rfl
    _        = P (b' + a) := by rw[ih]
    _        = P b' + a   := by rw[pred_add]

@[simp]
theorem add_asso : (a + b) + c = a + (b + c) := by
  induction c with
  | _0      => rfl
  | S c' ih => calc
    (a + b) + S c' = S ((a + b) + c') := by rfl
    _              = S (a + (b + c')) := by rw[ih]
    _              = a + (b + S c')   := by rfl
  | P c' ih => calc
    (a + b) + P c' = P ((a + b) + c') := by rfl
    _              = P (a + (b + c')) := by rw[ih]
    _              = a + (b + P c')   := by rfl

example : (a + b) + (c + d) = (a + c) + (b + d) := calc
  (a + b) + (c + d) = a + (b + c) + d   := by repeat rw[add_asso]
  _                 = a + (c + b) + d   := by rw[add_comm b c]
  _                 = (a + c) + (b + d) := by repeat rw[add_asso]

theorem add_elim {a b c : Z} (h : a + c = b + c) : a = b := by
  induction c with
  | _0 =>
    simp at h
    exact h
  | S c' ih =>
    simp at h
    exact ih h
  | P c' ih =>
    simp at h
    exact ih h

theorem add_pos_right {a b : Z} (h : a = a + S b) : False := by
  rw [←zero_add a,add_asso,add_comm a (S b),←add_asso] at h
  cases add_elim h

theorem add_neq_right {a b : Z} (h : a = a + P b) : False := by
  rw [←zero_add a,add_asso,add_comm a (P b),←add_asso] at h
  cases add_elim h

theorem add_inv : ∃ b, a + b = c := by
  induction a with
  | _0 => exact ⟨c, zero_add c⟩
  | S a' ih =>
    have ⟨b, heq⟩ := ih
    have heq := congrArg P heq
    have heq := congrArg S heq
    rw[←add_pred,←succ_add,SPZ] at heq
    exact ⟨P b, heq⟩
  | P a' ih =>
    have ⟨b, heq⟩ := ih
    have heq := congrArg S heq
    have heq := congrArg P heq
    rw[←add_succ,←pred_add,PSZ] at heq
    exact ⟨S b, heq⟩

def Z.neg : Z → Z
| _0 => _0
| S n => P (neg n)
| P n => S (neg n)

instance : Neg Z where
  neg := Z.neg

@[simp]
theorem neg_neg_elim : -(-a) = a := by
  induction a with
  | _0 => rfl
  | S a' ih => calc
    -(-(S a')) = -(P (-a')) := by rfl
    _          = S (-(-a')) := by rfl
    _          = S a'       := by rw[ih]
  | P a' ih => calc
    -(-(P a')) = -(S (-a')) := by rfl
    _          = P (-(-a')) := by rfl
    _          = P a'       := by rw[ih]

@[simp]
theorem add_neg : a + -a = _0 := by
  induction a with
  | _0 => exact Eq.refl _0
  | S a' ih =>
    have ih := congrArg S ih
    have ih := congrArg P ih
    rw[←succ_add,←add_pred,PSZ] at ih
    assumption
  | P a' ih =>
    have ih := congrArg P ih
    have ih := congrArg S ih
    rw[←pred_add,←add_succ,SPZ] at ih
    assumption

@[simp]
theorem neg_sum : -(a + b) = -a + -b := by
  induction b with
  | _0 => rfl
  | S b' ih => calc
    -(a + S b') = -(S (a + b')) := by rfl
    _           = P (-(a + b')) := by rfl
    _           = P (-a + -b')  := by rw[ih]
    _           = -a + P (-b')  := by rfl
    _           = -a + -(S b')  := by rfl
  | P b' ih => calc
    -(a + P b') = -(P (a + b')) := by rfl
    _           = S (-(a + b')) := by rfl
    _           = S (-a + -b')  := by rw[ih]
    _           = -a + S (-b')  := by rfl
    _           = -a + -(P b')  := by rfl

instance : Sub Z where
  sub a b := a + -b

@[simp]
theorem sub_addneg : a - b = a + -b := by
  rfl

instance : Mul Z where
  mul a b := _mul a b
    where _mul a b := match b with
      | _0   => _0
      | S b' => _mul a b' + a
      | P b' => _mul a b' - a

theorem mul_unique
  (mul' : Z → Z → Z)
  (h1 : mul' a _0 = _0)
  (h2 : ∀ b, mul' a (S b) = mul' a b + a)
  (h3 : ∀ b, mul' a (P b) = mul' a b - a) :
  mul' a b = a * b := by
    induction b with
    | _0      => calc
      mul' a _0 = _0      := by rw[h1]
    | S b' ih => calc
      mul' a (S b') = mul' a b' + a := by rw[h2 b']
      _             = a * b' + a    := by rw[ih]
      _             = a * S b'      := by rfl
    | P b' ih => calc
      mul' a (P b') = mul' a b' - a := by rw[h3 b']
      _             = a * b' - a    := by rw[ih]
      _             = a * P b'      := by rfl

@[simp]
theorem mul_zero : a * _0 = _0 := by
  rfl

@[simp]
theorem zero_mul : _0 * a = _0 := by
  induction a with
  | _0      => rfl
  | S a' ih => calc
    _0 * S a' = _0 * a' := by rfl
    _         = _0      := by rw[ih]
  | P a' ih => calc
    _0 * P a' = _0 * a' := by rfl
    _         = _0      := by rw[ih]

@[simp]
theorem mul_one : a * _1 = a := calc
  a * _1 = a * S _0   := by rfl
  _      = a * _0 + a := by rfl
  _      = a          := by simp[mul_zero]

@[simp]
theorem one_mul : _1 * a = a := by
  induction a with
  | _0      => rw[mul_zero]
  | S a' ih => calc
    _1 * S a' = _1 * a' + _1 := by rfl
    _         = a' + _1      := by rw[ih]
    _         = S a'         := by rfl
  | P a' ih => calc
    _1 * P a' = _1 * a' - _1 := by rfl
    _         = a' - _1      := by rw[ih]
    _         = P a'         := by rfl

@[simp]
theorem mul_succ : a * S b = a * b + a := by
  rfl

@[simp]
theorem mul_pred : a * P b = a * b - a := by
  rfl

@[simp]
theorem succ_mul : S a * b = a * b + b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    S a * S b' = S a * b' + S a      := by rfl
    _          = a * b' + b' + S a   := by rw[ih]
    _          = a * b' + (a + S b') := by simp
    _          = a * b' + a + S b'   := by rw[add_asso]
    _          = a * S b' + S b'     := by rfl
  | P b' ih => calc
    S a * P b' = S a * b' - S a         := by rfl
    _          = a * b' + b' - S a      := by rw[ih]
    _          = a * b' + b' + P (-a)   := by rfl
    _          = a * b' + (b' + P (-a)) := by rw[add_asso]
    _          = a * b' + (-a + P b')   := by simp
    _          = (a * b' + -a) + P b'   := by rw[add_asso]
    _          = (a * b' - a) + P b'    := by rfl
    _          = a * P b' + P b'        := by rw[←mul_pred]

@[simp]
theorem pred_mul : P a * b = a * b - b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    P a * S b' = P a * b' + P a         := by rfl
    _          = a * b' + -b' + P a     := by simp[ih]
    _          = a * b' + (-b' + P a)   := by rw[add_asso]
    _          = a * b' + (a + P (-b')) := by simp
    _          = (a * b' + a) + P (-b') := by rw[add_asso]
    _          = a * S b' - S b'        := by rfl
  | P b' ih => calc
    P a * P b' = P a * b' - P a          := by rfl
    _          = a * b' + -b' + -(P a)   := by simp[ih]
    _          = a * b' + -b' + S (-a)   := by rfl
    _          = a * b' + (-b' + S (-a)) := by rw[add_asso]
    _          = a * b' + (-a + S (-b')) := by simp
    _          = a * b' + -a + S (-b')   := by rw[add_asso]
    _          = a * P b' - P b'         := by rfl

@[simp]
theorem mul_comm : a * b = b * a := by
  induction b with
  | _0      => rw[mul_zero, zero_mul]
  | S b' ih => calc
    a * S b' = a * b' + a := by rfl
    _        = b' * a + a := by rw[ih]
    _        = S b' * a   := by rw[succ_mul]
  | P b' ih => calc
    a * P b' = a * b' - a := by rfl
    _        = b' * a - a := by rw[ih]
    _        = P b' * a   := by rw[pred_mul]

@[simp]
theorem mul_right_dist : (b + c) * a = b * a + c * a := by
  induction a with
  | _0      => rfl
  | S a' ih => calc
    (b + c) * S a' = (b + c) * a' + (b + c)      := by rfl
    _              = b + (b * a' + c + c * a')   := by simp[ih]
    _              = (b + b * a') + (c + c * a') := by repeat (rw[add_asso])
    _              = b * S a' + c * S a'         := by simp
  | P a' ih => calc
    (b + c) * P a' = (b + c) * a' - (b + c)        := by rfl
    _              = -b + (b * a' + c * a') + -c   := by simp[ih]
    _              = (-b + b * a') + (c * a' + -c) := by repeat (rw[add_asso])
    _              = b * P a' + c * P a'           := by simp

@[simp]
theorem mul_left_dist : a * (b + c) = a * b + a * c := by
  induction a with
  | _0      => simp
  | S a' ih => calc
    S a' * (b + c) = a' * (b + c) + (b + c)      := by rw[succ_mul]
    _              = b + (a' * b + c + a' * c)   := by simp[ih]
    _              = (b + a' * b) + (c + a' * c) := by repeat (rw[add_asso])
    _              = S a' * b + S a' * c         := by simp
  | P a' ih => calc
    P a' * (b + c) = a' * (b + c) - (b + c)        := by rw[pred_mul]
    _              = -b + (a' * b + a' * c) + -c   := by simp[ih]
    _              = (-b + a' * b) + (a' * c + -c) := by repeat (rw[add_asso])
    _              = P a' * b + P a' * c           := by simp

@[simp]
theorem mul_neg : a * -b = -(a * b) := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    a * -(S b') = a * -b' - a   := by rfl
    _           = -(a * b' + a) := by simp[ih]
    _           = -(a * S b')   := by rfl
  | P b' ih => calc
    a * -(P b') = a * -b' + a   := by rfl
    _           = -(a * b' - a) := by simp[ih]
    _           = -(a * P b')   := by rfl

@[simp]
theorem neg_mul : -a * b = -(a * b) := by
  induction a with
  | _0      => simp
  | S a' ih => calc
    -(S a') * b = -a' * b - b   := by simp
    _           = -(a' * b + b) := by simp[ih]
    _           = -(S a' * b)   := by simp
  | P a' ih => calc
    -(P a') * b = -a' * b + b   := by simp
    _           = -(a' * b - b) := by simp[ih]
    _           = -(P a' * b)   := by simp

@[simp]
theorem mul_asso : (a * b) * c = a * (b * c) := by
  induction c with
  | _0      => rfl
  | S c' ih => calc
    (a * b) * S c' = (a * b) * c' + (a * b) := by rfl
    _              = a * (b * c') + (a * b) := by rw[ih]
    _              = a * (b * c' + b)       := by rw[mul_left_dist]
    _              = a * (b * S c')         := by rfl
  | P c' ih => calc
    (a * b) * P c' = (a * b) * c' - (a * b)  := by rfl
    _              = a * (b * c') + -(a * b) := by simp[ih]
    _              = a * (b * c' + -b)       := by simp[mul_left_dist]
    _              = a * (b * P c')          := by simp

example : (a * b) * (c * d) = (a * c) * (b * d) := calc
  (a * b) * (c * d) = a * (b * c) * d   := by repeat rw[mul_asso]
  _                 = a * (c * b) * d   := by rw[mul_comm b c]
  _                 = (a * c) * (b * d) := by repeat rw[mul_asso]

theorem mul_zero_div (h : a * b = _0) : a = _0 ∨ b = _0 :=
  match a, b with
  | _0, _    => Or.inl (Eq.refl _0)
  | _, _0    => Or.inr (Eq.refl _0)

def Z.ble (a b : Z) : Bool :=
  _ble a b _0
    where _ble a b c := match a, b, c with
    | _0, _0, P _    => false
    | _0, _0, _      => true
    | _0, S b', P c' => _ble _0 b' c'
    | _0, S b', c'   => _ble _0 b' (S c')
    | _0, P b', S c' => _ble _0 b' c'
    | _0, P b', c'   => _ble _0 b' (P c')
    | S a', S b', c' => _ble a' b' c'
    | S a', b', c'   => _ble a' (P b') c'
    | P a', P b', c' => _ble a' b' c'
    | P a', b', c'   => _ble a' (S b') c'

def Z.le : Prop :=
  ble a b = true

instance : LE Z where
  le := Z.le
