inductive N : Type
| _0 : N
| S  : N → N
open N
def _1 := S _0
def _2 := S _1
def _3 := S _2
variable (a b c d : N)

theorem succ_neq_zero : S a ≠ _0 := by
  simp

theorem succ_eq_succ (h : S a = S b) : a = b := by
  simp at *
  assumption

theorem succ_eq_succ_of_eq (h : a = b) : S a = S b :=
  congrArg S h

theorem self_neq_succ : S a ≠ a := by
  induction a with
  | _0      => simp
  | S a' ih => simp[ih]

def N.P : N → N
| _0  => _0
| S a => a

@[simp]
theorem pred_succ : P (S a) = a := by
  rfl

example (p : N → N → Prop)
(h1 : ∀ a, p _0 a)
(h2 : ∀ a, p a _0)
(h3 : ∀ a, ∀ b, p a b → p (S a) (S b)) :
∀ a, ∀ b, p a b := by
  intro a
  induction a with
  | _0       => intro b; exact h1 b
  | S a' iha => intro b; induction b with
    | _0       => exact h2 (S a')
    | S b' ihb => exact h3 a' b' (iha b')

instance : Add N where
  add a b := _add a b
    where _add a b := match b with
    | _0   => a
    | S b' => S (_add a b')

theorem add_unique
  (add' : N → N → N)
  (h1 : add' a _0 = a)
  (h2 : ∀ b, add' a (S b) = S (add' a b)) :
  add' a b = a + b := by
    induction b with
    | _0      => calc
      add' a _0 = a      := by rw[h1]
      _         = a + _0 := by rfl
    | S b' ih => calc
      add' a (S b') = S (add' a b') := by rw[h2 b']
      _             = S (a + b')    := by rw[ih]
      _             = a + S b'      := by rfl

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

@[simp]
theorem add_one : a + _1 = S a := by
  rfl

@[simp]
theorem one_add : _1 + a = S a := calc
  _1 + a = S _0 + a   := by rfl
  _      = S (_0 + a) := by rw[succ_add]
  _      = S a        := by rw[zero_add]

@[simp]
theorem add_comm : a + b = b + a := by
  induction b with
  | _0      => rw[add_zero, zero_add]
  | S b' ih => calc
    a + S b' = S (a + b') := by rfl
    _        = S (b' + a) := by rw[ih]
    _        = S b' + a   := by rw[succ_add]

@[simp]
theorem add_asso {a b c : N} : (a + b) + c = a + (b + c) := by
  induction c with
  | _0      => rfl
  | S c' ih => calc
    (a + b) + S c' = S ((a + b) + c') := by rfl
    _              = S (a + (b + c')) := by rw[ih]
    _              = a + (b + S c')   := by rfl

theorem add_add_add_comm : (a + b) + (c + d) = (a + c) + (b + d) := calc
  (a + b) + (c + d) = a + (b + c) + d   := by repeat rw[add_asso]
  _                 = a + (c + b) + d   := by rw[add_comm b c]
  _                 = (a + c) + (b + d) := by repeat rw[add_asso]

theorem add_elim {a b c : N} (h : a + c = b + c) : a = b := by
  induction c with
  | _0 =>
    simp at h
    exact h
  | S c' ih =>
    simp at h
    exact ih h

example {a b : N} (h : a = a + S b) : False := by
  rw [←zero_add a,add_asso,add_comm a (S b),←add_asso] at h
  cases add_elim h

example {a b : N} (h : a + S b = _0) : False := by
  simp at *

theorem add_zero_iff_zero_and_zero {a b : N} : a + b = _0 ↔ a = _0 ∧ b = _0 := by
  apply Iff.intro
  . intro h
    match a, b with
    | _0, _0 => exact ⟨Eq.refl _0, Eq.refl _0⟩
    | S _, _ => simp at h
    | _, S _ => cases h
  . intro h
    simp[*]

instance : Mul N where
  mul a b := _mul a b
    where _mul a b := match b with
      | _0   => _0
      | S b' => _mul a b' + a

theorem mul_unique
  (mul' : N → N → N)
  (h1 : mul' a _0 = _0)
  (h2 : ∀ b, mul' a (S b) = mul' a b + a) :
  mul' a b = a * b := by
    induction b with
    | _0      => calc
      mul' a _0 = _0      := by rw[h1]
    | S b' ih => calc
      mul' a (S b') = mul' a b' + a := by rw[h2 b']
      _             = a * b' + a    := by rw[ih]
      _             = a * S b'      := by rfl

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

@[simp]
theorem mul_succ : a * S b = a * b + a := by
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

@[simp]
theorem mul_two : a * _2 = a + a := calc
  a * _2 = a * _1 + a := by rfl
  _      = a + a      := by simp

@[simp]
theorem two_mul : _2 * a = a + a := calc
  _2 * a = S _1 * a   := by rfl
  _      = _1 * a + a := by simp
  _      = a + a      := by simp

@[simp]
theorem mul_comm : a * b = b * a := by
  induction b with
  | _0      => rw[mul_zero, zero_mul]
  | S b' ih => calc
    a * S b' = a * b' + a := by rfl
    _        = b' * a + a := by rw[ih]
    _        = S b' * a   := by rw[succ_mul]

@[simp]
theorem mul_right_dist {a b c : N} : (b + c) * a = b * a + c * a := by
  induction a with
  | _0      => rfl
  | S a' ih => calc
    (b + c) * S a' = (b + c) * a' + (b + c)      := by rfl
    _              = b + (b * a' + c + c * a')   := by simp[ih]
    _              = (b + b * a') + (c + c * a') := by repeat (rw[add_asso])
    _              = b * S a' + c * S a'         := by simp

@[simp]
theorem mul_left_dist {a b c : N} : a * (b + c) = a * b + a * c := by
  rw[mul_comm, mul_comm a b, mul_comm a c]
  exact mul_right_dist

@[simp]
theorem mul_asso {a b c : N} : (a * b) * c = a * (b * c) := by
  induction c with
  | _0      => rfl
  | S c' ih => calc
    (a * b) * S c' = (a * b) * c' + (a * b) := by rfl
    _              = a * (b * c') + (a * b) := by rw[ih]
    _              = a * (b * c' + b)       := by rw[mul_left_dist]
    _              = a * (b * S c')         := by rfl

theorem mul_mul_mul_comm : (a * b) * (c * d) = (a * c) * (b * d) := calc
  (a * b) * (c * d) = a * (b * c) * d   := by repeat rw[mul_asso]
  _                 = a * (c * b) * d   := by rw[mul_comm b c]
  _                 = (a * c) * (b * d) := by repeat rw[mul_asso]

theorem mul_zero_iff_zero_or_zero {a b : N} : a * b = _0 ↔ a = _0 ∨ b = _0 := by
  apply Iff.intro
  . intro _
    match a, b with
    | _0, _    => exact Or.inl (Eq.refl _0)
    | _, _0    => exact Or.inr (Eq.refl _0)
  . intro h
    apply h.elim
    repeat
    . intro _
      simp[*]

def N.beq : N → N → Bool
  | _0,  _0   => true
  | _0,  S _  => false
  | S _, _0   => false
  | S a, S b  => beq a b

def N.eq : Prop :=
  beq a b = true

theorem beq_eq {a b : N} (h : eq a b) : a = b :=
  match a, b with
  | _0, _0     => Eq.refl _0
  | S a', S b' =>
    have h0 : beq a' b' = beq (S a') (S b') := by rfl;
    have h1 : eq a' b' := h0.trans h;
    congrArg S (@beq_eq a' b' h1)

def N.ble : N → N → Bool
  | _0,  _   => true
  | S _, _0  => false
  | S a, S b => ble a b

def N.le : Prop :=
  ble a b = true

instance : LE N where
  le := N.le

theorem zero_le : _0 ≤ a :=
  Eq.refl (ble _0 a)

theorem no_succ_le_zero : S a ≤ _0 → False := by
  intro h
  cases h

theorem eq_zero_of_le_zero {a : N} (h : a ≤ _0) : a = _0 := by
  match a with
  | _0 => simp

theorem succ_le_succ {a b : N} (h : a ≤ b) : S a ≤ S b := by
  have h : ble a b = true := h
  rw[show ble a b = ble (S a) (S b) from rfl] at h
  exact h

theorem pred_le_pred {a b : N} (h : S a ≤ S b) : a ≤ b := by
  have h : ble (S a) (S b) = true := h
  rw[show ble (S a) (S b) = ble a b from rfl] at h
  exact h

theorem le_succ : a ≤ S a := by
  induction a with
  | _0      => exact Eq.refl (ble _0 _1)
  | S a' ih => exact ih

theorem le_refl : a ≤ a := by
  induction a with
  | _0      => exact zero_le _0
  | S a' ih => exact ih

theorem le_of_eq {a b : N} (h : a = b) : a ≤ b :=
  h ▸ le_refl a

theorem le_antisymm {a b : N} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  match a, b with
  | _0, _0     => Eq.refl _0
  | S a', S b' => congrArg S (@le_antisymm a' b' h1 h2)

theorem le_trans {a b c : N} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  match a, b, c with
  | _0, _, c'       => zero_le c'
  | S a', S b', S c' => @le_trans a' b' c' h1 h2

theorem le_total {a b : N} : a ≤ b ∨ b ≤ a :=
  match a, b with
  | _0, b'     => Or.inl (zero_le b')
  | a', _0     => Or.inr (zero_le a')
  | S a', S b' => @le_total a' b'

theorem le_add {a b : N} : a ≤ b ↔ a + c ≤ b + c := by
  apply Iff.intro
  . intro h
    induction c with
    | _0      => exact h
    | S c' ih => exact ih
  . intro h
    induction c with
    | _0      => exact h
    | S c' ih => exact ih h

theorem le_add_right {a b : N} (h : a ≤ b) : a ≤ b + c := by
  induction c with
  | _0      => exact h
  | S c' ih => exact le_trans ih (le_succ (b + c'))

theorem le_mul_right {a b : N} (h : a ≤ b) : a ≤ b * S c := by
  induction c with
  | _0      =>
    rw[←mul_one b] at h
    exact h
  | S c' ih =>
    exact le_add_right b ih

theorem le_addeq {a b : N} : a ≤ b ↔ ∃ c, a + c = b := by
  apply Iff.intro
  . intro h
    match a, b with
    | _0, b'     =>
      exact ⟨b', zero_add b'⟩
    | S a', S b' =>
      have ⟨c, h0⟩ := le_addeq.mp (pred_le_pred h);
      simp at *
      exact ⟨c, h0⟩
  . intro ⟨c, h⟩
    match a, c, b with
    | a', _0, b'     =>
      rw[add_zero] at h
      exact le_of_eq h
    | _0, _, b'      =>
      exact zero_le b'
    | S a', c', S b' =>
      rw[succ_add] at h
      exact (@le_addeq a' b').mpr ⟨c', congrArg P h⟩

theorem zero_le_alt : _0 ≤ a :=
  le_addeq.mpr ⟨a, zero_add a⟩

theorem le_refl_alt : a ≤ a :=
  le_addeq.mpr ⟨_0, add_zero a⟩

theorem le_of_eq_alt {a b : N} (h : a = b) : a ≤ b :=
  le_addeq.mpr ⟨_0, h ▸ add_zero a⟩

theorem le_antisymm_alt {a b : N} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  have ⟨c1, heq1⟩ := le_addeq.mp h1
  have ⟨c2, heq2⟩ := le_addeq.mp h2
  have hc := heq1 ▸ heq2
  rw[add_asso, add_comm] at hc
  rw (occs := .pos [2]) [←zero_add a] at hc
  have hc := add_elim hc
  have ⟨c1z, c2z⟩ := add_zero_iff_zero_and_zero.mp hc
  simp[c1z] at heq1
  exact heq1

theorem le_trans_alt {a b c : N} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  have ⟨c1, heq1⟩ := le_addeq.mp h1
  have ⟨c2, heq2⟩ := le_addeq.mp h2
  le_addeq.mpr ⟨c1 + c2, add_asso ▸ (heq1 ▸ heq2)⟩

theorem le_total_alt {a b : N} : a ≤ b ∨ b ≤ a := by
  induction a with
  | _0      => exact Or.inl (le_addeq.mpr ⟨b, zero_add b⟩)
  | S a' ih =>
    apply ih.elim
    . intro hab
      have ⟨c, heq⟩ := le_addeq.mp hab
      match c with
      | _0 =>
        have h := le_addeq.mpr ⟨_1, (congrArg S heq).symm⟩
        simp at *
        exact Or.inr h
      | S c' =>
        rw[add_succ, ←succ_add] at heq
        exact Or.inl (le_addeq.mpr ⟨c', heq⟩)
    . intro hba
      have ⟨c, heq⟩ := le_addeq.mp hba
      exact Or.inr (le_addeq.mpr ⟨S c, congrArg S heq⟩)

theorem le_add_alt {a b : N} : a ≤ b ↔ a + c ≤ b + c := by
  apply Iff.intro
  . intro h
    have ⟨c0, heq⟩ := le_addeq.mp h
    have heq := congrArg (fun n => n + c) heq
    rw[add_asso,add_comm c0 c,←add_asso] at heq
    exact le_addeq.mpr ⟨c0, heq⟩
  . intro h
    have ⟨c0, heq⟩ := le_addeq.mp h
    rw[add_asso,add_comm c c0,←add_asso] at heq
    have heq := add_elim heq
    exact le_addeq.mpr ⟨c0, heq⟩

theorem le_add_right_alt {a b : N} (h : a ≤ b) : a ≤ b + c := by
  have ⟨c0, heq⟩ := le_addeq.mp h
  have heq := congrArg (fun n => n + c) heq
  rw[add_asso] at heq
  exact le_addeq.mpr ⟨c0 + c, heq⟩

theorem le_mul_right_alt {a b : N} (h : a ≤ b) : a ≤ b * S c := by
  have ⟨c0, heq⟩ := le_addeq.mp h
  have heq := congrArg (fun n => n + b * c) heq
  simp at *
  exact le_addeq.mpr ⟨c0 + c * b, heq⟩

theorem le_add_le {a b c d : N} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  have h3 := (le_add b).mp h2
  rw [add_comm c b, add_comm d b] at h3
  exact le_trans ((le_add c).mp h1) h3

def N.blt (a b : N) : Bool :=
  N.ble (S a) b

def N.lt : Prop :=
  blt a b = true

instance : LT N where
  lt := N.lt

theorem succ_lt_succ {a b : N} (h : a < b) : S a < S b := by
  have h : blt a b = true := h
  rw[show blt a b = blt (S a) (S b) from rfl] at h
  exact h

theorem pred_lt_pred {a b : N} (h : S a < S b) : a < b := by
  have h : blt (S a) (S b) = true := h
  rw[show blt (S a) (S b) = blt a b from rfl] at h
  exact h

theorem not_lt_zero {a : N} (h : a < _0) : False := by
  cases h

theorem lt_succ : a < S a :=
  le_refl (S a)

theorem zero_lt_succ : _0 < S a :=
  zero_le a

theorem zero_lt_have_pred {a : N} (h : _0 < a) : ∃ b, S b = a :=
  match a with
  | S b' => ⟨b', Eq.refl (S b')⟩

theorem lt_right_pos {a b : N} (h : a < b) : _0 < b :=
  match b with
  | S b' => zero_lt_succ b'

theorem lt_neq {a b : N} (h : a < b) : a ≠ b := by
  intro h0
  match a, b with
  | S a', S b' => exact (@lt_neq a' b' h) (congrArg P h0)

theorem le_of_lt {a b : N} (h : a < b) : a ≤ b :=
  le_trans (le_succ a) h

theorem le_lte {a b : N} (h : a ≤ b) : a < b ∨ a = b :=
  match a, b with
  | _0, _0 => Or.inr (Eq.refl _0)
  | _0, S b' => Or.inl (zero_le (S b'))
  | S a', S b' => (@le_lte a' b' h).elim Or.inl (fun h => Or.inr (congrArg S h))

theorem lt_arefl {a : N} (h : a < a) : False :=
  @lt_neq a a h (Eq.refl a)

theorem lt_trans {a b c : N} (h1 : a < b) (h2 : b < c) : a < c :=
  match a, b, c with
  | _0, _, S c'      => Eq.refl (blt _0 (S c'))
  | S a', S b', S c' => @lt_trans a' b' c' h1 h2

theorem lt_asymm {a b : N} (h1 : a < b) (h2 : b < a) : False :=
  lt_arefl (@lt_trans a b a h1 h2)

theorem lt_total {a b : N} : a = b ∨ a < b ∨ a > b :=
  match a, b with
  | _0, _0     => Or.inl (Eq.refl _0)
  | _0, S b'   => Or.inr (Or.inl (Eq.refl (blt _0 (S b'))))
  | S a', _0   => Or.inr (Or.inr (Eq.refl (blt _0 (S a'))))
  | S a', S b' => (@lt_total a' b').elim
    (fun heq => Or.inl (congrArg S heq))
    (fun hneq => hneq.elim
      (fun hlt => Or.inr (Or.inl hlt))
      (fun hgt => Or.inr (Or.inr hgt)))

theorem le_ngt {a b : N} (h1 : a ≤ b) (h2 : a > b) : False :=
  (le_lte h1).elim (fun hlt => lt_asymm hlt h2) (fun heq => lt_neq h2 heq.symm)

theorem le_or_gt {a b : N} : a ≤ b ∨ a > b :=
  lt_total.elim
    (fun heq => Or.inl (le_of_eq heq))
    (fun hneq => hneq.elim
      (fun hlt => Or.inl (le_of_lt hlt))
      (fun hgt => Or.inr hgt))

theorem not_between_self_and_succ {a b : N} (h1 : a < b) (h2 : b < S a) : False :=
  le_ngt h1 h2

theorem lt_add {a b : N} : a < b ↔ a + c < b + c := by
  apply Iff.intro
  . intro h
    induction c with
    | _0      => exact h
    | S c' ih => exact ih
  . intro h
    induction c with
    | _0      => exact h
    | S c' ih => exact ih h

theorem lt_add_right {a b : N} (h : a < b) : a < b + c := by
  induction c with
  | _0      => exact h
  | S c' ih => exact lt_trans ih (lt_succ (b + c'))

theorem lt_add_lt {a b c d : N} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  have h3 := (lt_add b).mp h2
  rw[add_comm c b, add_comm d b] at h3
  exact lt_trans ((lt_add c).mp h1) h3

theorem le_add_lt {a b c d : N} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  apply (le_lte h1).elim
  . intro hlt
    exact lt_add_lt hlt h2
  . intro heq
    rw[heq, add_comm b c, add_comm b d]
    exact (lt_add b).mp h2

theorem lt_mul_right {a b : N} (h : a < b) : a < b * S c := by
  induction c with
  | _0      =>
    rw[←mul_one b] at h
    exact h
  | S c' ih =>
    exact lt_add_right b ih

theorem lt_mul_mp {a b : N} (h : a < b) : a * S c < b * S c := by
  induction c with
  | _0 =>
    simp
    exact h
  | S c' ih =>
    have h0 := lt_add_lt ih h
    rw[←mul_succ, ←mul_succ] at h0
    exact h0

theorem lt_mul_mpr {a b : N} (h : a * S c < b * S c) : a < b := by
  apply lt_total.elim
  . intro heq
    cases lt_neq h (congrArg (fun x : N => x * S c) heq)
  . intro hneq
    apply hneq.elim
    . intro hlt
      exact hlt
    . intro hgt
      have h0 := (lt_mul_mp c) hgt
      cases lt_asymm h h0

theorem lt_mul {a b : N} : a < b ↔ a * S c < b * S c :=
  ⟨lt_mul_mp c, lt_mul_mpr c⟩

theorem mul_elim {a b c : N} (h : a * S c = b * S c) : a = b := by
  apply lt_total.elim
  . intro heq
    exact heq
  . intro hneq
    apply hneq.elim
    . intro hlt
      cases lt_neq ((lt_mul c).mp hlt) h
    . intro hgt
      cases lt_neq ((lt_mul c).mp hgt) h.symm

theorem le_mul {a b : N} : a ≤ b ↔ a * S c ≤ b * S c := by
  apply Iff.intro
  . intro h
    apply (le_lte h).elim
    . intro hlt
      exact le_of_lt ((lt_mul c).mp hlt)
    . intro heq
      exact le_of_eq (congrArg (fun x => x * S c) heq)
  . intro h
    apply (le_lte h).elim
    . intro hlt
      exact le_of_lt ((lt_mul c).mpr hlt)
    . intro heq
      exact le_of_eq (mul_elim heq)

theorem lt_mul_lt {a b c d : N} (h1 : a < b) (h2 : c < d) : a * c < b * d := by
  match a, b, c, d with
  | _0, b', c', d' =>
    simp
    have ⟨pd, hdeq⟩ := zero_lt_have_pred (lt_right_pos h2)
    have h0 := lt_mul_right pd h1
    simp[*] at *
    exact h0
  | a', b', _0, d' =>
    simp
    have ⟨pb, hbeq⟩ := zero_lt_have_pred (lt_right_pos h1)
    have h0 := lt_mul_right pb h2
    simp[*] at *
    exact h0
  | S a', S b', S c', S d' =>
    have hab := (lt_mul c').mp h1
    have hcd := (lt_mul b').mp h2
    rw[mul_comm (S c') (S b'), mul_comm (S d') (S b')] at hcd
    exact lt_trans hab hcd

theorem le_mul_le {a b c d : N} (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d := by
  match a, b, c, d with
  | _0, b', c', d' =>
    have h0 := zero_le (b' * d');
    rw[←zero_mul c'] at h0
    exact h0
  | a', b', _0, d' =>
    have h0 := zero_le (b' * d');
    rw[←mul_zero a'] at h0
    exact h0
  | S a', S b', S c', S d' =>
    have hab := (le_mul c').mp h1
    have hcd := (le_mul b').mp h2
    rw[mul_comm (S c') (S b'), mul_comm (S d') (S b')] at hcd
    exact le_trans hab hcd

theorem le_mul_lt {a b c d : N} (h1 : S a ≤ S b) (h2 : c < d) : S a * c < S b * d := by
  apply (le_lte h1).elim
  . intro hlt
    exact lt_mul_lt hlt h2
  . intro heq
    rw[heq, mul_comm (S b) c, mul_comm (S b) d]
    exact (lt_mul b).mp h2

theorem mul_one_iff_one_and_one {a b : N} : a * b = _1 ↔ a = _1 ∧ b = _1 := by
  apply Iff.intro
  . intro h
    apply (@lt_total a _1).elim
    . intro haeq
      simp[haeq] at h
      exact ⟨haeq, h⟩
    . intro haneq
      apply haneq.elim
      . intro halt
        have ha0 := eq_zero_of_le_zero halt
        simp[ha0] at h
        contradiction
      . intro hagt
        apply (@lt_total b _1).elim
        . intro hbeq
          simp[hbeq] at h
          simp[h] at hagt
          contradiction
        . intro hbneq
          apply hbneq.elim
          . intro hblt
            have hb0 := eq_zero_of_le_zero hblt
            simp[hb0] at h
            contradiction
          . intro hbgt
            have hgt := lt_mul_lt hagt hbgt
            simp[h] at hgt
            contradiction
  . intro ⟨_, _⟩
    simp[*]

theorem lt_addeq {a b : N} : a < b ↔ ∃ c, a + S c = b := by
  apply Iff.intro
  . intro h
    have ⟨c, heq⟩ := le_addeq.mp h
    simp at *
    exact ⟨c, heq⟩
  . intro ⟨c, h⟩
    rw[add_succ,←succ_add] at h
    exact le_addeq.mpr ⟨c, h⟩

theorem lt_arefl_alt {a : N} (h : a < a) : False := by
  have ⟨c, heq⟩ := lt_addeq.mp h
  rw[add_comm] at heq
  rw (occs := .pos [2]) [←zero_add a] at heq
  cases add_elim heq

theorem lt_trans_alt {a b c : N} (h1 : a < b) (h2 : b < c) : a < c := by
  have ⟨c1, heq1⟩ := lt_addeq.mp h1
  have ⟨c2, heq2⟩ := lt_addeq.mp h2
  have heq := add_asso ▸ (heq1 ▸ heq2)
  simp at heq
  exact lt_addeq.mpr ⟨S (c1 + c2), heq⟩

theorem lt_asymm_alt {a b : N} (h1 : a < b) (h2 : b < a) : False := by
  have ⟨c1, heq1⟩ := le_addeq.mp h1
  have ⟨c2, heq2⟩ := le_addeq.mp h2
  have hc := heq1 ▸ heq2
  rw[←add_succ, add_asso, add_comm, add_asso, add_succ, ←succ_add, ←add_asso] at hc
  rw (occs := .pos [2]) [←zero_add a] at hc
  cases add_elim hc

theorem lt_add_alt {a b : N} : a < b ↔ a + c < b + c := by
  apply Iff.intro
  . intro h
    have ⟨c0, heq⟩ := lt_addeq.mp h
    have heq := congrArg (fun n => n + c) heq
    rw[add_asso,add_comm (S c0) c,←add_asso] at heq
    exact lt_addeq.mpr ⟨c0, heq⟩
  . intro h
    have ⟨c0, heq⟩ := lt_addeq.mp h
    rw[add_asso,add_comm c (S c0),←add_asso] at heq
    have heq := add_elim heq
    exact lt_addeq.mpr ⟨c0, heq⟩

theorem lt_add_right_alt {a b : N} (h : a < b) : a < b + c := by
  have ⟨c0, heq⟩ := lt_addeq.mp h
  have heq := congrArg (fun n => n + c) heq
  rw[add_asso, succ_add] at heq
  exact lt_addeq.mpr ⟨c0 + c, heq⟩

instance : Pow N N where
  pow a b := _pow a b
    where _pow a b := match b with
      | _0   => _1
      | S b' => _pow a b' * a

theorem pow_unique
  (pow' : N → N → N)
  (h1 : pow' a _0 = _1)
  (h2 : ∀ b, pow' a (S b) = pow' a b * a) :
  pow' a b = a ^ b := by
    induction b with
    | _0      => calc
      pow' a _0 = _1     := by rw[h1]
      _         = a ^ _0 := by rfl
    | S b' ih => calc
      pow' a (S b') = pow' a b' * a := by rw[h2 b']
      _             = a ^ b' * a    := by rw[ih]
      _             = a ^ (S b')    := by rfl

@[simp]
theorem pow_zero : a ^ _0 = _1 := by
  rfl

@[simp]
theorem zero_pow : _0 ^ S a = _0 := by
  rfl

@[simp]
theorem pow_one : a ^ _1 = a := calc
  a ^ _1 = a ^ _0 * a := by rfl
  _      = a          := by simp

@[simp]
theorem square : a ^ _2 = a * a := calc
  a ^ _2 = a ^ _1 * a := by rfl
  _      = a * a      := by simp

@[simp]
theorem cube : a ^ _3 = a * a * a := calc
  a ^ _3 = a ^ _2 * a := by rfl
  _      = a * a * a  := by simp

@[simp]
theorem pow_succ : a ^ S b = a ^ b * a := by
  rfl

@[simp]
theorem one_pow : _1 ^ a = _1 := by
  induction a with
  | _0      => rfl
  | S a' ih => calc
    _1 ^ S a' = _1 ^ a' * _1 := by rfl
    _         = _1           := by simp[ih]

theorem square_of_sum : (a + b) ^ _2 = a ^ _2 + _2 * (a * b) + b ^ _2 := by
  simp

@[simp]
theorem pow_add : a ^ (b + c) = a ^ b * a ^ c := by
  induction c with
  | _0      => simp
  | S c' ih => calc
    a ^ (b + S c') = a ^ (b + c') * a   := by rfl
    _              = a ^ b * a ^ c' * a := by rw[ih]
    _              = a ^ b * a ^ (S c') := by rw[mul_asso]; rfl

@[simp]
theorem pow_mul : (a ^ b) ^ c = a ^ (b * c) := by
  induction c with
  | _0      => simp
  | S c' ih => calc
    (a ^ b) ^ (S c') = (a ^ b) ^ c' * a ^ b := by rfl
    _                = a ^ (b * c') * a ^ b := by rw[ih]
    _                = a ^ (b * S c')       := by simp

@[simp]
theorem mul_pow : (a * b) ^ c = (a ^ c) * (b ^ c) := by
  induction c with
  | _0      => simp
  | S c' ih => calc
    (a * b) ^ (S c') = (a * b) ^ c' * (a * b)        := by rfl
    _                = (a ^ c') * (b ^ c') * (a * b) := by rw[ih]
    _                = (a ^ c') * (a * b) * (b ^ c') := by simp
    _                = (a ^ c' * a) * ((b ^ c') * b) := by rw[←mul_asso,mul_asso,mul_comm b (b ^ c')]
    _                = (a ^ (S c')) * (b ^ (S c'))   := by rfl

theorem lt_pow_mp {a b : N} (h : a < b) : a ^ S c < b ^ S c := by
  induction c with
  | _0 =>
    rw[←pow_one a, ←pow_one b] at h
    exact h
  | S c' ih =>
    have h0 := lt_mul_lt ih h
    rw[←pow_succ, ←pow_succ] at h0
    exact h0

theorem lt_pow_mpr {a b : N} (h : a ^ S c < b ^ S c) : a < b := by
  apply lt_total.elim
  . intro heq
    cases lt_neq h (congrArg (fun x : N => x ^ S c) heq)
  . intro hneq
    apply hneq.elim
    . intro hlt
      exact hlt
    . intro hgt
      have h0 := (lt_pow_mp c) hgt
      cases lt_asymm h h0

theorem lt_pow {a b : N} : a < b ↔ a ^ S c < b ^ S c :=
  ⟨lt_pow_mp c, lt_pow_mpr c⟩

theorem pow_elim {a b c : N} (h : a ^ S c = b ^ S c) : a = b := by
  apply lt_total.elim
  . intro heq
    exact heq
  . intro hneq
    apply hneq.elim
    . intro hlt
      cases lt_neq ((lt_pow c).mp hlt) h
    . intro hgt
      cases lt_neq ((lt_pow c).mp hgt) h.symm

theorem le_pow {a b : N} : a ≤ b ↔ a ^ S c ≤ b ^ S c := by
  apply Iff.intro
  . intro h
    apply (le_lte h).elim
    . intro hlt
      exact le_of_lt ((lt_pow c).mp hlt)
    . intro heq
      exact le_of_eq (congrArg (fun x => x ^ S c) heq)
  . intro h
    apply (le_lte h).elim
    . intro hlt
      exact le_of_lt ((lt_pow c).mpr hlt)
    . intro heq
      exact le_of_eq (pow_elim heq)

theorem pos_pow : _0 < S a ^ b := by
  induction b with
  | _0      => exact zero_lt_succ _0
  | S b' ih => exact lt_mul_right a ih

theorem lt_pow_pos_right {a b : N} (h : a < b) : a < b ^ S c := by
  match a, b with
  | a', S b' =>
    have ⟨p, hpeq⟩ := zero_lt_have_pred (pos_pow b' c)
    have h0 := lt_mul_right p h
    rw[hpeq, mul_comm] at h0
    assumption

theorem le_pow_pos_right {a b : N} (h : a ≤ b) : a ≤ b ^ S c := by
  match a, b with
  | _0, _0 =>
    simp
    apply le_refl
  | a', S b' =>
    have ⟨p, hpeq⟩ := zero_lt_have_pred (pos_pow b' c)
    have h0 := le_mul_right p h
    rw[hpeq, mul_comm] at h0
    assumption

theorem pow_incre_mp {a b : N} (h : _1 < S c ∧ a < b) : S c ^ a < S c ^ b := by
  have ⟨d, heq⟩ := lt_addeq.mp h.right
  have ⟨ca, heq2⟩ := zero_lt_have_pred (pos_pow c a)
  have h0 := (lt_mul ca).mp (lt_pow_pos_right d h.left)
  rw[add_comm] at heq
  rw[one_mul, heq2, ←pow_add, heq] at h0
  exact h0

theorem pow_incre_mpr {a b : N} (h : S c ^ a < S c ^ b) : _1 < S c ∧ a < b := by
  match c with
  | _0 =>
    have h0 := (one_pow a).trans (one_pow b).symm
    cases lt_neq h h0
  | S c' =>
    apply (@lt_total a b).elim
    . intro heq
      have h0 := Eq.refl (S (S c') ^ a)
      rw (occs := .pos [2]) [heq] at h0
      cases lt_neq h h0
    . intro hneq
      apply hneq.elim
      . intro hlt
        have hl := (lt_add _1).mp (zero_lt_succ c')
        rw[zero_add, add_one] at hl
        exact ⟨hl, hlt⟩
      . intro hgt
        have hl := (lt_add _1).mp (zero_lt_succ c')
        rw[zero_add, add_one] at hl
        have h0 := (pow_incre_mp (S c')) ⟨hl, hgt⟩
        cases lt_asymm h h0

theorem pow_incre {a b : N} : _1 < S c ∧ a < b ↔ S c ^ a < S c ^ b :=
  ⟨pow_incre_mp c, pow_incre_mpr c⟩

theorem pow_le {a b : N} (h : a ≤ b) : S c ^ a ≤ S c ^ b := by
  apply (le_lte h).elim
  . intro hlt
    match c with
    | _0   =>
      simp[show S _0 = _1 from rfl]
      apply le_refl
    | S c' =>
      exact le_of_lt ((pow_incre (S c')).mp ⟨succ_lt_succ (zero_lt_succ c'), hlt⟩)
  . intro heq
    simp[*]
    apply le_refl

example : _1 + a * b ≤ (_1 + a) ^ b := by
  induction b with
  | _0      => exact le_of_eq (Eq.refl _1)
  | S b' ih =>
    have h0 := (le_mul a).mp ih
    rw[←one_add a, ←pow_succ, mul_left_dist, mul_right_dist, mul_one, mul_right_dist, mul_one, one_mul, ←add_asso] at h0
    have h1 := le_add_right (a * b' * a) ((le_add a).mp (le_of_eq (Eq.refl (_1 + a * b'))))
    have h2 := le_trans h1 h0
    rw[add_asso, ←mul_succ] at h2
    exact h2

def N.min : N → N → N
| _0, _    => _0
| _, _0    => _0
| S a, S b => S (min a b)

def N.max : N → N → N
| _0, b    => b
| a, _0    => a
| S a, S b => S (max a b)

@[simp]
theorem zero_min : min _0 a = _0 := by
  rfl

@[simp]
theorem min_zero : min a _0 = _0 := by
  match a with
  | _0   => rfl
  | S a' => rfl

@[simp]
theorem zero_max : max _0 a = a := by
  rfl

@[simp]
theorem max_zero : max a _0 = a := by
  match a with
  | _0   => rfl
  | S a' => rfl

@[simp]
theorem succ_min_succ {a b : N} : min (S a) (S b) = S (min a b) := by
  rfl

@[simp]
theorem succ_max_succ {a b : N} : max (S a) (S b) = S (max a b) := by
  rfl

@[simp]
theorem min_idem : min a a = a := by
  induction a with
  | _0      => simp
  | S a' ih => exact congrArg S ih

@[simp]
theorem max_idem : max a a = a := by
  induction a with
  | _0      => simp
  | S a' ih => exact congrArg S ih

@[simp]
theorem min_comm {a b : N} : min a b = min b a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => exact (congrArg S min_comm)

@[simp]
theorem max_comm {a b : N} : max a b = max b a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => exact (congrArg S max_comm)

@[simp]
theorem min_asso {a b c : N} : min (min a b) c = min a (min b c) := by
  match a, b, c with
  | _0, _, _         => simp
  | _, _0, _         => simp
  | _, _, _0         => simp
  | S a', S b', S c' => exact (congrArg S min_asso)

@[simp]
theorem max_asso {a b c : N} : max (max a b) c = max a (max b c) := by
  match a, b, c with
  | _0, _, _         => simp
  | _, _0, _         => simp
  | _, _, _0         => simp
  | S a', S b', S c' => exact (congrArg S max_asso)

theorem min_min_min_comm : min (min a b) (min c d) = min (min a c) (min b d) := calc
  min (min a b) (min c d) = min (min a (min b c)) d := by repeat rw[min_asso]
  _                       = min (min a (min c b)) d := by rw[@min_comm b c]
  _                       = min (min a c) (min b d) := by repeat rw[min_asso]

theorem max_max_max_comm : max (max a b) (max c d) = max (max a c) (max b d) := calc
  max (max a b) (max c d) = max (max a (max b c)) d := by repeat rw[max_asso]
  _                       = max (max a (max c b)) d := by rw[@max_comm b c]
  _                       = max (max a c) (max b d) := by repeat rw[max_asso]

@[simp]
theorem min_max_abso {a b : N} : min a (max a b) = a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => exact (congrArg S min_max_abso)

@[simp]
theorem max_min_abso {a b : N} : max a (min a b) = a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => exact (congrArg S max_min_abso)

theorem min_idem_alt {a b : N} : min a a = a := calc
  min a a = min a (max a (min a b)) := by rw[max_min_abso]
  _       = a                       := by rw[min_max_abso]

theorem max_idem_alt {a b : N} : max a a = a := calc
  max a a = max a (min a (max a b)) := by rw[min_max_abso]
  _       = a                       := by rw[max_min_abso]

theorem min_max_dist {a b c : N} : min a (max b c) = max (min a b) (min a c) := by
  match a, b, c with
  | _0, _, _         => simp
  | _, _0, _         => simp
  | _, _, _0         => simp
  | S a', S b', S c' => simp; exact min_max_dist

theorem max_min_dist {a b c : N} : max a (min b c) = min (max a b) (max a c) := by
  match a, b, c with
  | _0, _, _         => simp
  | _, _0, _         => simp
  | _, _, _0         => simp
  | S a', S b', S c' => simp; exact max_min_dist

@[simp]
theorem min_add_left {a b : N} : min (a + b) a = a := by
  induction a with
  | _0      => simp
  | S a' ih =>
    simp at *
    exact ih

@[simp]
theorem min_add_right {a b : N} : min a (a + b) = a :=
  min_comm ▸ min_add_left

@[simp]
theorem add_min_add_left {a b c : N} : min (c + a) (c + b) = c + min a b := by
  induction c with
  | _0      => simp
  | S c' ih => simp[-add_comm]; exact ih

@[simp]
theorem add_min_add_right {a b c : N} : min (a + c) (b + c) = min a b + c := by
  rw[add_comm a, add_comm b, add_comm (min a b)]
  exact add_min_add_left

@[simp]
theorem max_add_left {a b : N} : max (a + b) a = a + b := by
  induction a with
  | _0      => simp
  | S a' ih =>
    simp at *
    exact ih

@[simp]
theorem max_add_right {a b : N} : max a (a + b) = a + b :=
  max_comm ▸ max_add_left

@[simp]
theorem add_max_add_left {a b c : N} : max (c + a) (c + b) = c + max a b := by
  induction c with
  | _0      => simp
  | S c' ih => simp[-add_comm]; exact ih

@[simp]
theorem add_max_add_right {a b c : N} : max (a + c) (b + c) =  max a b + c := by
  rw[add_comm a, add_comm b, add_comm (max a b)]
  exact add_max_add_left

theorem min_eq_left {a b : N} (h : a ≤ b) : min a b = a :=
  match a, b with
  | _0, _    => by simp
  | S _, S _ => congrArg S (min_eq_left h)

theorem min_eq_right {a b : N} (h : b ≤ a) : min a b = b :=
  min_comm ▸ min_eq_left h

theorem max_eq_left {a b : N} (h : b ≤ a) : max a b = a :=
  match a, b with
  | a', _0   => by simp
  | S _, S _ => congrArg S (max_eq_left h)

theorem max_eq_right {a b : N} (h : a ≤ b) : max a b = b :=
  max_comm ▸ max_eq_left h

theorem min_le_left {a b : N} : min a b ≤ a := by
  apply (@le_total a b).elim
  . intro h
    rw[min_eq_left h]
    apply le_refl
  . intro h
    rw[min_eq_right h]
    assumption

theorem min_le_right {a b : N} : min a b ≤ b :=
  min_comm ▸ min_le_left

theorem le_max_left {a b : N} : a ≤ max a b := by
  apply (@le_total a b).elim
  . intro h
    rw[max_eq_right h]
    assumption
  . intro h
    rw[max_eq_left h]
    apply le_refl

theorem le_max_right {a b : N} : b ≤ max a b :=
  max_comm ▸ le_max_left

theorem min_le_max : min a b ≤ max a b :=
  le_trans min_le_left le_max_left

theorem le_min_of_le_of_le {a b c : N} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ min a b := by
  apply (@le_total a b).elim
  . intro h
    rwa[min_eq_left h]
  . intro h
    rwa[min_eq_right h]

theorem le_min {a b c : N} : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
  ⟨ fun h => ⟨le_trans h min_le_left, le_trans h min_le_right⟩,
    fun ⟨h1, h2⟩ => le_min_of_le_of_le h1 h2⟩

theorem lt_min {a b c : N} : c < min a b ↔ c < a ∧ c < b :=
  le_min

theorem max_le_of_le_of_le {a b c : N} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c := by
  apply (@le_total a b).elim
  . intro h
    rwa[max_eq_right h]
  . intro h
    rwa[max_eq_left h]

theorem max_le {a b c : N} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨ fun h => ⟨le_trans le_max_left h, le_trans le_max_right h⟩,
    fun ⟨h1, h2⟩ => max_le_of_le_of_le h1 h2⟩

theorem max_lt {a b c : N} : max a b < c ↔ a < c ∧ b < c := by
  match c with
  | _0  =>
    apply Iff.intro
    . intro _
      contradiction
    . intro ⟨_, _⟩
      contradiction
  | S _ => exact max_le

theorem min_le_min {a b c d : N} (h1 : a ≤ c) (h2 : b ≤ d) : min a b ≤ min c d := by
  apply (@le_total c d).elim
  . intro h
    rw[min_eq_left h]
    exact le_trans min_le_left h1
  . intro h
    rw[min_eq_right h]
    exact le_trans min_le_right h2

theorem max_le_max {a b c d : N} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ max c d := by
  apply (@le_total a b).elim
  . intro h
    rw[max_eq_right h]
    exact le_trans h2 le_max_right
  . intro h
    rw[max_eq_left h]
    exact le_trans h1 le_max_left

theorem mul_min_mul_left {a b c : N} : c * min a b = min (c * a) (c * b) := by
  apply (le_lte (zero_le c)).elim
  . intro hlt
    apply (@le_total a b).elim
    . intro hle
      have ⟨pc, hp⟩ := zero_lt_have_pred hlt
      have h1 := min_eq_left hle
      have h2 := min_eq_left ((le_mul pc).mp hle)
      simp[*] at h2
      rw[mul_comm a c, mul_comm b c] at h2
      exact (congrArg (fun x => c * x) h1).trans h2.symm
    . intro hge
      have ⟨pc, hp⟩ := zero_lt_have_pred hlt
      have h1 := min_eq_left hge
      have h2 := min_eq_left ((le_mul pc).mp hge)
      rw[min_comm] at h1
      simp[*] at h2
      rw[mul_comm a c, mul_comm b c] at h2
      exact (congrArg (fun x => c * x) h1).trans h2.symm
  . intro heq
    simp[←heq]

theorem mul_min_mul_right {a b c : N} : min a b * c = min (a * c) (b * c) := by
  rw[mul_comm, mul_comm a c, mul_comm b c]
  exact mul_min_mul_left

theorem mul_max_mul_left {a b c : N} : c * max a b = max (c * a) (c * b) := by
  apply (le_lte (zero_le c)).elim
  . intro hlt
    apply (@le_total a b).elim
    . intro hle
      have ⟨pc, hp⟩ := zero_lt_have_pred hlt
      have h1 := max_eq_left hle
      have h2 := max_eq_left ((le_mul pc).mp hle)
      rw[max_comm] at h1
      simp[*] at h2
      rw[mul_comm a c, mul_comm b c] at h2
      exact (congrArg (fun x => c * x) h1).trans h2.symm
    . intro hge
      have ⟨pc, hp⟩ := zero_lt_have_pred hlt
      have h1 := max_eq_left hge
      have h2 := max_eq_left ((le_mul pc).mp hge)
      simp[*] at h2
      rw[mul_comm a c, mul_comm b c] at h2
      exact (congrArg (fun x => c * x) h1).trans h2.symm
  . intro heq
    simp[←heq]

theorem mul_max_mul_right {a b c : N} : max a b * c = max (a * c) (b * c) := by
  rw[mul_comm, mul_comm a c, mul_comm b c]
  exact mul_max_mul_left

theorem comm_fun_min_max {a b : N} {f : N → N → N}
  (h : ∀ a, ∀ b, f a b = f b a) :
  f (min a b) (max a b) = f a b := by
  apply le_total.elim
  . intro hle
    rw[min_eq_left hle, max_eq_right hle]
  . intro hge
    rw[min_eq_right hge, max_eq_left hge, h a b]

@[simp]
theorem min_add_max {a b : N} : min a b + max a b = a + b :=
  comm_fun_min_max add_comm

@[simp]
theorem min_mul_max {a b : N} : min a b * max a b = a * b :=
  comm_fun_min_max mul_comm

instance : Dvd N where
  dvd a b := ∃ c, a * c = b

theorem dvd_refl : a ∣ a :=
  ⟨_1, by simp⟩

theorem dvd_zero : a ∣ _0 :=
  ⟨_0, by simp⟩

theorem one_dvd : _1 ∣ a :=
  ⟨a, by simp⟩

theorem eq_zero_of_zero_dvd {a : N} (h : _0 ∣ a) : a = _0 := by
  have ⟨c, heq⟩ := h
  simp at *
  exact heq.symm

theorem pos_of_dvd_of_pos {a b : N} (h1 : a ∣ b) (h2 : _0 < b) : _0 < a := by
  match a with
  | _0   => rw[eq_zero_of_zero_dvd h1] at h2; cases h2
  | S a' => exact zero_lt_succ a'

theorem eq_one_of_dvd_one {a : N} (h : a ∣ _1) : a = _1 := by
  have ⟨c, heq⟩ := h
  exact (mul_one_iff_one_and_one.mp heq).left

theorem dvd_trans {a b c : N} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  have ⟨c1, heq1⟩ := h1
  have ⟨c2, heq2⟩ := h2
  ⟨c1 * c2, mul_asso ▸ (heq1 ▸ heq2)⟩

theorem le_of_dvd {a b : N} (h0 : _0 < b) (h : a ∣ b) : a ≤ b := by
  have ⟨c, heq⟩ := h
  apply (le_lte (zero_le c)).elim
  . intro hcp
    have ⟨pc, hp⟩ := zero_lt_have_pred hcp
    rw[←hp, mul_succ, add_comm] at heq
    exact le_addeq.mpr ⟨a * pc, heq⟩
  . intro hcz
    simp[←hcz] at heq
    cases lt_neq h0 heq

theorem dvd_antisymm {a b : N} (h1 : a ∣ b) (h2 : b ∣ a) : a = b :=
  match a, b with
  | _, _0 => eq_zero_of_zero_dvd h2
  | _0, _ => (eq_zero_of_zero_dvd h1).symm
  | S a', S b' => le_antisymm (le_of_dvd (zero_lt_succ b') h1) (le_of_dvd (zero_lt_succ a') h2)

theorem dvd_add {a b c : N} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c :=
  have ⟨c1, heq1⟩ := h1
  have ⟨c2, heq2⟩ := h2
  ⟨c1 + c2, by simp[*]⟩

theorem dvd_mul {a b : N} (h : a ∣ b) : a ∣ b * c := by
  have ⟨d, heq⟩ := h
  have heq := congrArg (fun x => x * c) heq
  rw[mul_asso] at heq
  exact ⟨d * c, heq⟩

theorem dvd_mul_elim {a b c : N} (h : a * S c ∣ b * S c) : a ∣ b := by
  have ⟨d, heq⟩ := h
  rw[mul_asso, mul_comm (S c) d, ←mul_asso] at heq
  exact ⟨d, mul_elim heq⟩

theorem dvd_mul_add_mul {a b c m n : N} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ m * b + n * c := by
  have h := dvd_add (dvd_mul m h1) (dvd_mul n h2)
  rw[mul_comm m b, mul_comm n c]
  exact h

theorem euclidean (n q : N) : ∃ m, ∃ r, r < (S q) ∧ n = m * (S q) + r := by
  induction n with
  | _0 =>
    exact ⟨_0, _0, zero_lt_succ (S q), by simp⟩
  | S n' ih =>
    have ⟨m, r, hlt, heq⟩ := ih
    apply (@lt_total (S r) (S q)).elim
    . intro hreq
      have heq := congrArg S heq
      rw[←add_succ, hreq, ←succ_mul] at heq
      exact ⟨S m, _0, zero_lt_succ (S q), heq⟩
    . intro hrneq
      apply hrneq.elim
      . intro hrlt
        have heq := congrArg S heq
        rw[←add_succ] at heq
        exact ⟨m, S r, hrlt, heq⟩
      . intro hrgt
        cases le_ngt hlt hrgt

def abssub : N → N → N
| _0, b => b
| a, _0 => a
| S a, S b => abssub a b

@[simp]
theorem zero_abssub : abssub _0 a = a := by
  rfl

@[simp]
theorem abssub_zero : abssub a _0 = a := by
  match a with
  | _0   => rfl
  | S a' => rfl

@[simp]
theorem succ_abssub_succ {a b : N} : abssub (S a) (S b) = abssub a b := by
  rfl

@[simp]
theorem abssub_self : abssub a a = _0 := by
  induction a with
  | _0      => rfl
  | S a' ih => simp; exact ih

theorem abssub_eq_zero {a b : N} : abssub a b = _0 ↔ a = b := by
  apply Iff.intro
  . intro h
    match a, b with
    | _0, _0     => simp
    | S a', S b' => simp at *; exact abssub_eq_zero.mp h
  . intro h
    match a, b with
    | _0, _0     => simp
    | S a', S b' => simp at *; exact abssub_eq_zero.mpr h

theorem abssub_add_cancel {a b : N} (h : a ≥ b) : (abssub a b) + b = a := by
  match a, b with
  | _, _0      => simp
  | S a', S b' => simp[-add_comm, abssub_add_cancel (pred_le_pred h)]

@[simp]
theorem add_abssub_add_right {a b c : N} : abssub (a + c) (b + c) = abssub a b := by
  induction c with
  | _0      => rfl
  | S c' ih => simp; exact ih

@[simp]
theorem add_abssub_add_left {a b c : N} : abssub (c + a) (c + b) = abssub a b := by
  rw[add_comm c a, add_comm c b]
  exact add_abssub_add_right

@[simp]
theorem abssub_comm {a b : N} : abssub a b = abssub b a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => exact @abssub_comm a' b'

theorem abssub_le_max {a b : N} : abssub a b ≤ max a b := by
  match a, b with
  | _0, _      => simp; apply le_refl
  | _, _0      => simp; apply le_refl
  | S a', S b' => simp; exact le_trans abssub_le_max (le_succ (max a' b'))

theorem abssub_le_of_le_of_le {a b c : N} (h1 : a ≤ c) (h2 : b ≤ c) : abssub a b ≤ c :=
  le_trans abssub_le_max (max_le.mpr ⟨h1, h2⟩)

theorem abssub_lt_of_lt_of_lt {a b c : N} (h1 : a < c) (h2 : b < c) : abssub a b < c :=
  le_trans abssub_le_max (max_lt.mpr ⟨h1, h2⟩)

theorem abssub_eq_of_eq_of_add {a b c d : N} (h : a + c = b + d) : abssub a b = abssub c d := by
  match a, b, c, d with
  | _0, _0, _, _ => simp at *; rw[h]; simp
  | _, _, _0, _0 => simp at *; rw[h]; simp
  | _0, _, _, _0 => simp at *; exact h.symm
  | _, _0, _0, _ => simp at *; exact h
  | a', _0, S c', S d' =>
    simp at *
    rw[←zero_add d'] at h
    have h0 := (@abssub_eq_of_eq_of_add a' _0 c' d') h
    simp at *
    exact h0
  | _0, b', S c', S d' =>
    simp at *;
    rw[←zero_add c'] at h
    have h0 := (@abssub_eq_of_eq_of_add _0 b' c' d') h
    simp at *;
    exact h0
  | S a', S b', c', _0 =>
    simp at *
    have h0 := (@abssub_eq_of_eq_of_add a' b' c' _0) h
    simp at *
    exact h0
  | S a', S b', _0, d' =>
    simp at *
    have h0 := (@abssub_eq_of_eq_of_add a' b' _0 d') h
    simp at *
    exact h0
  | S a', S b', S c', S d' =>
    simp at *
    exact abssub_eq_of_eq_of_add h

theorem abssub_add_of_le_of_le {a b c d : N} (h1 : a ≤ b) (h2 : c ≤ d) : abssub a b + abssub c d = abssub (a + c) (b + d) := by
  match a, b, c, d with
  | _0, _, _0, _ => simp
  | _0, b', S c', S d' =>
    simp at *
    have h0 := (@abssub_add_of_le_of_le _0 b' c' d') h1 h2
    simp at *
    exact h0
  | S a', S b', _0, d' =>
    simp at *
    have h0 := (@abssub_add_of_le_of_le a' b' _0 d') h1 h2
    simp at *
    exact h0
  | S a', S b', S c', S d' =>
    simp at *
    exact abssub_add_of_le_of_le h1 h2

theorem mul_abssub_mul_left {a b c : N} : c * abssub a b = abssub (c * a) (c * b) := by
  match a, b, c with
  | _0, _, _ => simp
  | _, _0, _ => simp
  | _, _, _0 => simp
  | a', b', S c' =>
    simp at *
    rw[@mul_abssub_mul_left a' b' c']
    apply (le_lte (zero_le c')).elim
    . intro hcp
      have ⟨pc, hp⟩ := zero_lt_have_pred hcp
      apply (@le_total a' b').elim
      repeat
      . intro h
        have h0 := abssub_add_of_le_of_le h ((le_mul pc).mp h)
        simp[*] at *
        exact h0
    . intro hcz
      simp[←hcz]

theorem mul_abssub_mul_right {a b c : N} : abssub a b * c = abssub (a * c) (b * c) := by
  rw[mul_comm, mul_comm a c, mul_comm b c]
  exact mul_abssub_mul_left

theorem euclidean_unique (n q m1 r1 m2 r2: N)
  (h1 : r1 < (S q) ∧ n = m1 * (S q) + r1)
  (h2 : r2 < (S q) ∧ n = m2 * (S q) + r2) :
  m1 = m2 ∧ r1 = r2 := by
  have ⟨hrlt1, heq1⟩ := h1
  have ⟨hrlt2, heq2⟩ := h2
  have hrlt := abssub_lt_of_lt_of_lt hrlt1 hrlt2
  have hn := heq1.symm.trans heq2
  have hsub := abssub_eq_of_eq_of_add hn
  rw[←mul_abssub_mul_right,mul_comm] at hsub
  have hdvd : S q ∣ abssub r1 r2 := ⟨abssub m1 m2, hsub⟩
  apply (le_lte (zero_le (abssub r1 r2))).elim
  . intro hlt
    have hrge := le_of_dvd hlt hdvd
    cases le_ngt hrge hrlt
  . intro heq
    have hr := abssub_eq_zero.mp heq.symm
    exact ⟨mul_elim (add_elim (hr ▸ hn)), hr⟩

theorem abssub_ge_one_of_neq {a b : N} (h : a ≠ b) : abssub a b ≥ _1 := by
  match a, b with
  | _0, S b'   => exact succ_le_succ (zero_le b')
  | S a', _0   => exact succ_le_succ (zero_le a')
  | S a', S b' => simp at *; exact @abssub_ge_one_of_neq a' b' h

theorem euclidean_unique_alt (n q m1 r1 m2 r2: N)
  (h1 : r1 < (S q) ∧ n = m1 * (S q) + r1)
  (h2 : r2 < (S q) ∧ n = m2 * (S q) + r2) :
  m1 = m2 ∧ r1 = r2 := by
  have ⟨hrlt1, heq1⟩ := h1
  have ⟨hrlt2, heq2⟩ := h2
  have hrlt := abssub_lt_of_lt_of_lt hrlt1 hrlt2
  have hn := heq1.symm.trans heq2
  by_cases h : r1 = r2
  . exact ⟨mul_elim (add_elim (h ▸ hn)), h⟩
  . by_cases hm : m1 = m2
    . have hn := hm ▸ hn
      rw[add_comm _ r1, add_comm _ r2] at hn
      have hn := add_elim hn
      contradiction
    . have hsub := abssub_eq_of_eq_of_add hn
      have hsubm := (le_mul q).mp (abssub_ge_one_of_neq hm)
      rw[mul_abssub_mul_right, hsub] at hsubm
      have hsubr := abssub_lt_of_lt_of_lt hrlt1 hrlt2
      simp at *
      cases le_ngt hsubm hsubr

theorem square_abssub_square (a b : N) : abssub (a ^ _2) (b ^ _2) = (a + b) * (abssub a b) := by
  match a, b with
  | _0, _ => simp
  | _, _0 => simp
  | S a', S b' =>
    rw[←add_one, ←add_one, square_of_sum a' _1, square_of_sum b' _1, one_pow, mul_one, mul_one]
    rw[add_abssub_add_right, add_abssub_add_right]
    rw[←add_asso, @add_asso a' _1 b', add_comm _1 b', add_asso, add_asso]
    have h2 : _1 + _1 = _2 := by rfl
    rw[h2, ←add_asso, mul_right_dist]
    have h1 : _2 = S _1 := by rfl
    rw[mul_comm _2 a', mul_comm _2 b']
    apply (@le_total a' b').elim
    . intro h
      have h3 := abssub_add_of_le_of_le ((le_pow _1).mp h) ((le_mul _1).mp h)
      rw[←h1] at h3
      rw[←h3, square_abssub_square a' b', ←mul_abssub_mul_right, mul_comm _2]
    . intro h
      have h3 := abssub_add_of_le_of_le ((le_pow _1).mp h) ((le_mul _1).mp h)
      rw[←h1, @abssub_comm (b' ^ _2), @abssub_comm (b' * _2), @abssub_comm (b' ^ _2 + b' * _2)] at h3
      rw[←h3, square_abssub_square a' b', ←mul_abssub_mul_right, mul_comm _2]

def monus (a b : N) : N :=
  match b with
  | _0   => a
  | S b' => P (monus a b')

@[simp]
theorem monus_zero : monus a _0 = a := by
  rfl

theorem monus_succ : monus a (S b) = P (monus a b) := by
  rfl

@[simp]
theorem zero_monus : monus _0 a = _0 := by
  induction a with
  | _0      => rfl
  | S a' ih => rw[monus_succ, ih]; rfl

@[simp]
theorem succ_monus_succ : monus (S a) (S b) = monus a b := by
  induction b with
  | _0      => rfl
  | S b' ih => rw[monus_succ, ih]; rfl

@[simp]
theorem monus_self : monus a a = _0 := by
  induction a with
  | _0      => rfl
  | S a' ih => simp[ih]

theorem add_monus (a b : N) : a + monus b a = b + monus a b := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => simp[add_monus a' b']

theorem monus_monus : monus (monus a b) c = monus a (b + c) := by
  induction c with
  | _0      => rfl
  | S c' ih => rw[monus_succ, add_succ, monus_succ, ih]

theorem abssub_of_monus (a b : N) : abssub a b = monus a b + monus b a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => simp[abssub_of_monus a' b']

theorem max_of_monus (a b : N) : max a b = a + monus b a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => simp[max_of_monus a' b']

theorem monus_eq_zero {a b : N} : a ≤ b ↔ monus a b = _0 := by
  apply Iff.intro
  . intro h
    match a, b with
    | _0, _      => simp
    | S a', S b' => simp[monus_eq_zero.mp (pred_le_pred h)]
  . intro h
    match a, b with
    | _0, _      => apply zero_le
    | S a', S b' => simp at h; apply succ_le_succ; exact monus_eq_zero.mpr h

theorem monus_gt_zero {a b : N} : a > b ↔ monus a b > _0 := by
  apply Iff.intro
  . intro h
    match a, b with
    | _, _0      => simp[h]
    | S a', S b' => simp[monus_gt_zero.mp (pred_lt_pred h)]
  . intro h
    match a, b with
    | _0, _      => simp at h; contradiction
    | _, _0      => simp at h; exact h
    | S a', S b' => simp at h; apply succ_lt_succ; exact monus_gt_zero.mpr h

theorem monus_add_cancel {a b : N} (h : a ≥ b) : (monus a b) + b = a := by
  match a, b with
  | _, _0      => simp
  | S a', S b' => simp[-add_comm, monus_add_cancel (pred_le_pred h)]

theorem succ_monus {a b : N} (h : a ≥ b) : monus (S a) b = S (monus a b) := by
  match a, b with
  | _, _0      => simp
  | S a', S b' => simp[succ_monus (pred_le_pred h)]

theorem monus_le_left (a b : N) : monus a b ≤ a := by
  match a, b with
  | _0, _      => simp; apply zero_le
  | _, _0      => simp; apply le_refl
  | S a', S b' => simp; exact le_trans (monus_le_left a' b') (le_succ a')

theorem min_of_monus (a b : N) : min a b = monus a (monus a b) := by
  apply le_total.elim
  . intro hle
    rw[min_eq_left hle, monus_eq_zero.mp hle, monus_zero]
  . intro hge
    let rec hb {a b : N} (h : a ≥ b) : monus a (monus a b) = b := by
      match a, b with
      | _, _0      => simp
      | S a', S b' =>
        simp
        simp[succ_monus (monus_le_left a' b'), hb (pred_le_pred h)]
    rw[min_eq_right hge, hb hge]

@[simp]
theorem add_monus_add_right {a b c : N} : monus (a + c) (b + c) = monus a b := by
  induction c with
  | _0      => rfl
  | S c' ih => simp; exact ih

@[simp]
theorem add_monus_add_left {a b c : N} : monus (c + a) (c + b) = monus a b := by
  rw[add_comm c a, add_comm c b]
  exact add_monus_add_right

theorem monus_add_of_ge_of_ge {a b c d : N} (h1 : a ≥ b) (h2 : c ≥ d) : monus a b + monus c d = monus (a + c) (b + d) := by
  match a, b, c, d with
  | _, _0, _, _0 => simp
  | a', _0, S c', S d' =>
    simp at *
    have h0 := (@monus_add_of_ge_of_ge a' _0 c' d') h1 h2
    simp at *
    exact h0
  | S a', S b', c', _0 =>
    simp at *
    have h0 := (@monus_add_of_ge_of_ge a' b' c' _0) h1 h2
    simp at *
    exact h0
  | S a', S b', S c', S d' =>
    simp at *
    exact monus_add_of_ge_of_ge h1 h2

theorem mul_monus_mul_left {a b c : N} : c * monus a b = monus (c * a) (c * b) := by
  match a, b, c with
  | _0, _, _ => simp
  | _, _0, _ => simp
  | _, _, _0 => simp
  | a', b', S c' =>
    apply (le_lte (zero_le c')).elim
    . intro hcp
      apply (@le_total a' b').elim
      . intro h
        rw[monus_eq_zero.mp h, ←mul_comm a', ←mul_comm b', monus_eq_zero.mp ((le_mul c').mp h)]
        simp
      . intro h
        simp at *
        rw[@mul_monus_mul_left a' b' c']
        have ⟨pc, hp⟩ := zero_lt_have_pred hcp
        have h0 := monus_add_of_ge_of_ge h ((le_mul pc).mp h)
        simp[*] at *
        exact h0
    . intro hcz
      simp[←hcz]

theorem mul_monus_mul_right {a b c : N} : monus a b * c = monus (a * c) (b * c) := by
  rw[mul_comm, mul_comm a c, mul_comm b c]
  exact mul_monus_mul_left

theorem square_monus_square (a b : N) : monus (a ^ _2) (b ^ _2) = (a + b) * (monus a b) := by
  apply (@le_total a b).elim
  . intro hle
    rw[show _2 = S _1 from rfl, monus_eq_zero.mp hle, monus_eq_zero.mp ((le_pow _1).mp hle)]
    simp
  . intro hge
    match a, b with
    | _, _0      => simp
    | S a', S b' =>
      rw[←add_one, ←add_one, square_of_sum a' _1, square_of_sum b' _1, one_pow, mul_one, mul_one]
      rw[add_monus_add_right, add_monus_add_right]
      rw[←add_asso, @add_asso a' _1 b', add_comm _1 b', add_asso, add_asso]
      rw[show _1 + _1 = _2 from rfl, ←add_asso, mul_right_dist]
      rw[mul_comm _2 a', mul_comm _2 b']
      have hge := pred_le_pred hge
      have h := monus_add_of_ge_of_ge ((le_pow _1).mp hge) ((le_mul _1).mp hge)
      rw[show S _1 = _2 from rfl] at h
      rw[←h, square_monus_square a' b', ←mul_monus_mul_right, mul_comm _2]

def N.H : N → Nat
| _0  => 0
| S a => (H a).succ

@[simp]
theorem iso_zero : H _0 = 0 := by
  rfl

@[simp]
theorem iso_succ : H (S a) = (H a).succ := by
  rfl

theorem H_unique
  (f : N → Nat)
  (h1 : f _0 = 0)
  (h2 : ∀ a, f (S a) = (f a).succ) :
  f a = H a := by
  induction a with
  | _0      => simp[h1]
  | S a' ih => simp[h2 a', ih]

theorem iso_eq {a b : N} : a = b ↔ H a = H b := by
  apply Iff.intro
  . intro h
    simp[h]
  . intro h
    match a, b with
    | _0, _0     =>
      rfl
    | S a', S b' =>
      simp at h
      simp[iso_eq.mpr h]

def N.unH : Nat → N
| 0  => _0
| Nat.succ a => S (unH a)

@[simp]
theorem unH_zero : unH 0 = _0 := by
  rfl

@[simp]
theorem unH_succ (a : Nat) : unH a.succ = S (unH a) := by
  rfl

theorem unH_eq {a b : Nat} : a = b ↔ unH a = unH b := by
  apply Iff.intro
  . intro h
    simp[h]
  . intro h
    match a, b with
    | 0, 0 =>
      rfl
    | Nat.succ a', Nat.succ b' =>
      simp at h
      simp[unH_eq.mpr h]

@[simp]
theorem unHH : unH (H a) = a := by
  induction a with
  | _0      => rfl
  | S a' ih => simp[ih]

@[simp]
theorem HunH (a : Nat) : H (unH a) = a := by
  induction a with
  | zero       => rfl
  | succ a' ih => simp[ih]

@[simp]
theorem iso_one : H _1 = 1 := by
  rfl

theorem iso_pred : H (P a) = (H a).pred := by
  induction a with
  | _0      => rfl
  | S a' ih => simp

theorem iso_add : H (a + b) = H a + H b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    H (a + S b') = H (S (a + b'))    := by rfl
    _            = (H (a + b')).succ := by rfl
    _            = (H a + H b').succ := by rw[ih]
    _            = H a + H (S b')    := by rfl

theorem iso_mul : H (a * b) = H a * H b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    H (a * S b') = H (a * b' + a)   := by rfl
    _            = H (a * b') + H a := by rw[iso_add]
    _            = H a * H b' + H a := by rw[ih]
    _            = H a * H (S b')   := by rfl

theorem iso_pow : H (a ^ b) = H a ^ H b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    H (a ^ S b') = H (a ^ b' * a)   := by rfl
    _            = H (a ^ b') * H a := by rw[iso_mul]
    _            = H a ^ H b' * H a := by rw[ih]
    _            = H a ^ H (S b')   := by rfl

theorem iso_min {a b : N} : H (min a b) = min (H a) (H b) := by
  match a, b with
  | _0, _ => simp
  | _, _0 => simp
  | S a', S b' =>
    simp[iso_min] at *

theorem iso_max {a b : N} : H (max a b) = max (H a) (H b) := by
  match a, b with
  | _0, _ => simp
  | _, _0 => simp
  | S a', S b' =>
    simp[iso_max] at *

theorem iso_monus {a b : N} : H (monus a b) = (H a) - (H b) := by
  induction b with
  | _0      => rfl
  | S b' ih => rw[monus_succ, iso_succ, Nat.sub_succ, iso_pred, ih]

-- from Mathlib.Data.Nat.Dist
def Nat.dist (n m : Nat) :=
  n - m + (m - n)

theorem iso_abssub {a b : N} : H (abssub a b) = Nat.dist (H a) (H b) := by
  match a, b with
  | _0, _      => unfold Nat.dist; simp
  | _, _0      => unfold Nat.dist; simp
  | S a', S b' => simp[iso_abssub]; unfold Nat.dist; simp

theorem iso_le {a b : N} : a ≤ b ↔ H a ≤ H b := by
  apply Iff.intro
  . intro h
    match a, b with
    | _0, b'     =>
      exact Nat.zero_le (H b')
    | S a', S b' =>
      exact Nat.succ_le_succ (iso_le.mp h)
  . intro h
    match a, b with
    | _0, b'     =>
      exact zero_le b'
    | S a', S b' =>
      simp at h
      exact succ_le_succ (iso_le.mpr h)

theorem iso_dvd {a b : N} : a ∣ b ↔ H a ∣ H b := by
  apply Iff.intro
  . intro ⟨c, heq⟩
    have heq' := (congrArg H heq).symm
    rw[iso_mul] at heq'
    exact ⟨H c, heq'⟩
  . intro ⟨c, heq⟩
    rw[←HunH c, ←iso_mul] at heq
    have heq' := (congrArg unH heq).symm
    rw[unHH, unHH] at heq'
    exact ⟨unH c, heq'⟩
