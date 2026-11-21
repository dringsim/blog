---
title: 自然数
published: 2026-11-21
description: 让我们从头开始。
tags: [数, Lean]
category: 数学
draft: false
---

# 皮亚诺算术

自然数可以用朱塞佩·皮亚诺（Giuseppe Peano）提出的5条公理来定义：

1. （PA1）$0$是一个自然数。
2. （PA2）如果$n$是自然数，那么其有且只有一个后继$n^+$，$n^+$也是自然数。
3. （PA3）$0$不是任何自然数的后继，即对任意自然数$n$都有$n^+ \ne 0$。
4. （PA4）不同的自然数有不同的后继，即对任意自然数$m$和$n$，如果$m \ne n$，那么$m^+ \ne n^+$。等价地，如果$m^+ = n^+$，那么$m = n$。
5. （PA5，归纳公理模式）对自然数的任意性质$P(n)$，如果$P(0)$为真，并且只要$P(n)$为真就有$P(n^+)$为真，那么对任意自然数$n$都有$P(n)$为真。

这样，我们就有了

$$
0, 0^+, (0^+)^+, ((0^+)^+)^+…
$$

如果删去上述公理中的某一条，得到的就可能不是我们所认识的自然数。例如，如果令某一自然数没有后继，那么自然数可以只有有限个；令一个自然数可以有多于一个后继，那么自然数可能是树状排列的；让$0$是某个自然数的后继，或者让不同的自然数可以有相同的后继，可以让后继运算在进行若干次后绕回到某一个数；如果没有归纳法原理，将可以存在一些自然数不能通过对$0$进行后继运算得到。

上述定义没有说明自然数是如何构造的，只是抽象出了自然数具备的基本性质。我们可以从这些性质推出其它的常见性质，并不需要涉及研究对象的具体构造。

---

在lean中，自然数`Nat`类型用归纳类型定义：

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

仿照上述定义，我们构造类型`N`，并定义一些常量和变量：

```lean
inductive N : Type
| _0 : N
| S  : N → N
open N
def _1 := S _0
def _2 := S _1
def _3 := S _2
variable (a b c d : N)
```

显然，我们有PA3和PA4:

```lean
theorem succ_neq_zero : S a ≠ _0 := by
  simp

theorem succ_eq_succ (h : S a = S b) : a = b := by
  simp at *
  assumption
```

当$a = b$时我们也有$a^+ = b^+$：

```lean
theorem succ_eq_succ_of_eq (h : a = b) : S a = S b :=
  congrArg S h
```

现在我们开始证明一些命题。

**命题：**对任意自然数$x$都有它的后继不等于它本身，即$x^+ \ne x$。

**证明：**采用归纳法。对于$0$，由PA3，有$0^+ \ne 0$。现在假设$x^+ \ne x$。由PA4，两个不同的自然数$x^+$和$x$有不同的后继，即$(x^+)^+ \ne x^+$。这就完成了归纳。

```lean
theorem self_neq_succ : S a ≠ a := by
  induction a with
  | _0      => simp
  | S a' ih => simp[ih]
```

**命题：**对任意非$0$自然数$x$都存在唯一前驱$y$使得$y^+ = x$。

**证明：**<br/>
唯一性：由PA4可得。<br/>
存在性：$x = 0$时命题成立。现在假设命题对$x$成立，则显然有$x^+ = x^+$，从而命题对$x^+$也成立。归纳完毕。<br/>

记$x$的前驱为$x^-$。为使每个自然数都有前驱，可定义$0$的前驱是$0$本身：

```lean
def N.P : N → N
| _0  => _0
| S a => a

@[simp]
theorem pred_succ : P (S a) = a := by
  rfl
```

在lean代码中可以用`S a`表示一个非$0$自然数（正自然数）$a^+$。不过这种表示方式有时会在处理上带来一些麻烦。

# 递归

令$A$为一非空集合，取$A$中一个固定元素$c$，再令$g : A \times \N \to A$为一函数，则唯一存在函数$f : \N \to X$满足$f(0) = c$和对任意自然数$n$都有$f(n^+) = g(f(n), n)$。

可以非正式地证明：对$0$已经唯一确定了$f(0) = c$（由PA3，$n^+ \ne 0$，无论$f(n^+)$如何定义都不改变$f(0)$的值）。现在假设$f(n)$的值已经唯一确定，则唯一确定了$f(n^+) = g(f(n), n)$（由PA4，$m \ne n$时有$m^+ \ne n^+$，无论其它的$f(m^+) = g(f(m), m)$如何定义都不改变$f(n^+)$的值）。从而对所有自然数$n$，$f(n)$都唯一确定了一个值。

以$(0, y)$和$(x, 0)$为结束条件、从$(x^+, y^+)$归约到$(x, y)$的函数也可以改写为在$min(x, y)$上递归的函数（不过下文的$min$函数已经用这种方式定义了，虽然$min$可以用其它方式定义）。

（好吧，其实主包并不知道什么是递归。。。😭）

---

我们先尝试变换一下归纳法的形式：

**命题：**令$P(a, b)$为一与任意自然数$a$和$b$有关的性质，若对任意自然数$a$都有$P(0, a)$和$P(a, 0)$成立，以及对任意自然数$a$和$b$，如果$P(a, b)$成立，那么$P(a^+, b^+)$成立，那么$P(a, b)$对任意自然数$a$和$b$都成立。

**证明：**对$a$归纳。$a = 0$时，有$P(0, b)$。现在假设对任意自然数$b$都有$P(a, b)$，对$b$归纳，$b = 0$时有$P(a^+, b)$，现在假设有$P(a^+, b)$，则由归纳假设“对任意自然数$b$都有$P(a, b)$”，我们有$P(a, b)$，从而有$P(a^+, b^+)$，从而对任意自然数$b$都有$P(a^+, b)$，从而$P(a, b)$对任意自然数$a$和$b$都成立。

```lean
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
```

# 加法

定义自然数加法$a + b$为：
$$
\begin{alignat*}{2}
a &+ 0& &:= a \\
a &+ b&^+ &:= (a + b)^+
\end{alignat*}
$$

```lean
instance : Add N where
  add a b := _add a b
    where _add a b := match b with
    | _0   => a
    | S b' => S (_add a b')
```

**命题：**上述定义的加法是唯一的。

**证明：**假设另有一加法$\oplus$满足
$$
\begin{alignat*}{2}
a &\oplus 0& &= a \\
a &\oplus b&^+ &= (a \oplus b)^+
\end{alignat*}
$$
对$b$归纳。$b = 0$时，对任意$a$有$a + 0 = a = a \oplus 0$。现在假设对任意$a$有$a \oplus b = a + b$，则有
$$
\begin{alignat*}{2}
a \oplus b^+ &= (a \oplus b)^+ \quad &(\oplus\text{定义})  \\
&= (a + b)^+ \quad &(\text{归纳假设}) \\
&= a + b^+ \quad &(+\text{定义})
\end{alignat*}
$$
从而对任意$a$，$b$都有$a \oplus b = a + b$。

```lean
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
```

**命题：**$0$是加法恒等元。<br/>
（右加以$0$）$a + 0 = a$，<br/>
（左加以$0$）$0 + a = a$。

**证明：**由定义有$a + 0 = a$。对于$0 + a = a$，对$a$归纳。$a = 0$时，有$0 + 0 = 0$。现在假设$0 + a = a$，则有$0 + a^+ = (0 + a)^+ = a^+$。归纳完毕。

```lean
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
```

**命题：**<br/>
（右加以后继数）$a + b^+ = (a + b)^+$，<br/>
（左加以后继数）$a^+ + b = (a + b)^+$。<br/>

**证明：**由定义有$a + b^+ = (a + b)^+$。对于$a^+ + b = (a + b)^+$，对$b$归纳。$b = 0$时，有$a^+ + 0 = a^+ = (a + 0)^+$。现在假设$a^+ + b = (a + b)^+$，则有
$$
\begin{alignat*}{2}
a^+ + b^+ &= (a^+ + b)^+ \quad &(\text{加法定义}) \\
&= ((a + b)^+)^+ \quad &(\text{归纳假设}) \\
&= (a + b^+)^+ \quad &(\text{加法定义})
\end{alignat*}
$$
归纳完毕。

```lean
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
```

作为推论，令$1 = 0^+$，对任意自然数$a$有$a + 1 = 1 + a = a^+$：

$$
\begin{alignat*}{2}
a + 1 &= (a + 0)^+ \quad &(\text{加法定义}) \\
&= a^+ \quad &(\text{加法定义}) \\
\\
1 + a &= (0 + a)^+ \quad &(\text{左加以后继数})\\
&= a^+ \quad &(\text{左加以}0)
\end{alignat*}
$$

```lean
@[simp]
theorem add_one : a + _1 = S a := by
  rfl

@[simp]
theorem one_add : _1 + a = S a := calc
  _1 + a = S _0 + a   := by rfl
  _      = S (_0 + a) := by rw[succ_add]
  _      = S a        := by rw[zero_add]
```

**命题：**（加法交换律）$a + b = b + a$。

**证明：**对$b$归纳。当$b = 0$时，有$a + 0 = 0 + a = a$。现在假设$a + b = b + a$，则有
$$
\begin{alignat*}{2}
a + b^+ &= (a + b)^+ \quad &(\text{加法定义}) \\
&= (b + a)^+ \quad &(\text{归纳假设}) \\
&= b^+ + a \quad &(\text{左加以后继数})
\end{alignat*}
$$
归纳完毕。

```lean
@[simp]
theorem add_comm : a + b = b + a := by
  induction b with
  | _0      => rw[add_zero, zero_add]
  | S b' ih => calc
    a + S b' = S (a + b') := by rfl
    _        = S (b' + a) := by rw[ih]
    _        = S b' + a   := by rw[succ_add]
```

**命题：**（加法结合律）$(a + b) + c = a + (b + c)$。

**证明：**对$c$归纳。当$c = 0$时，有$(a + b) + 0 = a + (b + 0) = a + b$。现在假设$(a + b) + c = a + (b + c)$，则有
$$
\begin{alignat*}{2}
(a + b) + c^+ &= ((a + b) + c)^+ \quad &(\text{加法定义}) \\
&= (a + (b + c))^+ \quad &(\text{归纳假设}) \\
&= a + (b + c^+) \quad &(\text{加法定义})
\end{alignat*}
$$
归纳完毕。

```lean
@[simp]
theorem add_asso {a b c : N} : (a + b) + c = a + (b + c) := by
  induction c with
  | _0      => rfl
  | S c' ih => calc
    (a + b) + S c' = S ((a + b) + c') := by rfl
    _              = S (a + (b + c')) := by rw[ih]
    _              = a + (b + S c')   := by rfl
```

有了常用的运算律，我们可以证明另外一些等式。

**命题：**$(a + b) + (c + d) = (a + c) = (b + d)$。

**证明：**
$$
\begin{alignat*}{2}
(a + b) + (c + d) &= a + (b + c) + d \quad &(\text{加法结合律}) \\
&= a + (c + b) + d \quad &(\text{加法交换律}) \\
&= (a + c) + (b + d) \quad &(\text{加法结合律})
\end{alignat*}
$$

```lean
theorem add_add_add_comm : (a + b) + (c + d) = (a + c) + (b + d) := calc
  (a + b) + (c + d) = a + (b + c) + d   := by repeat rw[add_asso]
  _                 = a + (c + b) + d   := by rw[add_comm b c]
  _                 = (a + c) + (b + d) := by repeat rw[add_asso]
```

**命题：**（加法消去律）若$a + c = b + c$，则$a = b$。

**证明：**对$c$归纳。$c = 0$时，有$a + 0 = b + 0$。由加法的定义有$a = b$。现在假设在$a + c = b + c$时有$a = b$，那么假设$a + c^+ = b + c^+$，由加法的定义有$(a + c)^+ = (b + c)^+$，由PA4有$a + c = b + c$，由归纳假设有$a = b$。

```lean
theorem add_elim {a b c : N} (h : a + c = b + c) : a = b := by
  induction c with
  | _0 =>
    simp at h
    exact h
  | S c' ih =>
    simp at h
    exact ih h
```

**命题：**对任意自然数$a$，$a$与正自然数之和不为$a$，即$a \ne a + b^+$。

**证明：**假设存在自然数$b$满足$a = a + b^+$。由假设有$0 + a = b^+ + a$。由加法消去律有$0 = b^+$，与PA3矛盾。

```lean
example {a b : N} (h : a = a + S b) : False := by
  rw [←zero_add a,add_asso,add_comm a (S b),←add_asso] at h
  cases add_elim h
```

**命题：**自然数和正自然数之和不为$0$，即$a + b^+ \ne 0$。

**证明：**$a + b^+ = (a + b)^+$，由PA3$(a + b)^+ \ne 0$。

```lean
example {a b : N} (h : a + S b = _0) : False := by
  simp at *
```

**命题：**$a + b = 0$当且仅当$a = 0$并且$b = 0$。

**证明：**<br/>
（$\implies$）假设$a \ne 0$，那么$a$为正数，$b$与正数之和$a + b \ne 0$。类似的，$b \ne 0$时也有$a + b \ne 0$。因此$a + b = 0$时有$a = 0$且$b = 0$。<br/>
（$\impliedby$）显然有$0 + 0 = 0$。

```lean
theorem add_zero_iff_zero_and_zero {a b : N} : a + b = _0 ↔ a = _0 ∧ b = _0 := by
  apply Iff.intro
  . intro h
    match a, b with
    | _0, _0 => exact ⟨Eq.refl _0, Eq.refl _0⟩
    | S _, _ => simp at h
    | _, S _ => cases h
  . intro h
    simp[*]
```

# 乘法

定义自然数乘法$a \times b$为：
$$
\begin{alignat*}{2}
a &\times 0& &:= 0 \\
a &\times b&^+ &:= (a \times b) + a
\end{alignat*}
$$

```lean
instance : Mul N where
  mul a b := _mul a b
    where _mul a b := match b with
      | _0   => _0
      | S b' => _mul a b' + a
```

规定乘法运算优先于加法运算，因此$(a \times b) + c$中的括号可以略去。按惯例乘号也可略去。

**命题：**上述定义的乘法是唯一的。

**证明：**假设另有一乘法$\otimes$满足
$$
\begin{alignat*}{2}
a &\otimes 0& &= 0 \\
a &\otimes b&^+ &= (a \otimes b) + a
\end{alignat*}
$$
对$b$归纳。$b = 0$时，对任意$a$有$a \times 0 = 0 = a \otimes 0$。现在假设对任意$a$有$a \otimes b = a \times b$，则有
$$
\begin{alignat*}{2}
a \otimes b^+ &= (a \otimes b) + a \quad &(\otimes\text{定义})  \\
&= (a \times b) + a \quad &(\text{归纳假设}) \\
&= a \times b^+ \quad &(\times\text{定义})
\end{alignat*}
$$
从而对任意$a$，$b$都有$a \otimes b = a \times b$。

```lean
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
```

**命题：**$0$是乘法零元。<br/>
（右乘以$0$）$a \times 0 = 0$，<br/>
（左乘以$0$）$0 \times a = 0$。

**证明：**由定义有$a \times 0 = 0$。对于$0 \times a = 0$，对$a$归纳。$a = 0$时，有$0 \times 0 = 0$。现在假设$0 \times a = 0$，则$0 \times a^+ = (0 \times a) + 0 = 0$。

```lean
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
```

**命题：**$1$是乘法恒等元。<br/>
（右乘以$1$）$a \times 1 = a$，<br/>
（左乘以$1$）$1 \times a = a$。

**证明：**

$a \times 1 = a \times 0 + a = a$。

对于$1 \times a = a$，对$a$归纳。$a = 0$时，有$1 \times 0 = 0$。现在假设$1 \times a = a$，则有$1 \times a^+ = 1 \times a + 1 = a + 1 = a^+$。

```lean
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
```

**命题：**<br/>
（右乘以后继数）$a \times b^+ = a \times b + a$，<br/>
（左乘以后继数）$a^+ \times b = a \times b + b$。

**证明：**由定义有$a \times b^+ = a \times b + a$。对$a^+ \times b = a \times b + b$，对$b$归纳。$b = 0$时，有$a^+ \times 0 = a \times 0 + 0 = 0$。现在假设$a^+ \times b = a \times b + b$，则有
$$
\begin{alignat*}{2}
a^+ \times b^+ &= a^+ \times b + a^+ \quad &(\text{乘法定义}) \\
&= (a \times b + b) + a^+ \quad &(\text{归纳假设}) \\
&= (a \times b + a) + b^+ \quad &(\text{加法的性质}) \\
&= a \times b^+ + b^+ \quad &(\text{乘法定义})
\end{alignat*}
$$

```lean
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
```

**命题：**（右乘以$2$和左乘以$2$）$a \times 2 = 2 \times a = a + a$。

**证明：**
$$
\begin{gather*}
a \times 2 = a \times 1 + a = a + a \\
2 \times a = 1 \times a + a = a + a
\end{gather*}
$$

```lean
@[simp]
theorem mul_two : a * _2 = a + a := calc
  a * _2 = a * _1 + a := by rfl
  _      = a + a      := by simp

@[simp]
theorem two_mul : _2 * a = a + a := calc
  _2 * a = S _1 * a   := by rfl
  _      = _1 * a + a := by simp
  _      = a + a      := by simp
```

**命题：**（乘法交换律）$a \times b = b \times a$。

**证明：**对$b$归纳。$b = 0$时，有$a \times 0 = 0 \times a = 0$。现在假设$a \times b = b \times a$，则有
$$
\begin{alignat*}{2}
a \times b^+ &= a \times b + a \quad &(\text{乘法定义}) \\
&= b \times a + a \quad &(\text{归纳假设}) \\
&= b^+ \times a \quad &(\text{左乘以后继数})
\end{alignat*}
$$

```lean
@[simp]
theorem mul_comm : a * b = b * a := by
  induction b with
  | _0      => rw[mul_zero, zero_mul]
  | S b' ih => calc
    a * S b' = a * b' + a := by rfl
    _        = b' * a + a := by rw[ih]
    _        = S b' * a   := by rw[succ_mul]
```

**命题：**乘法对加法满足分配律。<br/>
（乘法对加法的右分配律）$(b + c)a = ba + ca$，<br/>
（乘法对加法的左分配律）$a(b + c) = ab + ac$。

**证明：**先证明右分配律。对$a$归纳。$a = 0$时，有$(b + c) \times 0 = b \times 0 + c \times 0 = 0$。现在假设$(b + c)a = ba + ca$，则有
$$
\begin{alignat*}{2}
(b + c)a^+ &= (b + c)a + (b + c) \quad &(\text{乘法定义}) \\
&= (ba + ca) + (b + c) \quad &(\text{归纳假设}) \\
&= (ba + b) + (ca + c) \quad &(\text{加法的性质}) \\
&= ba^+ + ca^+ \quad &(\text{乘法定义})
\end{alignat*}
$$

应用乘法交换律即可得到左分配律。

```lean
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
```

**命题：**（乘法结合律）$(ab)c = a(bc)$。

**证明：**对$c$归纳。$c = 0$时，有$ab \times 0 = a(b \times 0) = 0$。现在假设$(ab)c = a(bc)$，则有
$$
\begin{alignat*}{2}
(ab)c^+ &= (ab)c + ab \quad &(\text{乘法定义}) \\
&= a(bc) + ab \quad &(\text{归纳假设}) \\
&= a(bc + b) \quad &(\text{乘法对加法的分配律}) \\
&= a(bc^+) \quad &(\text{乘法定义})
\end{alignat*}
$$

```lean
@[simp]
theorem mul_asso {a b c : N} : (a * b) * c = a * (b * c) := by
  induction c with
  | _0      => rfl
  | S c' ih => calc
    (a * b) * S c' = (a * b) * c' + (a * b) := by rfl
    _              = a * (b * c') + (a * b) := by rw[ih]
    _              = a * (b * c' + b)       := by rw[mul_left_dist]
    _              = a * (b * S c')         := by rfl
```

**命题：**$(ab)(cd) = (ac)(bd)$。

**证明：**
$$
\begin{alignat*}{2}
(ab)(cd) &= a(bc)d \quad &(\text{乘法结合律}) \\
&= a(cb)d \quad &(\text{乘法交换律}) \\
&= (ac)(bd) \quad &(\text{乘法结合律})
\end{alignat*}
$$

```lean
theorem mul_mul_mul_comm : (a * b) * (c * d) = (a * c) * (b * d) := calc
  (a * b) * (c * d) = a * (b * c) * d   := by repeat rw[mul_asso]
  _                 = a * (c * b) * d   := by rw[mul_comm b c]
  _                 = (a * c) * (b * d) := by repeat rw[mul_asso]
```

**命题：**$ab = 0$当且仅当$a = 0$或$b = 0$。

**证明：**<br/>
（$\implies$）$a$和$b$均不为$0$时，可设$c^+ = a$和$d^+ = b$，则$ab = c^+ \times d^+ = c^+ \times d + c^+ \ne 0$。因此$a$和$b$至少有一个数为$0$。<br/>
（$\impliedby$）显然当$a$或$b$为$0$时有$ab = 0$。

```lean
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
```

在证明乘法的消去律之前，我们首先要定义自然数的序。

# 序

定义自然数的序$\le$：
$$
\begin{alignat*}{2}
0 &\le a& &:= \top \\
a^+ &\le 0& &:= \bot \\
a^+ &\le b&^+ &:= a \le b
\end{alignat*}
$$

$a \ge b$表示$b \le a$。

```lean
def N.ble : N → N → Bool
  | _0,  _   => true
  | S _, _0  => false
  | S a, S b => ble a b

def N.le : Prop :=
  ble a b = true

instance : LE N where
  le := N.le
```

在lean的prelude中的定义为：

```lean
set_option bootstrap.genMatcherCode false in
/--
The Boolean less-than-or-equal-to comparison on natural numbers.

This function is overridden in both the kernel and the compiler to efficiently evaluate using the
arbitrary-precision arithmetic library. The definition provided here is the logical model.

Examples:
 * `Nat.ble 2 5 = true`
 * `Nat.ble 5 2 = false`
 * `Nat.ble 5 5 = true`
-/
@[extern "lean_nat_dec_le"]
def Nat.ble : @& Nat → @& Nat → Bool
  | zero,   _      => true
  | succ _, zero   => false
  | succ n, succ m => ble n m

/--
Non-strict, or weak, inequality of natural numbers, usually accessed via the `≤` operator.
-/
protected inductive Nat.le (n : Nat) : Nat → Prop
  /-- Non-strict inequality is reflexive: `n ≤ n` -/
  | refl     : Nat.le n n
  /-- If `n ≤ m`, then `n ≤ m + 1`. -/
  | step {m} : Nat.le n m → Nat.le n (succ m)

instance instLENat : LE Nat where
  le := Nat.le
```

由定义有：

1. 对任意自然数$a$都有$0 \le a$。
2. 不存在正数$a$使$a \le 0$（若$a \le 0$则$a = 0$）。
3. $a \le b \iff a^+ \le b^+$。

```lean
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
```

**命题：**$a \le a^+$。

**证明：**对$a$归纳。$a = 0$时，有$0 \le 1$。现在假设$a \le a^+$。$a^+ \le (a^+)^+$与$a \le a^+$等价。

```lean
theorem le_succ : a ≤ S a := by
  induction a with
  | _0      => exact Eq.refl (ble _0 _1)
  | S a' ih => exact ih
```

**命题：**<br/>
1. （自反性）$a \le a$。
2. $a = b \to a \le b$。
3. （反对称性）若$a \le b$且$b \le a$，则$a = b$。
4. （传递性）若$a \le b$且$b \le c$，则$a \le c$。
5. （可比性）$a \le b$和$b \le a$二者必居其一。
6. （加法保序）$a \le b$当且仅当$a + c \le b + c$。
7. 如果$a \le b$，那么$a \le b + c$。
8. 如果$a \le b$，那么$a \le b \times c^+$。

**证明：**<br/>
1. 对$a$归纳。$a = 0$时有$0 \le 0$。现在假设$a \le a$，则$a^+ \le a^+$与$a \le a$等价，也为真。
2. 由自反性立得。
3. $a = b = 0$时有$0 \le 0$和$0 = 0$。当$a = 0$且$b \ne 0$时，$b \nleq 0$。类似的，当$a \ne 0$且$b = 0$时，$a \nleq 0$。现在假设当$a \le b$且$b \le a$时有$a = b$，则当$a^+ \le b^+$且$b^+ \le a^+$时，由序的定义有$a \le b$和$b \le a$，由假设有$a = b$，于是有$a^+ = b^+$。
4. $a = 0$时显然有$0 \le c$。$a \ne 0$且$b = 0$或$c = 0$时有矛盾。现在假设当$a \le b$且$b \le c$时有$a \le c$，则当$a^+ \le b^+$且$b^+ \le c^+$时，由序的定义有$a \le b$和$b \le c$，由假设有$a \le c$，于是有$a^+ \le c^+$。
5. $a = 0$时有$0 \le b$，$b = 0$时有$0 \le a$。对$a^+$和$b^+$，$a^+ \le b^+ \lor b^+ \le a^+$和$a \le b \lor b \le a$等价。
6. （$\implies$）对$c$归纳。$c = 0$时显然有$a + c \le b + c$。现在假设当$a \le b$时有$a + c \le b + c$。$a + c^+ \le b + c^+$与$a + c \le b + c$等价。<br/>
（$\impliedby$）对$c$归纳。$c = 0$时显然有$a \le b$。现在假设当$a + c \le b + c$时有$a \le b$。$a + c^+ \le b + c^+$与$a + c \le b + c$等价，由假设有$a \le b$。
7. 对$c$归纳。$c = 0$时显然有$a \le b + 0$。现在假设$a \le b + c$，则有$a \le b + c \le b + c^+$。
8. 对$c$归纳。$c = 0$，$c^+ = 1$时显然有$a \le b \times 1$。现在假设$a \le b + c^+$，则有$a \le b + c^+ \le b + c^+ + b = b \times (c^+)^+$。

```lean
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
```

$a \le b$也可以定义为存在自然数$c$使得$a + c = b$。可以证明这种定义和递归定义的$\le$是等价的。

**命题：**$a ≤ b ↔ ∃ c (a + c = b)$。

**证明：**<br/>
（$\implies$）$0 \le b$时，有$0 + b = b$。现在假设$a \le b$时有$a + c = b$。$a^+ \le b^+$时，有$a \le b$，由假设得$a + c = b$，即有$a^+ + c = b^+$。<br/>
（$\impliedby$）$c = 0$时，有$a + 0 = b$，由$a = b$有$a \le b$。<br/>
$a = 0$时，显然有$0 \le b$。现在假设$a + c = b$时有$a \le b$，$a^+ + c = b^+$时，有$(a + c)^+ = b^+$，于是$a + c = b$，由假设有$a \le b$，从而有$a^+ \le b^+$。

```lean
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
```

可以用这种定义证明之前证明过的一些命题。

> [!NOTE]- 证明
> **命题：**<br/>
> 1. $0 \le a$。
> 2. （自反性）$a \le a$。
> 3. $a = b \to a \le b$。
> 4. （反对称性）若$a \le b$且$b \le a$，则$a = b$。
> 5. （传递性）若$a \le b$且$b \le c$，则$a \le c$。
> 6. （可比性）$a \le b$和$b \le a$二者必居其一。
> 7. （加法保序）$a \le b$当且仅当$a + c \le b + c$。
> 8. 如果$a \le b$，那么$a \le b + c$。
> 9. 如果$a \le b$，那么$a \le b \times c^+$。
>
> **证明：**<br/>
> 1. 由$0 + a = a$有$0 \le a$。
> 2. 由$a + 0 = a$有$a \le a$。
> 3. 由自反性立得。
> 4. 由$a \le b$和$b \le a$，可知存在自然数$c_{1}$和$c_{2}$使得$a + c_{1} = b$和$b + c_{2} = a$，前式代入后式得$a + c_{1} + c_{2} = a$，消去$a$有$c_{1} + c_{2} = 0$，于是$c_{1} = c_{2} = 0$，于是有$a = b$。
> 5. 由$a \le b$和$b \le c$，可知存在自然数$c_{1}$和$c_{2}$使得$a + c_{1} = b$和$b + c_{2} = c$，前式代入后式得$a + (c_{1} + c_{2}) = c$，于是有$a \le c$。
> 6. 对$a$归纳。$a = 0$时，由$0 + b = b$有$0 \le b$。现在假设对$a$和$b$有$a \le b$或$b \le a$。<br/>
> $a \le b$时，有$a + c = b$。当$c = 0$时，有$a = b$，则有$b + 1 = a^+$，于是有$b \le a^+$。当$c \ne 0$时，有$a + c^+ = a^+ + c = b$，于是有$a^+ \le b$。<br/>
> $b \le a$时，有$b + c = a$，则有$b + c^+ = a^+$，于是有$b \le a^+$。
> 7. （$\implies$）$a \le b$时有$a + c_{0} = b$，两边加$c$有$(a + c) + c_{0} = b + c$，从而$a + c \le b + c$。<br/>
> （$\impliedby$）$a + c \le b + c$时有$(a + c) + c_{0} = (b + c)$，两边消去$c$有$a + c_{0} = b$，从而$a \le b$。
> 8. $a \le b$时有$a + c_{0} = b$，两边加$c$有$a + (c_{0} + c) = b + c$，从而$a \le b + c$。
> 9. $a \le b$时有$a + c_{0} = b$，两边加$b \times c$有$a + (c_{0} + b \times c) = b + b \times c = b \times c^+$，从而$a \le b \times c^+$。
>
> ```lean
> theorem zero_le_alt : _0 ≤ a :=
>   le_addeq.mpr ⟨a, zero_add a⟩
>
> theorem le_refl_alt : a ≤ a :=
>   le_addeq.mpr ⟨_0, add_zero a⟩
>
> theorem le_of_eq_alt {a b : N} (h : a = b) : a ≤ b :=
>   le_addeq.mpr ⟨_0, h ▸ add_zero a⟩
>
> theorem le_antisymm_alt {a b : N} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
>   have ⟨c1, heq1⟩ := le_addeq.mp h1
>   have ⟨c2, heq2⟩ := le_addeq.mp h2
>   have hc := heq1 ▸ heq2
>   rw[add_asso, add_comm] at hc
>   rw (occs := .pos [2]) [←zero_add a] at hc
>   have hc := add_elim hc
>   have ⟨c1z, c2z⟩ := add_zero_iff_zero_and_zero.mp hc
>   simp[c1z] at heq1
>   exact heq1
>
> theorem le_trans_alt {a b c : N} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
>   have ⟨c1, heq1⟩ := le_addeq.mp h1
>   have ⟨c2, heq2⟩ := le_addeq.mp h2
>   le_addeq.mpr ⟨c1 + c2, add_asso ▸ (heq1 ▸ heq2)⟩
>
> theorem le_total_alt {a b : N} : a ≤ b ∨ b ≤ a := by
>   induction a with
>   | _0      => exact Or.inl (le_addeq.mpr ⟨b, zero_add b⟩)
>   | S a' ih =>
>     apply ih.elim
>     . intro hab
>       have ⟨c, heq⟩ := le_addeq.mp hab
>       match c with
>       | _0 =>
>         have h := le_addeq.mpr ⟨_1, (congrArg S heq).symm⟩
>         simp at *
>         exact Or.inr h
>       | S c' =>
>         rw[add_succ, ←succ_add] at heq
>         exact Or.inl (le_addeq.mpr ⟨c', heq⟩)
>     . intro hba
>       have ⟨c, heq⟩ := le_addeq.mp hba
>       exact Or.inr (le_addeq.mpr ⟨S c, congrArg S heq⟩)
>
> theorem le_add_alt {a b : N} : a ≤ b ↔ a + c ≤ b + c := by
>   apply Iff.intro
>   . intro h
>     have ⟨c0, heq⟩ := le_addeq.mp h
>     have heq := congrArg (fun n => n + c) heq
>     rw[add_asso,add_comm c0 c,←add_asso] at heq
>     exact le_addeq.mpr ⟨c0, heq⟩
>   . intro h
>     have ⟨c0, heq⟩ := le_addeq.mp h
>     rw[add_asso,add_comm c c0,←add_asso] at heq
>     have heq := add_elim heq
>     exact le_addeq.mpr ⟨c0, heq⟩
>
> theorem le_add_right_alt {a b : N} (h : a ≤ b) : a ≤ b + c := by
>   have ⟨c0, heq⟩ := le_addeq.mp h
>   have heq := congrArg (fun n => n + c) heq
>   rw[add_asso] at heq
>   exact le_addeq.mpr ⟨c0 + c, heq⟩
>
> theorem le_mul_right_alt {a b : N} (h : a ≤ b) : a ≤ b * S c := by
>   have ⟨c0, heq⟩ := le_addeq.mp h
>   have heq := congrArg (fun n => n + b * c) heq
>   simp at *
>   exact le_addeq.mpr ⟨c0 + c * b, heq⟩
>```

**命题：**若$a \le b$且$c \le d$，则$a + c \le b + d$。

**证明：**由$a \le b$和$c \le d$，有$a + c \le b + c$和$b + c \le b + d$，于是$a + c \le b + c \le b + d$。

```lean
theorem le_add_le {a b c d : N} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  have h3 := (le_add b).mp h2
  rw [add_comm c b, add_comm d b] at h3
  exact le_trans ((le_add c).mp h1) h3
```

定义$a < b$为$a^+ \le b$。$a > b$表示$b < a$。

```lean
def N.blt (a b : N) : Bool :=
  N.ble (S a) b

def N.lt : Prop :=
  blt a b = true

instance : LT N where
  lt := N.lt
```

**命题：**$a < b \iff a^+ \le b^+$。

**证明：**$a < b \iff a^+ \le b \iff (a^+)^+ \le b^+ \iff a^+ < b^+$。

```lean
theorem succ_lt_succ {a b : N} (h : a < b) : S a < S b := by
  have h : blt a b = true := h
  rw[show blt a b = blt (S a) (S b) from rfl] at h
  exact h

theorem pred_lt_pred {a b : N} (h : S a < S b) : a < b := by
  have h : blt (S a) (S b) = true := h
  rw[show blt (S a) (S b) = blt a b from rfl] at h
  exact h
```

**命题：**<br/>
1. $a \nless 0$。
2. $a < a^+$。
3. $0 < a^+$。
4. 若$0 < a$，则$a$存在前驱$b$使$b^+ = a$。
5. 若$a < b$，则$0 < b$。
6. 若$a < b$，则$a \ne b$。
7. 若$a < b$，则$a \le b$。
8. 若$a \le b$，则$a < b$或$a = b$。

**证明：**<br/>
1. 对任意$a$都有$a^+ \nleq 0$。
2. 由$a^+ \le a^+$可得。
3. 由$0 \le a$，有$1 \le a^+$，即有$0 < a^+$。
4. $0 < a$时$a \ne 0$，对非零自然数都有前驱$b$使$b^+ = a$。
5. 由$a < b$有$b \ne 0$，所以有$0 < c^+ = b$。
6. $a = 0$时，$0 \nless 0$，所以$b \ne 0$。现在假设$a < b$时有$a \ne b$。$a^+ < b^+$时有$a < b$，由归纳假设有$a \ne b$，则有$a^+ \ne b^+$。
7. $a < b$时有$a^+ \le b$，即有$a \le a^+ \le b$。
8. $a = b = 0$时有$0 = 0$。$a = 0$且$b \ne 0$时有$0 < b$。$b = 0$且$a \ne 0$时有矛盾。现在假设时$a \le b$有$a < b$或$a = b$。由$a^+ \le b^+$有$a \le b$，由假设有$a < b$或$a = b$。$a < b$时有$a^+ < b^+$，$a = b$时有$a^+ = b^+$。

```lean
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
```

**命题：**<br/>
1. （反自反性）$a \nless a$。
2. （传递性）若$a < b$且$b < c$，则$a < c$。
3. （非对称性）$a < b$和$b < a$不能同时成立。

**证明：**<br/>
1. 已经证明若$a < b$，则$a \ne b$。现在有$a = a$，于是$a \nless a$。
2. $a = 0$时有$0 < c$。$b$或$c$为$0$时有矛盾。现在假设$a < b$且$b < c$时有$a < c$，则$a^+ < b^+$且$b^+ < c^+$时有$a < b$且$b < c$，由假设有$a < c$，于是$a^+ < c^+$。
3. 若$a < b$且$b < a$，由传递性有$a < a$，不符合反自反性。

```lean
theorem lt_arefl {a : N} (h : a < a) : False :=
  @lt_neq a a h (Eq.refl a)

theorem lt_trans {a b c : N} (h1 : a < b) (h2 : b < c) : a < c :=
  match a, b, c with
  | _0, _, S c'      => Eq.refl (blt _0 (S c'))
  | S a', S b', S c' => @lt_trans a' b' c' h1 h2

theorem lt_asymm {a b : N} (h1 : a < b) (h2 : b < a) : False :=
  lt_arefl (@lt_trans a b a h1 h2)
```

**命题：**（序的三歧性）$a < b$、$a = b$和$a > b$三者必居其一。

**证明：**由$<$的反自反性和非对称性可知这三者至多有一个成立，现在证明这三者至少有一个成立。$a = b = 0$时有$0 = 0$，$a = 0$且$b \ne 0$时有$0 < b$，$b = 0$且$a \ne 0$时有$a > 0$。假设$a < b$、$a = b$或$a > b$，则分别能得到$a^+ < b^+$、$a^+ = b^+$和$a^+ > b^+$。

作为推论，我们有$a \le b$和$a > b$二者必居其一。

```lean
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
```

**命题：**不存在自然数$b$使得$a < b < a^+$。

**证明：**$a < b$即$a^+ \le b$，与$a^+ > b$矛盾。

```lean
theorem not_between_self_and_succ {a b : N} (h1 : a < b) (h2 : b < S a) : False :=
  le_ngt h1 h2
```

**命题：**<br/>
1. $a < b \iff a + c < b + c$。
2. 若$a < b$，则$a < b + c$。
3. 若$a < b$且$c < d$，则$a + c < b + d$。
4. 若$a \le b$且$c < d$，则$a + c < b + d$。
5. 如果$a < b$，那么$a < b \times c^+$。

**证明：**<br/>
1. （$\implies$）对$c$归纳。$c = 0$时显然有$a + c < b + c$。现在假设当$a < b$时有$a + c < b + c$。$a + c^+ < b + c^+$与$a + c < b + c$等价。<br/>
（$\impliedby$）对$c$归纳。$c = 0$时显然有$a < b$。现在假设当$a + c < b + c$时有$a < b$。$a + c^+ < b + c^+$与$a + c < b + c$等价，由假设有$a < b$。
2. 对$c$归纳。$c = 0$时显然有$a < b + 0$。现在假设$a < b + c$，则有$a < b + c < b + c^+$。
3. $a + c < b + c < b + d$。
4. $a \le b$时有$a < b$或$a = b$，$a < b$时已经证明$a + c < b + d$，$a = b$时在$c < d$两边加$a$（即$b$）即有$a + c < b + d$。
5. 对$c$归纳。$c = 0$，$c^+ = 1$时显然有$a < b \times 1$。现在假设$a < b + c^+$，则有$a < b + c^+ < b + c^+ + b = b \times (c^+)^+$。

```lean
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
```

**命题：**
1. （乘法保序）$a < b \iff ac^+ < bc^+$。
2. （乘法消去律）若$ac^+ = bc^+$，则$a = b$。
3. $a \le b \iff ac^+ \le bc^+$。

**证明：**<br/>
1. （$\implies$）对$c$归纳。$c = 0$，$c^+ = 1$时，显然有$a \times 1 < b \times 1$。现在假设$ac^+ < bc^+$，与$a < b$相加，则有$ac^+ + a < bc^+ + b$，即$a(c^+)^+ < b(c^+)^+$。<br/>
（$\impliedby$）假设$a = b$，则有$ac^+ = bc^+$，与$ac^+ < bc^+$矛盾。假设$a > b$时也有类似矛盾。由序的三歧性必有$a < b$。
2. 假设$a < b$，则有$ac^+ < bc^+$，与$ac^+ = bc^+$矛盾。假设$a > b$时也有类似矛盾。由序的三歧性必有$a = b$。
3. （$\implies$）由$a \le b$有$a < b$或$a = b$，分别在两边乘$c^+$有$ac^+ < bc^+$或$ac^+ = bc^+$，两种情况都有$ac^+ \le bc^+$。<br/>
（$\impliedby$）由$ac^+ \le bc^+$有$ac^+ < bc^+$或$ac^+ = bc^+$，分别在两边消去$c^+$有$a < b$或$a = b$，两种情况都有$a \le b$。

```lean
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
```

**命题：**<br/>
1. 若$a < b$且$c < d$，则$ac < bd$。
2. 若$a \le b$且$c \le d$，则$ac \le bd$。
3. 若$a^+ \le b^+$且$c < d$，则$a^{+}c < b^{+}d$。

**证明：**<br/>
1. $b$和$d$都大于$0$。$ac = 0$时，有$0 < bd$。$c \ne 0$时，有$ac < bc < bd$。
2. $ac = 0$时，有$0 \le bd$。$a$和$c$都不为$0$时（此时有$b$和$d$都大于$0$），有$ac \le bc \le bd$。
3. 由$a^+ \le b^+$有$a^+ < b^+$或$a^+ = b^+$。$a^+ < b^+$时，已经证明$a^{+}c < b^{+}d$。$a^+ = b^+$时，在$c < d$两边乘$a^+$（即$b^+$）即有$a^{+}c < b^{+}d$。

```lean
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
```

**命题：**$ab = 1$当且仅当$a = 1$且$b = 1$。

**证明：**<br/>
（$\implies$）若$a = 1$，则$ab = 1 \times b = b = 1$。若$a < 1$，则$a \le 0$，则有$a = 0$，$ab = 0$，与$ab = 1$矛盾。当$a > 1$时，若$b = 1$，则$ab = a \times 1 = a = 1$，与$a > 1$矛盾；若$b < 1$，则$b \le 0$，则有$b = 0$，$ab = 0$，与$ab = 1$矛盾；若$b > 1$，则$a > 1$与$b > 1$相乘得$ab > 1$，与$ab = 1$矛盾。<br/>
（$\impliedby$）显然有$1 \times 1 = 1$。

```lean
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
```

**命题：**$a < b$当且仅当存在正自然数$c^+$使得$a + c^+ = b$。

**证明：**（$\implies$）$a < b$时有$a^+ \le b$，则有自然数$c$使得$a^+ + c = b$，则有$a + c^+ = b$。<br/>
（$\impliedby$）$a + c^+ = b$时有$a^+ + c = b$，则有$a^+ \le b$，即$a < b$。

```lean
theorem lt_addeq {a b : N} : a < b ↔ ∃ c, a + S c = b := by
  apply Iff.intro
  . intro h
    have ⟨c, heq⟩ := le_addeq.mp h
    simp at *
    exact ⟨c, heq⟩
  . intro ⟨c, h⟩
    rw[add_succ,←succ_add] at h
    exact le_addeq.mpr ⟨c, h⟩
```

# 乘方

定义自然数乘方$a^b$为：
$$
\begin{alignat*}{1}
a^0 &:= 1 \\
a^{b^+} &:= a^b \times a
\end{alignat*}
$$

```lean
instance : Pow N N where
  pow a b := _pow a b
    where _pow a b := match b with
      | _0   => _1
      | S b' => _pow a b' * a
```

可以验证上述定义的乘方是唯一的：若另有一函数$pow(a, b)$满足上述定义，则当$b = 0$时有$pow(a, 0) = 1 = a^0$，现在假设$pow(a, b) = a^b$，则$pow(a, b^+) = pow(a, b) \times a = a^b \times a = a^{b^+}$。

```lean
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
```

我们有$a^0 = 1$以及当$a > 0$时$0^a = 0$。

```lean
@[simp]
theorem pow_zero : a ^ _0 = _1 := by
  rfl

@[simp]
theorem zero_pow : _0 ^ S a = _0 := by
  rfl
```

我们还有$a^1 = a^0 \times a = 1 \times a = a$，平方$a^2 = a^1 \times a = a \times a$，立方$a^3 = a^2 \times a = a \times a \times a$……

```lean
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
```

为了方便重写项，我们写出$a^{b^+} = a^b \times a$：

```lean
@[simp]
theorem pow_succ : a ^ S b = a ^ b * a := by
  rfl
```

**命题：**$1^a = 1$。

**证明：**对$a$归纳。$a = 0$时有$1^0 = 1$。现在假设$1^a = 1$，则有$1^{a^+} = 1^a \times 1 = 1$。

```lean
@[simp]
theorem one_pow : _1 ^ a = _1 := by
  induction a with
  | _0      => rfl
  | S a' ih => calc
    _1 ^ S a' = _1 ^ a' * _1 := by rfl
    _         = _1           := by simp[ih]
```

**命题：**（完全平方公式）$(a + b)^2 = a^2 + 2ab + b^2$。

**证明：**
$$
\begin{alignat*}{2}
(a + b)^2 &= (a + b)(a + b) \quad &(\text{平方}) \\
&= a(a + b) + b(a + b) \quad &(\text{乘法对加法的分配律}) \\
&= (aa + ab) + (ab + bb) \quad &(\text{乘法对加法的分配律、乘法交换律}) \\
&= a^2 + (ab + ab) + b^2 \quad &(\text{平方、加法结合律}) \\
&= a^2 + 2ab + b^2 \quad &(\text{乘}2)
\end{alignat*}
$$

```lean
theorem square_of_sum : (a + b) ^ _2 = a ^ _2 + _2 * (a * b) + b ^ _2 := by
  simp
```

**命题：**（指数律）<br/>
1. $a^{b + c} = a^{b}a^{c}$。
2. $(a^b)^c = a^{bc}$。
3. $(ab)^c = a^{c}b^{c}$。

**证明：**<br/>
1. 对$c$归纳。$c = 0$时有$a^{b + 0} = a^b = a^{b}a^{0}$。现在假设$a^{b + c} = a^{b}a^{c}$，则有$a^{b + c^+} = a^{b + c}a = a^{b}a^{c}a = a^{b}a^{c^+}$（由归纳假设有第2个等号）。
2. 对$c$归纳。$c = 0$时有$(a^b)^0 = 1 = a^{b \times 0}$。现在假设$(a^b)^c = a^{bc}$，则有$(a^b)^{c^+} = (a^b)^{c}a^{b} = a^{bc}a^{b} = a^{bc + b} = a^{bc^+}$（由归纳假设有第2个等号）。
3. 对$c$归纳。$c = 0$时有$(ab)^0 = 1 = a^{0}b^{0}$。现在假设$(ab)^c = a^{c}b^{c}$，则有$(ab)^{c^+} = (ab)^{c}ab = a^{c}b^{c}ab = a^{c}ab^{c}b = a^{c^+}b^{c^+}$（由归纳假设有第2个等号）。

```lean
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
```

**命题：**（乘方和序）<br/>
1. $a < b \iff a^{c^+} < b^{c^+}$。
2. 若$a^{c^+} = b^{c^+}$，则$a = b$。
3. $a \le b \iff a^{c^+} \le b^{c^+}$。
4. 若$a > 0$，则$a^{b} > 0$。
5. 若$a < b$，则$a < b^{c^+}$。
6. 若$a \le b$，则$a \le b^{c^+}$。
7. $(c^+ > 1 ∧ a < b) \iff (c^+)^{a} < (c^+)^{b}$。
8. 若$c > 0$且$a \le b$，则$c^{a} \le c^{b}$。

**证明：**<br/>
1. （$\implies$）对$c$归纳。$c = 0$，$c^+ = 1$时，显然有$a^1 < b^1$。现在假设$a^{c^+} < b^{c^+}$，与$a < b$相乘，则有$a^{c^+}a < b^{c^+}b$，即$a^{(c^+)^+} < b^{(c^+)^+}$。<br/>
（$\impliedby$）假设$a = b$，则有$a^{c^+} = b^{c^+}$，与$a^{c^+} < b^{c^+}$矛盾。假设$a > b$时也有类似矛盾。由序的三歧性必有$a < b$。
2. 假设$a < b$，则有$a^{c^+} < b^{c^+}$，与$a^{c^+} = b^{c^+}$矛盾。假设$a > b$时也有类似矛盾。由序的三歧性必有$a = b$。
3. （$\implies$）由$a \le b$有$a < b$或$a = b$，此时分别有$a^{c^+} < b^{c^+}$和$a^{c^+} = b^{c^+}$，两种情况都有$a^{c^+} \le b^{c^+}$。<br/>
（$\impliedby$）由$a^{c^+} \le b^{c^+}$有$a^{c^+} < b^{c^+}$或$a^{c^+} = b^{c^+}$，分别可以得到$a < b$或$a = b$，两种情况都有$a \le b$。
4. 对$b$归纳。$b = 0$时有$0 < 1 = a^0$。现在假设$0 < a^b$，在右边乘$a$即有$0 < a^ba = a^{b^+}$。
5. $a < b$时有$b > 0$，所以有$b^c > 0$。在$a < b$的右侧乘$b^c$即有$a < bb^c = b^{c^+}$。
6. $a = b = 0$时有$0 = 0^{c^+}$。$a > 0$（同时$b > 0$）时有$b^c > 0$，在$a \le b$的右侧乘$b^c$即有$a \le bb^c = b^{c^+}$。
7. （$\implies$）由$a < b$得$a + d^+ = b$。$1 < c^+$右侧作$d^+$次方有$1 < (c^+)^{d^+}$。由于$(c^+)^{a} > 0$，可以在$1 < (c^+)^{d^+}$两侧乘$(c^+)^{a}$得到$(c^+)^{a} < (c^+)^{d^+}(c^+)^{a} = (c^+)^{a + d^+} = (c^+)^{b}$。<br/>
（$\impliedby$）若$c^+ = 1$则有$1^{a} = 1^{b}$，矛盾，所以有$c^+ > 1$。当$c^+ > 1$时，若$a = b$则有$(c^+)^{a} = (c^+)^{b}$，矛盾。$a > b$时也有类似矛盾。由序的三歧性必有$a < b$。
8. $a = b$时有$c^{a} = c^{a}$。$a < b$时，若$c = 1$，则有$1^{a} = 1^{b}$；若$c > 1$，则有$c^{a} < c^{b}$，从而$c^{a} \le c^{b}$。

```lean
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
```

**命题：**$1 + ab \le (1 + a)^b$。

**证明：**对$b$归纳。$b = 0$时有$1 = 1$。现在假设$1 + ab \le (1 + a)^b$，则有$1 + ab^+ = 1 + ab + a \le 1 + ab + a + a^{2}b = (1 + ab)(1 + a) \le (1 + a)^b(1 + a) = (1 + a)^{b^+}$。

```lean
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
```

# 最小值与最大值

定义$min$和$max$函数：
$$
\begin{alignat*}{3}
min(0, b) &:= 0 &\quad max(0, b) &:= b \\
min(a, 0) &:= 0 &\quad max(a, 0) &:= a \\
min(a^+, b^+) &:= min(a, b)^+ &\quad max(a^+, b^+) &:= max(a, b)^+
\end{alignat*}
$$

```lean
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
```

**命题：**（幂等律）$min(a, a) = max(a, a) = a$。

**证明：**对$a$归纳。$a = 0$时有$min(0, 0) = max(0, 0) = 0$。现在假设$min(a, a) = max(a, a) = a$。则有$min(a^+, a^+) = min(a, a)^+ = a^+$和$max(a^+, a^+) = max(a, a)^+ = a^+$。

```lean
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
```

**命题：**（交换律）
$$
\begin{gather*}
min(a, b) = min(b, a) \\
max(a, b) = max(b, a)
\end{gather*}
$$

**证明：**$ab = 0$时显然有
$$
\begin{gather*}
min(0, a) = 0 = min(a, 0) \\
max(0, a) = 0 = max(a, 0)
\end{gather*}
$$
现在假设$min(a, b) = min(b, a)$和$max(a, b) = max(b, a)$，则有
$$
\begin{gather*}
min(a^+, b^+) = min(a, b)^+ = min(b, a)^+ = min(b^+, a^+) \\
max(a^+, b^+) = max(a, b)^+ = max(b, a)^+ = max(b^+, a^+)
\end{gather*}
$$

```lean
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
```

**命题：**（结合律）
$$
\begin{gather*}
min(min(a, b), c) = min(a, min(b, c)) \\
max(max(a, b), c) = max(a, max(b, c))
\end{gather*}
$$

**证明：**
$$
\begin{gather*}
min(min(0, b), c) = min(0, c) = 0 = min(0, min(b, c)) \\
min(min(a, 0), c) = min(0, c) = 0 = min(a, 0) = min(a, min(0, c)) \\
min(min(a, b), 0) = 0 = min(a, 0) = min(a, min(b, 0)) \\
\\
max(max(0, b), c) = max(b, c) = max(0, max(b, c)) \\
max(max(a, 0), c) = max(a, c) = max(a, max(0, c)) \\
max(max(a, b), 0) = max(a, b) = max(a, max(b, 0))
\end{gather*}
$$
现在假设$min(min(a, b), c) = min(a, min(b, c))$和$max(max(a, b), c) = max(a, max(b, c))$，则有
$$
\begin{gather*}
min(min(a^+, b^+), c^+) = min(min(a, b)^+, c^+) = min(min(a, b), c)^+ = min(a, min(b, c))^+ = min(a^+, min(b, c)^+) = min(a^+, min(b^+, c^+)) \\
max(max(a^+, b^+), c^+) = max(max(a, b)^+, c^+) = max(max(a, b), c)^+ = max(a, max(b, c))^+ = max(a^+, max(b, c)^+) = max(a^+, max(b^+, c^+))
\end{gather*}
$$

```lean
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
```

**命题：**
$$
\begin{gather*}
min(min(a, b), min(c, d)) = min(min(a, c), min(b, d)) \\
max(max(a, b), max(c, d)) = max(max(a, c), max(b, d))
\end{gather*}
$$

**证明：**应用结合律和交换律可得。

```lean
theorem min_min_min_comm : min (min a b) (min c d) = min (min a c) (min b d) := calc
  min (min a b) (min c d) = min (min a (min b c)) d := by repeat rw[min_asso]
  _                       = min (min a (min c b)) d := by rw[@min_comm b c]
  _                       = min (min a c) (min b d) := by repeat rw[min_asso]

theorem max_max_max_comm : max (max a b) (max c d) = max (max a c) (max b d) := calc
  max (max a b) (max c d) = max (max a (max b c)) d := by repeat rw[max_asso]
  _                       = max (max a (max c b)) d := by rw[@max_comm b c]
  _                       = max (max a c) (max b d) := by repeat rw[max_asso]
```

**命题：**（吸收律）
$$
\begin{gather*}
min(a, max(a, b)) = a \\
max(a, min(a, b)) = a
\end{gather*}
$$

**证明：**$a = 0$时有$min(0, max(0, b)) = 0$和$max(0, min(0, b)) = min(0, b) = 0$，$b = 0$时有$min(a, max(a, 0)) = min(a, a) = a$和$max(a, min(a, 0)) = max(a, 0) = a$。现在假设$min(a, max(a, b)) = a$和$max(a, min(a, b)) = a$，则有
$$
\begin{gather*}
min(a^+, max(a^+, b^+)) = min(a^+, max(a, b)^+) = min(a, max(a, b))^+ = a^+ \\
max(a^+, min(a^+, b^+)) = max(a^+, min(a, b)^+) = max(a, min(a, b))^+ = a^+
\end{gather*}
$$

```lean
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
```

由吸收律可以推出幂等律：
$$
\begin{gather*}
min(a, a) = min(a, max(a, min(a, b))) = a \\
max(a, a) = max(a, min(a, max(a, b))) = a
\end{gather*}
$$

```lean
theorem min_idem_alt {a b : N} : min a a = a := calc
  min a a = min a (max a (min a b)) := by rw[max_min_abso]
  _       = a                       := by rw[min_max_abso]

theorem max_idem_alt {a b : N} : max a a = a := calc
  max a a = max a (min a (max a b)) := by rw[min_max_abso]
  _       = a                       := by rw[max_min_abso]
```

**命题：**（分配律）
$$
\begin{gather*}
min(a, max(b, c)) = max(min(a, b), min(a, c)) \\
max(a, min(b, c)) = min(max(a, b), max(a, c))
\end{gather*}
$$

**证明：**
$$
\begin{gather*}
min(0, max(b, c)) = 0 = max(0, 0) = max(min(0, b), min(0, c)) \\
min(a, max(0, c)) = min(a, c) = max(0, min(a, c)) = max(min(a, 0), min(a, c)) \\
min(a, max(b, 0)) = min(a, b) = max(min(a, b), 0) = max(min(a, b), min(a, 0)) \\
\\
max(0, min(b, c)) = min(b, c) = min(max(0, b), max(0, c)) \\
max(a, min(0, c)) = max(a, 0) = a = min(a, max(a, c)) = min(max(a, 0), max(a, c)) \\
max(a, min(b, 0)) = max(a, 0) = a = min(max(a, b), a) = min(max(a, b), max(a, 0))
\end{gather*}
$$
现在假设
$$
\begin{gather*}
min(a, max(b, c)) = max(min(a, b), min(a, c)) \\
max(a, min(b, c)) = min(max(a, b), max(a, c))
\end{gather*}
$$
则有
$$
\begin{gather*}
min(a^+, max(b^+, c^+)) = min(a^+, max(b, c)^+) = min(a, max(b, c))^+ = max(min(a, b), min(a, c))^+ = max(min(a, b)^+, min(a, c)^+) = max(min(a^+, b^+), min(a^+, c^+)) \\
max(a^+, min(b^+, c^+)) = max(a^+, min(b, c)^+) = max(a, min(b, c))^+ = min(max(a, b), max(a, c))^+ = min(max(a, b)^+, max(a, c)^+) = min(max(a^+, b^+), max(a^+, c^+))
\end{gather*}
$$

```lean
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
```

**命题：**（最小值、最大值和加法）<br/>
1. $min(a + b, a) = min(a, a + b) = a$。
2. $min(c + a, c + b) = c + min(a, b)$。
3. $max(a + b, a) = max(a, a + b) = a + b$。
4. $max(c + a, c + b) = c + max(a, b)$。

**证明：**<br/>
1. 先证明$min(a + b, a) = a$。对$a$归纳。$a = 0$时有$min(b, 0) = 0$。现在假设$min(a + b, a) = a$，则有$min(a^+ + b, a^+) = min((a + b)^+, a^+) = min(a + b, a)^+ = a^+$。$min(a, a + b) = a$由$min$的交换律可得。
2. 对$c$归纳。$c = 0$时显然有$min(0 + a, 0 + b) = 0 + min(a, b)$。现在假设$min(c + a, c + b) = c + min(a, b)$，则有$min(c^+ + a, c^+ + b) = min((c + a)^+, (c + b)^+) = min(c + a, c + b)^+ = (c + min(a, b))^+ = c^+ + min(a, b)$。
3. 先证明$max(a + b, a) = a + b$。对$a$归纳。$a = 0$时有$max(b, 0) = b$。现在假设$max(a + b, a) = a + b$，则有$max(a^+ + b, a^+) = max((a + b)^+, a^+) = max(a + b, a)^+ = a^+ + b$。$max(a, a + b) = a + b$由$max$的交换律可得。
4. 对$c$归纳。$c = 0$时显然有$max(0 + a, 0 + b) = 0 + max(a, b)$。现在假设$max(c + a, c + b) = c + max(a, b)$，则有$max(c^+ + a, c^+ + b) = max((c + a)^+, (c + b)^+) = max(c + a, c + b)^+ = (c + max(a, b))^+ = c^+ + max(a, b)$。

```lean
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
```

**命题：**（最小值、最大值和序）<br/>
1. 若$a \le b$，则$min(a, b) = a$，否则$min(a, b) = b$。
2. 若$a \ge b$，则$max(a, b) = a$，否则$max(a, b) = b$。
3. $min(a, b) \le a$且$min(a, b) \le b$。
4. $a \le max(a, b)$且$b \le max(a, b)$。
5. $min(a, b) \le max(a, b)$。
6. $c \le min(a, b) \iff c ≤ a ∧ c ≤ b$。
7. $c < min(a, b) \iff c < a ∧ c < b$。
8. $max(a, b) \le c \iff a ≤ c ∧ b ≤ c$。
9. $max(a, b) < c \iff a < c ∧ b < c$。
10. 当$a \le c$且$b \le d$时有$min(a, b) \le min(c, d)$和$max(a, b) \le max(c, d)$。

**证明：**<br/>
1. 先证前半部分，$a = 0$时有$min(0, b) = 0$。现在假设$a \le b$时有$min(a, b) = a$，则$a^+ \le b^+$时有$a \le b$，由假设有$min(a, b) = a$，即有$min(a^+, b^+) = min(a, b)^+ = a^+$。后半部分由$min$的交换律可得。
2. 先证前半部分，$b = 0$时有$max(a, 0) = a$。现在假设$a \ge b$时有$max(a, b) = a$，则$a^+ \ge b^+$时有$a \ge b$，由假设有$max(a, b) = a$，即有$max(a^+, b^+) = max(a, b)^+ = a^+$。后半部分由$max$的交换律可得。
3. $a \le b$时$min(a, b) = a$，有$a \le a$和$a \le b$。$b \le a$时$min(a, b) = b$，有$b \le a$和$b \le b$。
4. $a \le b$时$max(a, b) = b$，有$a \le b$和$b \le b$。$b \le a$时$max(a, b) = a$，有$a \le a$和$b \le a$。
5. $min(a, b) \le a \le max(a, b)$。
6. （$\implies$）$c \le min(a, b) \le a$且$c \le min(a, b) \le b$。<br/>
（$\impliedby$）$a \le b$时有$c \le min(a, b) = a$，$b \le a$时有$c \le min(a, b) = b$。
7. $c^+ \le min(a, b) \iff c^+ ≤ a ∧ c^+ ≤ b$。
8. （$\implies$）$a \le max(a, b) \le c$且$b \le max(a, b) \le c$。<br/>
（$\impliedby$）$a \le b$时有$max(a, b) = b \le c$，$b \le a$时有$max(a, b) = a \le c$。
9. $max(a, b)^+ = max(a^+, b^+) \le c \iff a^+ ≤ c ∧ b^+ ≤ c$。
10. $c \le d$时有$min(a, b) \le a \le c = min(c, d)$，$d \le c$时有$min(a, b) \le b \le d = min(c, d)$。<br/>
$a \le b$时有$max(a, b) = b \le d \le max(c, d)$，$b \le a$时有$max(a, b) = a \le c \le max(c, d)$。

```lean
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
```

以下便是最小值和最大值通常的定义：
$$
min(a, b) =
\begin{cases}
a & \text{如果} a \le b \\
b & \text{如果} a > b
\end{cases}
\quad
max(a, b) =
\begin{cases}
b & \text{如果} a \le b \\
a & \text{如果} a > b
\end{cases}
$$

在lean中是用序关系定义最小值和最大值的：

```lean
def minOfLe [LE α] [DecidableRel (@LE.le α _)] : Min α where
  min x y := ite (LE.le x y) x y

def maxOfLe [LE α] [DecidableRel (@LE.le α _)] : Max α where
  max x y := ite (LE.le x y) y x

instance : Min Nat := minOfLe

instance : Max Nat := maxOfLe
```

**命题：**（最小值、最大值和乘法）
$$
\begin{gather*}
min(ca, cb) = c \times min(a, b) \\
max(ca, cb) = c \times max(a, b)
\end{gather*}
$$

**证明：**$c = 0$时有$min(0, 0) = max(0, 0) = 0$。$c > 0$时，$a \le b$时有$ca \le cb$，从而有$min(ca, cb) = ca = c \times min(a, b)$和$max(ca, cb) = cb = c \times max(a, b)$；$b \le a$时有$cb \le ca$，从而有$min(ca, cb) = cb = c \times min(a, b)$和$max(ca, cb) = ca = c \times max(a, b)$。

```lean
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
```

**命题：**若函数$f : \N \times \N \to \N$对任意的自然数$a$和$b$都满足$f(a, b) = f(b, a)$，则$f(min(a, b), max(a, b)) = f(a, b)$。

**证明：**$a \le b$时有$min(a, b) = a$和$max(a, b) = b$，于是$f(min(a, b), max(a, b)) = f(a, b)$。$b \le a$时有$min(a, b) = b$和$max(a, b) = a$，于是$f(min(a, b), max(a, b)) = f(b, a) = f(a, b)$。

```lean
theorem comm_fun_min_max {a b : N} {f : N → N → N}
  (h : ∀ a, ∀ b, f a b = f b a) :
  f (min a b) (max a b) = f a b := by
  apply le_total.elim
  . intro hle
    rw[min_eq_left hle, max_eq_right hle]
  . intro hge
    rw[min_eq_right hge, max_eq_left hge, h a b]
```

作为推论，我们有$min(a, b) + max(a, b) = a + b$和$min(a, b) \times max(a, b) = ab$。

```lean
@[simp]
theorem min_add_max {a b : N} : min a b + max a b = a + b :=
  comm_fun_min_max add_comm

@[simp]
theorem min_mul_max {a b : N} : min a b * max a b = a * b :=
  comm_fun_min_max mul_comm
```

# 整除

定义$a$整除$b$（记为$a \mid b$）为存在自然数$c$使得$ac = b$（比较$a \le b$等价于存在自然数$c$使得$a + c = b$）。

```lean
instance : Dvd N where
  dvd a b := ∃ c, a * c = b
```

**命题：**<br/>
1. （自反性）对任意自然数$a$都有$a \mid a$。
2. 对任意自然数$a$都有$a \mid 0$。
3. 对任意自然数$a$都有$1 \mid a$。
4. 若$0 \mid a$，则$a = 0$。
5. 若$a \mid b$且$b > 0$，则$a > 0$。
6. 若$a \mid 1$，则$a = 1$。
7. （传递性）若$a \mid b$且$b \mid c$，则$a \mid c$。
8. 若$a \mid b$且$b > 0$，则$a \le b$。
9. （反对称性）若$a \mid b$且$b \mid a$，则$a = b$。
10. 若$a \mid b$且$a \mid c$，则$a \mid b + c$。
11. 若$a \mid b$，则对任意自然数$c$都有$a \mid bc$。
12. 若$ac^+ \mid bc^+$，则$a \mid b$。
13. 若$a \mid b$且$a \mid c$，则$a \mid mb + nc$。

**证明：**<br/>
1. $a \times 1 = a$。
2. $a \times 0 = 0$。
3. $1 \times a = a$。
4. 由$0 \mid a$有$0 \times c = a$，又$0 \times c = 0$，于是$a = 0$。
5. 若$a = 0$，则由$0 \mid b$有$b = 0$，与$b > 0$矛盾，因此$a > 0$。
6. 由$a \mid 1$有$ac = 1$，即有$a = 1$。
7. 由$a \mid b$和$b \mid c$有$ac_{1} = b$和$bc_{2} = c$，前式代入后式得$a(c_{1}c_{2}) = c$。
8. 由$a \mid b$有$ac = b$。若$c = 0$，则$b = 0$，矛盾。因此$c > 0$，则有$ac = a + ac^{-} = b$，即有$a \le b$。
9. 若$a = 0$，则有$0 \mid b$，从而$b = 0 = a$。类似地，从$b = 0$也能推出$a = 0 = b$。若$ab > 0$，则由$a \mid b$且$b \mid a$有$a \le b$且$b \le a$，于是由$\le$的反对称性有$a = b$。
10. 由$a \mid b$和$a \mid c$有$ac_{1} = b$和$ac_{2} = c$，两式相加有$a(c_{1} + c_{2}) = b + c$。
11. 由$a \mid b$有$ad = b$，等式两边乘$c$有$a(dc) = bc$。
12. 由$ac^+ \mid bc^+$有$ac^{+}d = bc^{+}$，等式两边消去$c^+$得$ad = b$。
13. 由$a \mid b$右边乘$m$和$a \mid c$右边乘$n$有$a \mid mb$和$a \mid nc$，两式右边相加有$a \mid mb + nc$。

```lean
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
```

# 带余除法、绝对差

**命题：**（欧几里得算法）设$n$为一自然数，$q$为一正自然数，那么唯一存在自然数$m$和$r$使得$0 \le r < q$并且$n = mq + r$。

我们暂不讨论如何计算出$m$和$r$，只证明其存在性和唯一性。

**证明：**（存在性）对$n$归纳。$n = 0$时，取$m = 0$和$r = 0$即满足$0 < q$且$0 = 0 \times q + 0$。现在假设对$n$有$m$和$r$满足$0 \le r < q$和$n = mq + r$，则有$n^+ = mq + r^+$。$r^+ > q$不成立，因为不存在$q$使得$r < q < r^+$。若$r^+ = q$，则$n^+ = mq + r^+ = mq + q = m^{+}q + 0$，且$0 < q$，$m^+$和$0$即是所求的数。若$r^+ < q$，则$m$和$r^+$即是所求的数。

```lean
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
```

在证明唯一性之前，我们先定义自然数$a$和$b$的绝对差$\lvert a - b \rvert$：
$$
\begin{alignat*}{2}
\lvert 0 &- b\rvert& &:= b \\
\lvert a &- 0\rvert& &:= a \\
\lvert a^+ &- b^+\rvert& &:= \lvert a - b \rvert
\end{alignat*}
$$

```lean
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
```

**命题：**<br/>
1. $\lvert a - a\rvert = 0$。
2. $\lvert a - b\rvert = 0 \iff a = b$。

**证明：**<br/>
1. 对$a$归纳。$a = 0$时有$\lvert 0 - 0\rvert = 0$。现在假设$\lvert a - a\rvert = 0$，则$\lvert a^{+} - a^{+}\rvert = \lvert a - a\rvert = 0$。
2. $a = b = 0$时显然有$\lvert 0 - 0\rvert = 0$和$0 = 0$。现在假设$\lvert a - b\rvert = 0 \iff a = b$，则$\lvert a^{+} - b^{+}\rvert = 0 \iff \lvert a - b\rvert = 0 \iff a = b \iff a^{+} = b^{+}$。

```lean
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
```

**命题：**若$a \ge b$，则$\lvert a - b \rvert + b = a$。

**证明：**$b = 0$时有$\lvert a - 0 \rvert + 0 = a$。现在假设$\lvert a - b \rvert + b = a$，则$\lvert a^+ - b^+ \rvert + b^+ = \lvert a - b \rvert + b + 1 = a$。

```lean
theorem abssub_add_cancel {a b : N} (h : a ≥ b) : (abssub a b) + b = a := by
  match a, b with
  | _, _0      => simp
  | S a', S b' => simp[-add_comm, abssub_add_cancel (pred_le_pred h)]
```

假设已经有了减法，我们就有：
$$
\lvert a - b \rvert =
\begin{cases}
a - b & \text{如果} a \ge b \\
b - a & \text{如果} a < b
\end{cases}
$$

**命题：**$\lvert (a + c) - (b + c)\rvert = \lvert a - b\rvert$。

**证明：**对$c$归纳。$c = 0$时显然有$\lvert (a + 0) - (b + 0)\rvert = \lvert a - b\rvert$。现在假设$\lvert (a + c) - (b + c)\rvert = \lvert a - b\rvert$，则有$\lvert (a + c^{+}) - (b + c^{+})\rvert = \lvert (a + c)^{+} - (b + c)^{+}\rvert = \lvert (a + c) - (b + c)\rvert = \lvert a - b\rvert$。

```lean
@[simp]
theorem add_abssub_add_right {a b c : N} : abssub (a + c) (b + c) = abssub a b := by
  induction c with
  | _0      => rfl
  | S c' ih => simp; exact ih

@[simp]
theorem add_abssub_add_left {a b c : N} : abssub (c + a) (c + b) = abssub a b := by
  rw[add_comm c a, add_comm c b]
  exact add_abssub_add_right
```

**命题：**$\lvert a - b\rvert = \lvert b - a\rvert$。

**证明：**$\lvert a - 0\rvert = \lvert 0 - a\rvert = a$。现在假设$\lvert a - b\rvert = \lvert b - a\rvert$，则有$\lvert a^{+} - b^{+}\rvert = \lvert a - b\rvert = \lvert b - a\rvert = \lvert b^{+} - a^{+}\rvert$。

```lean
@[simp]
theorem abssub_comm {a b : N} : abssub a b = abssub b a := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => exact @abssub_comm a' b'
```

**命题：**<br/>
1. $\lvert a - b\rvert \le max(a, b)$。
2. 若$a \le c$且$b \le c$，则$\lvert a - b\rvert \le c$。
3. 若$a < c$且$b < c$，则$\lvert a - b\rvert < c$。

**证明：**<br/>
1. $a = 0$时有$\lvert 0 - b\rvert = b = max(0, b)$，有$b \le b$。$b = 0$时有类似结论。现在假设$\lvert a - b\rvert \le max(a, b)$，则$\lvert a^{+} - b^{+}\rvert = \lvert a - b\rvert \le max(a, b) \le max(a, b)^+ = max(a^+, b^+)$。
2. $\lvert a - b\rvert \le max(a, b) \le c$。
3. $\lvert a - b\rvert \le max(a, b) < c$。

```lean
theorem abssub_le_max {a b : N} : abssub a b ≤ max a b := by
  match a, b with
  | _0, _      => simp; apply le_refl
  | _, _0      => simp; apply le_refl
  | S a', S b' => simp; exact le_trans abssub_le_max (le_succ (max a' b'))

theorem abssub_le_of_le_of_le {a b c : N} (h1 : a ≤ c) (h2 : b ≤ c) : abssub a b ≤ c :=
  le_trans abssub_le_max (max_le.mpr ⟨h1, h2⟩)

theorem abssub_lt_of_lt_of_lt {a b c : N} (h1 : a < c) (h2 : b < c) : abssub a b < c :=
  le_trans abssub_le_max (max_lt.mpr ⟨h1, h2⟩)
```

**命题：**若$a + c = b + d$，则$\lvert a - b\rvert = \lvert c - d\rvert$。

**证明：**

$a = c = 0 \iff b = d = 0$。

$a = b = 0$时，有$c = d$，从而$\lvert 0 - 0 \rvert = 0 = \lvert c - d \rvert$。$c = d = 0$时，有$a = b$，从而$\lvert a - b \rvert = 0 = \lvert 0 - 0 \rvert$。

$a = d = 0$时，有$c = b$，从而$\lvert 0 - b \rvert = b = c = \lvert c - 0 \rvert$。$b = c = 0$时，有$a = d$，从而$\lvert a - 0 \rvert = a = d = \lvert 0 - d \rvert$。

只有一个自然数为$0$时，例如$a = 0$时，固定$b$，假设$\lvert 0 - b\rvert = \lvert c - d\rvert$，则有$\lvert a - b\rvert = \lvert c - d\rvert = \lvert c^+ - d^+ \rvert$。其它数为$0$时也有类似结论。

最后，当$abcd \ne 0$时，假设$\lvert a - b\rvert = \lvert c - d\rvert$，则有$\lvert a^+ - b^+ \rvert = \lvert a - b \rvert = \lvert c - d \rvert = \lvert c^+ - d^+ \rvert$。

```lean
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
```

**命题：**若$a \le b$且$c \le d$，则$\lvert a - b\rvert + \lvert c - d\rvert = \lvert (a + c) - (b + d)\rvert$。

**证明：**

$a = c = 0$时有$\lvert 0 - b\rvert + \lvert 0 - d\rvert = b + d = \lvert (0 + 0) - (b + d)\rvert$。

$a$和$c$当中只有$a = 0$时，固定$b$，假设有$\lvert 0 - b\rvert + \lvert c - d\rvert = b + \lvert c - d\rvert = \lvert c - (b + d)\rvert$，则$\lvert 0 - b\rvert + \lvert c^+ - d^+\rvert = b + \lvert c^+ - d^+\rvert = b + \lvert c - d\rvert = \lvert c - (b + d)\rvert = \lvert c^+ - (b + d^+)\rvert$。类似地在$c = 0$时可以证明$\lvert a - b\rvert + \lvert 0 - d\rvert = \lvert (a + 0) - (b + d)\rvert$。

$abcd \ne 0$时，假设有$\lvert a - b\rvert + \lvert c - d\rvert = \lvert (a + c) - (b + d)\rvert$，则$\lvert a^+ - b^+ \rvert + \lvert c^+ - d^+ \rvert = \lvert a - b\rvert + \lvert c - d\rvert = \lvert (a + c) - (b + d)\rvert = \lvert (a^{+} + c^{+}) - (b^{+} + d^{+})\rvert$。

```lean
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
```

**命题：**$c\lvert a - b\rvert = \lvert ca - cb\rvert$。

**证明：**

$c = 0$时等式两边都等于$0$。$a = 0$时有$c\lvert 0 - b\rvert = cb = \lvert c \times 0 - cb\rvert$，$b = 0$时有$c\lvert a - 0\rvert = ca = \lvert ca - c \times 0 \rvert$。

现在假设$c\lvert a - b\rvert = \lvert ca - cb\rvert$。当$c^+ = 1$时，显然有$\lvert a - b\rvert = \lvert a - b\rvert$。当$c^+ > 1$时，有$c > 0$，若$a \le b$则有$ca \le cb$，若$a \ge b$则有$ca \ge cb$。于是$c^{+}\lvert a - b\rvert = c\lvert a - b\rvert + \lvert a - b\rvert = \lvert ca - cb\rvert + \lvert a - b\rvert = \lvert c^{+}a - c^{+}b\rvert$。

```lean
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
```

现在可以开始证明欧几里得算法中$m$和$r$的唯一性了：假设$n = m_{1}q + r_{1} = m_{2}q + r_{2}$，$0 \le r_{1} < q$，$0 \le r_{2} < q$，则有$q\lvert m_{1} - m_{2}\rvert = \lvert m_{1}q - m_{2}q\rvert = \lvert r_{1} - r_{2}\rvert$，从而$q \mid \lvert r_{1} - r_{2}\rvert$；同时也有$\lvert r_{1} - r_{2}\rvert < q$。若$\lvert r_{1} - r_{2}\rvert > 0$，就有$q \le \lvert r_{1} - r_{2}\rvert$，与$\lvert r_{1} - r_{2}\rvert < q$矛盾，因此$\lvert r_{1} - r_{2}\rvert = 0$，从而$r_{1} = r_{2}$，由此得出$m_{1} = m_{2}$。

```lean
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
```

对于绝对差，我们还可以证明：

**命题：**（平方绝对差）$\lvert a^2 - b^2 \rvert = (a + b) \lvert a - b \rvert$。

**证明：**$a = 0$时有$\lvert 0^2 - b^2 \rvert = b^2 = (0 + b) \lvert 0 - b \rvert$，$b = 0$时有$\lvert a^2 - 0^2 \rvert = a^2 = (a + 0) \lvert a - 0 \rvert$。现在假设$\lvert a^2 - b^2 \rvert = (a + b) \lvert a - b \rvert$。若$a \le b$则有$2a \le 2b$和$a^2 \le b^2$，反之亦然。于是
$$
\begin{split}
\lvert (a + 1)^2 - (b + 1)^2 \rvert &= \lvert (a^2 + 2a + 1) - (b^2 + 2b + 1) \rvert \\
&= \lvert (a^2 + 2a) - (b^2 + 2b) \rvert \\
&= \lvert a^2 - b^2 \rvert + 2\lvert a - b \rvert \\
&= (a + b + 2)\lvert a - b \rvert \\
&= (a + 1 + b + 1)\lvert (a + 1) - (b + 1) \rvert
\end{split}
$$

```lean
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
```

# 截断减法

定义截断减法$a \dotminus b$为：
$$
\begin{alignat*}{2}
a &\dotminus 0& &:= a \\
a &\dotminus b&^+ &:= (a \dotminus b)^-
\end{alignat*}
$$

```lean
def monus (a b : N) : N :=
  match b with
  | _0   => a
  | S b' => P (monus a b')

@[simp]
theorem monus_zero : monus a _0 = a := by
  rfl

theorem monus_succ : monus a (S b) = P (monus a b) := by
  rfl
```

**命题：**<br/>
1. $0 \dotminus a = 0$。
2. $a^+ \dotminus b^+ = a \dotminus b$。

**证明：**<br/>
1. 对$a$归纳。$a = 0$时有$0 \dotminus 0 = 0$。现在假设$0 \dotminus a = 0$，则$0 \dotminus a^+ = (0 \dotminus a)^- = 0^- = 0$。
2. 对$b$归纳。$b = 0$时有$a^+ \dotminus 1 = (a^+ \dotminus 0)^- = (a^+)^- = a$。现在假设$a^+ \dotminus b^+ = a \dotminus b$，则$a^+ \dotminus (b^+)^+ = (a^+ \dotminus b^+)^- = (a \dotminus b)^- = a \dotminus b^+$。

```lean
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
```

这意味着我们可以将$a \dotminus b$定义为：
$$
\begin{alignat*}{2}
a &\dotminus 0& &:= a \\
0 &\dotminus b& &:= 0 \\
a^+ &\dotminus b&^+ &:= a \dotminus b
\end{alignat*}
$$

**命题：**$a \dotminus a = 0$。

**证明：**对$a$归纳。$a = 0$时有$0 \dotminus 0 = 0$。现在假设$a \dotminus a = 0$，则有$a^+ \dotminus a^+ = a \dotminus a = 0$

```lean
@[simp]
theorem monus_self : monus a a = _0 := by
  induction a with
  | _0      => rfl
  | S a' ih => simp[ih]
```

**命题：**<br/>
1. $a + (b \dotminus a) = b + (a \dotminus b)$。
2. $(a \dotminus b) \dotminus c = a \dotminus (b + c)$。

**证明：**<br/>
1. $a = 0$时有$0 + (b \dotminus 0) = b = b + (0 \dotminus b)$，$b = 0$时有$a + (0 \dotminus a) = a = 0 + (a \dotminus 0)$。现在假设$a + (b \dotminus a) = b + (a \dotminus b)$，则$a^{+} + (b^{+} \dotminus a^{+}) = a^{+} + (b \dotminus a) = (a + (b \dotminus a))^{+} = (b + (a \dotminus b))^{+} = b^{+} + (a^{+} \dotminus b^{+})$。
2. 对$c$归纳。$c = 0$时有$(a \dotminus b) \dotminus 0 = a \dotminus b = a \dotminus (b + 0)$。现在假设$(a \dotminus b) \dotminus c = a \dotminus (b + c)$，则$(a \dotminus b) \dotminus c^{+} = ((a \dotminus b) \dotminus c)^{-} = (a \dotminus (b + c))^{-} = a \dotminus (b + c)^{+} = a \dotminus (b + c^{+})$。

```lean
theorem add_monus (a b : N) : a + monus b a = b + monus a b := by
  match a, b with
  | _0, _      => simp
  | _, _0      => simp
  | S a', S b' => simp[add_monus a' b']

theorem monus_monus : monus (monus a b) c = monus a (b + c) := by
  induction c with
  | _0      => rfl
  | S c' ih => rw[monus_succ, add_succ, monus_succ, ih]
```

**命题：**<br/>
1. $\lvert a - b\rvert = a \dotminus b + b \dotminus a$。
2. $max(a, b) = a + (b \dotminus a)$。

**证明：**<br/>
1. $a = 0$时有$\lvert 0 - b\rvert = b = 0 \dotminus b + b \dotminus 0$，$b = 0$时有$\lvert a - 0\rvert = a = a \dotminus 0 + 0 \dotminus a$。现在假设$\lvert a - b\rvert = a \dotminus b + b \dotminus a$，则$\lvert a^{+} - b^{+}\rvert = \lvert a - b\rvert = a \dotminus b + b \dotminus a = a^{+} \dotminus b^{+} + b^{+} \dotminus a^{+}$。
2. $a = 0$时有$max(0, b) = b = 0 + (b \dotminus 0)$，$b = 0$时有$max(a, 0) = a = a + (0 \dotminus a)$。现在假设$max(a, b) = a + (b \dotminus a)$，则$max(a^+, b^+) = max(a, b)^+ = (a + (b \dotminus a))^+ = a^+ + (b^+ \dotminus a^+)$。

```lean
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
```

**命题：**<br/>
1. $a \le b \iff a \dotminus b = 0$。
2. $a > b \iff a \dotminus b > 0$。
3. 若$a \ge b$，则$(a \dotminus b) + b = a$。
4. 若$a \ge b$，则$a^+ \dotminus b = (a \dotminus b)^+$。
5. $a \dotminus b \le a$。

**证明：**<br/>
1. （$\implies$）$a = 0$时有$0 \dotminus b = 0$。现在假设当$a \le b$时有$a \dotminus b = 0$，则$a^+ \le b^+$时有$a \le b$，由假设有$a \dotminus b = 0$，从而$a^+ \dotminus b^+ = 0$。<br/>
（$\impliedby$）$a = 0$时有$0 \le b$。现在假设当$a \dotminus b = 0$时有$a \le b$，则$a^+ \dotminus b^+ = 0$时有$a \dotminus b = 0$，由假设有$a \le b$，从而$a^+ \le b^+$。
2. （$\implies$）$b = 0$时有$a \dotminus 0 = a > 0$。现在假设当$a > b$时有$a \dotminus b > 0$，则$a^+ > b^+$时有$a > b$，由假设有$a \dotminus b > 0$，从而$a^+ \dotminus b^+ = a \dotminus b > 0$。<br/>
（$\impliedby$）$a = 0$时$0 \dotminus b = 0$。$b = 0$时有$a \dotminus 0 = a$，从而$a = a \dotminus b > 0$。现在假设当$a \dotminus b > 0$时有$a > b$，则当$a^+ \dotminus b^+ > 0$时由$a^+ \dotminus b^+ = a \dotminus b$有$a \dotminus b > 0$，由假设有$a > b$，从而$a^+ > b^+$。
3. $b = 0$时有$(a \dotminus 0) + 0 = a$。现在假设$(a \dotminus b) + b = a$，则$(a^+ \dotminus b^+) + b^+ = (a \dotminus b) + b + 1 = a^+$。
4. $b = 0$时有$a^+ \dotminus 0 = a^+ = (a \dotminus 0)^+$。现在假设当$a \ge b$时有$a^+ \dotminus b = (a \dotminus b)^+$，则$a^+ \ge b^+$时有$a \ge b$，由假设有$a^+ \dotminus b = (a \dotminus b)^+$，从而$(a^+)^+ \dotminus b^+ = a^+ \dotminus b = (a \dotminus b)^+ = (a^+ \dotminus b^+)^+$。
5. $a = 0$时有$0 \dotminus b = 0 \le 0$，$b = 0$时有$a \dotminus 0 = a \le a$。现在假设$a \dotminus b \le a$，则$a^+ \dotminus b^+ = a \dotminus b \le a \le a^+$。

```lean
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
```

假设已经有了减法，我们就有：
$$
a \dotminus b =
\begin{cases}
a - b & \text{如果} a \ge b \\
0 & \text{如果} a < b
\end{cases}
$$

**命题：**$min(a, b) = a \dotminus (a \dotminus b)$。

**证明：**

当$a \le b$时，左边$min(a, b) = a$，右边$a \dotminus (a \dotminus b) = a \dotminus 0 = a$，等式两边相等。

当$a \ge b$时，左边$min(a, b) = b$。

现在证明当$a \ge b$时有$a \dotminus (a \dotminus b) = b$：$b = 0$时，有$a \dotminus (a \dotminus 0) = a \dotminus a = 0$。现在假设当$a \ge b$时有$a \dotminus (a \dotminus b) = b$，则$a^+ \ge b^+$时有$a \ge b$，由假设有$a \dotminus (a \dotminus b) = b$，又由于$a \dotminus b \le a$，有$a^+ \dotminus (a \dotminus b) = b^+$，从而$a^+ \dotminus (a^+ \dotminus b^+) = a^+ \dotminus (a \dotminus b) = b^+$。

因此，我们有等式右边$a \dotminus (a \dotminus b) = b$，等式两边相等。

```lean
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
```

**命题：**$(a + c) \dotminus (b + c) = a \dotminus b$。

**证明：**对$c$归纳。$c = 0$时显然有$(a + 0) \dotminus (b + 0) = a \dotminus b$。现在假设$(a + c) \dotminus (b + c) = a \dotminus b$，则$(a + c^+) \dotminus (b + c^+) = (a + c)^+ \dotminus (b + c)^+ = (a + c) \dotminus (b + c) = a \dotminus b$。

```lean
@[simp]
theorem add_monus_add_right {a b c : N} : monus (a + c) (b + c) = monus a b := by
  induction c with
  | _0      => rfl
  | S c' ih => simp; exact ih

@[simp]
theorem add_monus_add_left {a b c : N} : monus (c + a) (c + b) = monus a b := by
  rw[add_comm c a, add_comm c b]
  exact add_monus_add_right
```

**命题：**若$a \ge b$且$c \ge d$，则$(a \dotminus b) + (c \dotminus d) = (a + c) \dotminus (b + d)$。

**证明：**

$b = d = 0$时，$(a \dotminus 0) + (c \dotminus 0) = a + c = (a + c) \dotminus (0 + 0)$。

$b$和$d$当中只有$b = 0$时，固定$a$，假设有$(a \dotminus 0) + (c \dotminus d) = a + (c \dotminus d) = (a + c) \dotminus d$，则$(a \dotminus 0) + (c^{+} \dotminus d^{+}) = a + (c^{+} \dotminus d^{+}) = a + (c \dotminus d) = (a + c) \dotminus d = (a + c^{+}) \dotminus d^{+}$。类似地当$d = 0$时也可证明$(a \dotminus b) + (c \dotminus 0) = (a + c) \dotminus (b + 0)$。

$abcd \ne 0$时，假设$(a \dotminus b) + (c \dotminus d) = (a + c) \dotminus (b + d)$，则$(a^{+} \dotminus b^{+}) + (c^{+} \dotminus d^{+}) = (a \dotminus b) + (c \dotminus d) = (a + c) \dotminus (b + d) = (a^{+} + c^{+}) \dotminus (b^{+} + d^{+})$。

```lean
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
```

**命题：**$c(a \dotminus b) = ca \dotminus cb$。

**证明：**

$c = 0$时等式两边都等于$0$。$a = 0$时有$c(0 \dotminus b) = 0 = c \times 0 \dotminus cb$，$b = 0$时有$c(a \dotminus 0) = ca = ca \dotminus c \times b$。

现在假设$c(a \dotminus b) = ca \dotminus cb$。当$c^+ = 1$时，显然有$a \dotminus b = a \dotminus b$。当$c^+ > 1$时，有$c > 0$，若$a \le b$则有$c^{+}a \le c^{+}b$，于是$c^{+}(a \dotminus b) = 0 = c^{+}a \dotminus c^{+}b$；若$a \ge b$则有$ca \ge cb$，于是$c^{+}(a \dotminus b) = c(a \dotminus b) + a \dotminus b = ca \dotminus cb + a \dotminus b = c^{+}a \dotminus c^{+}b$。

```lean
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
```

**命题：**（平方截断差）$a^2 \dotminus b^2 = (a + b)(a \dotminus b)$。

**证明：**

若$a \le b$，则有$a^2 \le b^2$，于是$a^2 \dotminus b^2 = 0 = (a + b)(a \dotminus b)$。

若$a \ge b$，$b = 0$时显然有$a^2 \dotminus 0^2 = a^2 = (a + 0)(a \dotminus 0)$，现在假设$a^2 \dotminus b^2 = (a + b)(a \dotminus b)$，由于$a \ge b$时有$2a \ge 2b$和$a^2 \ge b^2$，于是
$$
\begin{split}
(a + 1)^2 \dotminus (b + 1)^2 &= (a^2 + 2a + 1) \dotminus (b^2 + 2b + 1) \\
&= (a^2 + 2a) \dotminus (b^2 + 2b) \\
&= a^2 \dotminus b^2 + 2(a \dotminus b) \\
&= (a + b + 2)(a \dotminus b) \\
&= (a + 1 + b + 1)((a + 1) \dotminus (b + 1))
\end{split}
$$

```lean
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
```

# 同构

我们建立一个从`N`（$\N$）到`Nat`（$\overline{\N}$）的映射$H$：
$$
\begin{align*}
H(0) &:= \overline{0} \\
H(a^+) &:= H(a)^+
\end{align*}
$$

```lean
def N.H : N → Nat
| _0  => 0
| S a => (H a).succ

@[simp]
theorem iso_zero : H _0 = 0 := by
  rfl

@[simp]
theorem iso_succ : H (S a) = (H a).succ := by
  rfl
```

$H$是唯一的：

```lean
theorem H_unique
  (f : N → Nat)
  (h1 : f _0 = 0)
  (h2 : ∀ a, f (S a) = (f a).succ) :
  f a = H a := by
  induction a with
  | _0      => simp[h1]
  | S a' ih => simp[h2 a', ih]
```

$H$是一个一一对应，即$a = b \iff H(a) = H(b)$：显然有$0 = 0$和$\overline{0} = \overline{0}$。$a$和$b$不全为$0$时，例如$a = 0$时有$a = 0 \ne b$和$H(a) = \overline{0} \ne H(b)$。现在假设$a = b \iff H(a) = H(b)$，则$a^+ = b^+ \iff a = b \iff H(a) = H(b) \iff H(a)^+ = H(a^+) = H(b)^+ = H(b^+)$。

```lean
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
```

我们可以定义$H$的逆映射$H^{-1} : \overline{\N} \to \N$：
$$
\begin{align*}
H^{-1}(\overline{0}) &:= 0 \\
H^{-1}(a^+) &:= H^{-1}(a)^+
\end{align*}
$$

```lean
def N.unH : Nat → N
| 0  => _0
| Nat.succ a => S (unH a)

@[simp]
theorem unH_zero : unH 0 = _0 := by
  rfl

@[simp]
theorem unH_succ (a : Nat) : unH a.succ = S (unH a) := by
  rfl
```

我们有$a = b \iff H^{-1}(a) = H^{-1}(b)$：

```lean
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
```

我们有$H^{-1}(H(a)) = a$和$H(H^{-1}(a)) = a$：

```lean
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
```

各常元在此一一对应下保持，例如除$H(0) = \overline{0}$外，我们还有$H(1) = H(0^+) = H(0)^+ = \overline{1}$：

```lean
@[simp]
theorem iso_one : H _1 = 1 := by
  rfl
```

各运算在此一一对应下保持：

$H(a^{-}) = H(a)^{-}$：$a = 0$时有$H(0^{-}) = H(0) = \overline{0} = \overline{0}^{-}$。现在假设$H(a^{-}) = H(a)^{-}$，则$H((a^{+})^{-}) = H(a) = (H(a)^{+})^{-} = H(a^{+})^{-}$。

```lean
theorem iso_pred : H (P a) = (H a).pred := by
  induction a with
  | _0      => rfl
  | S a' ih => simp
```

$H(a + b) = H(a) + H(b)$：对$b$归纳。$b = 0$时有$H(a + 0) = H(a) = H(a) + H(0)$。现在假设$H(a + b) = H(a) + H(b)$，则$H(a + b^{+}) = H(a + b)^{+} = (H(a) + H(b))^{+} = H(a) + H(b)^{+} = H(a) + H(b^{+})$。

```lean
theorem iso_add : H (a + b) = H a + H b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    H (a + S b') = H (S (a + b'))    := by rfl
    _            = (H (a + b')).succ := by rfl
    _            = (H a + H b').succ := by rw[ih]
    _            = H a + H (S b')    := by rfl
```

$H(ab) = H(a)H(b)$：对$b$归纳。$b = 0$时有$H(a \times 0) = \overline{0} = H(a)H(0)$。现在假设$H(ab) = H(a)H(b)$，则$H(ab^{+}) = H(ab + a) = H(ab) + H(a) = H(a)H(b) + H(a) = H(a)H(b)^{+} = H(a)H(b^{+})$。

```lean
theorem iso_mul : H (a * b) = H a * H b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    H (a * S b') = H (a * b' + a)   := by rfl
    _            = H (a * b') + H a := by rw[iso_add]
    _            = H a * H b' + H a := by rw[ih]
    _            = H a * H (S b')   := by rfl
```

$H(a^{b}) = H(a)^{H(b)}$：对$b$归纳。$b = 0$时有$H(a^0) = \overline{1} = H(a)^{H(0)}$。现在假设$H(a^{b}) = H(a)^{H(b)}$，则$H(a^{b^+}) = H(a^{b}a) = H(a^{b})H(a) = H(a)^{H(b)}H(a) = H(a)^{H(b)^+} = H(a)^{H(b^+)}$。

```lean
theorem iso_pow : H (a ^ b) = H a ^ H b := by
  induction b with
  | _0      => rfl
  | S b' ih => calc
    H (a ^ S b') = H (a ^ b' * a)   := by rfl
    _            = H (a ^ b') * H a := by rw[iso_mul]
    _            = H a ^ H b' * H a := by rw[ih]
    _            = H a ^ H (S b')   := by rfl
```

$H(min(a, b)) = min(H(a), H(b))$

```lean
theorem iso_min {a b : N} : H (min a b) = min (H a) (H b) := by
  match a, b with
  | _0, _ => simp
  | _, _0 => simp
  | S a', S b' =>
    simp[iso_min] at *
```

$H(max(a, b)) = max(H(a), H(b))$

```lean
theorem iso_max {a b : N} : H (max a b) = max (H a) (H b) := by
  match a, b with
  | _0, _ => simp
  | _, _0 => simp
  | S a', S b' =>
    simp[iso_max] at *
```

$H(a \dotminus b) = H(a) \dotminus H(b)$

```lean
theorem iso_monus {a b : N} : H (monus a b) = (H a) - (H b) := by
  induction b with
  | _0      => rfl
  | S b' ih => rw[monus_succ, iso_succ, Nat.sub_succ, iso_pred, ih]
```

$H(\lvert a - b \rvert) = \lvert H(a) - H(b) \rvert$

```lean
-- from Mathlib.Data.Nat.Dist
def Nat.dist (n m : Nat) :=
  n - m + (m - n)

theorem iso_abssub {a b : N} : H (abssub a b) = Nat.dist (H a) (H b) := by
  match a, b with
  | _0, _      => unfold Nat.dist; simp
  | _, _0      => unfold Nat.dist; simp
  | S a', S b' => simp[iso_abssub]; unfold Nat.dist; simp
```

各关系在此一一对应下保持：

$a \le b \iff H(a) \le H(b)$：$a = 0$时显然有$0 \le b$和$\overline{0} \le H(b)$。现在假设$a \le b \iff H(a) \le H(b)$，则$a^+ \le b^+ \iff a \le b \iff H(a) \le H(b) \iff H(a)^{+} = H(a^+) \le H(b)^{+} = H(b^+)$。

又：（$\implies$）$a \le b$时有$a + c = b$，于是$H(a + c) = H(a) + H(c) = H(b)$，从而$H(a) \le H(b)$。（$\impliedby$）$H(a) \le H(b)$时有$H(a) + c = H(a) + H(H^{-1}(c)) = H(a + H^{-1}(c)) = H(b)$，于是$a + H^{-1}(c) = b$，从而$a \le b$。

```lean
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
```

$a \mid b \iff H(a) \mid H(b)$：（$\implies$）$a \mid b$时有$ac = b$，于是$H(ac) = H(a)H(c) = H(b)$，从而$H(a) \mid H(b)$。（$\impliedby$）$H(a) \mid H(b)$时有$H(a)c = H(a)H(H^{-1}(c)) = H(aH^{-1}(c)) = H(b)$，于是$aH^{-1}(c) = b$，从而$a \mid b$。

```lean
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
```
