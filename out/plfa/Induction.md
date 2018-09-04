---
src       : src/plfa/Induction.lagda
title     : "Induction: Proof by Induction"
layout    : page
permalink : /Induction/
---

<pre class="Agda">{% raw %}<a id="108" class="Keyword">module</a> <a id="115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}" class="Module">plfa.Induction</a> <a id="130" class="Keyword">where</a>{% endraw %}</pre>

> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.


## Imports

We require equivality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below.
<pre class="Agda">{% raw %}<a id="743" class="Keyword">import</a> <a id="750" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="788" class="Symbol">as</a> <a id="791" class="Module">Eq</a>
<a id="794" class="Keyword">open</a> <a id="799" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="802" class="Keyword">using</a> <a id="808" class="Symbol">(</a><a id="809" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="812" class="Symbol">;</a> <a id="814" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="818" class="Symbol">;</a> <a id="820" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a><a id="824" class="Symbol">;</a> <a id="826" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#560" class="Function">sym</a><a id="829" class="Symbol">)</a>
<a id="831" class="Keyword">open</a> <a id="836" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3861" class="Module">Eq.≡-Reasoning</a> <a id="851" class="Keyword">using</a> <a id="857" class="Symbol">(</a><a id="858" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin_</a><a id="864" class="Symbol">;</a> <a id="866" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">_≡⟨⟩_</a><a id="871" class="Symbol">;</a> <a id="873" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">_≡⟨_⟩_</a><a id="879" class="Symbol">;</a> <a id="881" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">_∎</a><a id="883" class="Symbol">)</a>
<a id="885" class="Keyword">open</a> <a id="890" class="Keyword">import</a> <a id="897" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="906" class="Keyword">using</a> <a id="912" class="Symbol">(</a><a id="913" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="914" class="Symbol">;</a> <a id="916" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="920" class="Symbol">;</a> <a id="922" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="925" class="Symbol">;</a> <a id="927" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="930" class="Symbol">;</a> <a id="932" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="935" class="Symbol">;</a> <a id="937" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="940" class="Symbol">)</a>{% endraw %}</pre>


## Properties of operators

Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Identity_ Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_ Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutatitivity_ Operator `+` is commutative if order or
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_ Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.

Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplications distributes over addition.

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will ofter call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


## Associativity

One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables.
<pre class="Agda">{% raw %}<a id="3287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#3287" class="Function">_</a> <a id="3289" class="Symbol">:</a> <a id="3291" class="Symbol">(</a><a id="3292" class="Number">3</a> <a id="3294" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3296" class="Number">4</a><a id="3297" class="Symbol">)</a> <a id="3299" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3301" class="Number">5</a> <a id="3303" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3305" class="Number">3</a> <a id="3307" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3309" class="Symbol">(</a><a id="3310" class="Number">4</a> <a id="3312" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3314" class="Number">5</a><a id="3315" class="Symbol">)</a>
<a id="3317" class="Symbol">_</a> <a id="3319" class="Symbol">=</a>
  <a id="3323" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="3333" class="Symbol">(</a><a id="3334" class="Number">3</a> <a id="3336" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3338" class="Number">4</a><a id="3339" class="Symbol">)</a> <a id="3341" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3343" class="Number">5</a>
  <a id="3347" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="3355" class="Number">7</a> <a id="3357" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3359" class="Number">5</a>
  <a id="3363" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="3371" class="Number">12</a>
  <a id="3376" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="3384" class="Number">3</a> <a id="3386" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3388" class="Number">9</a>
  <a id="3392" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="3400" class="Number">3</a> <a id="3402" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3404" class="Symbol">(</a><a id="3405" class="Number">4</a> <a id="3407" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3409" class="Number">5</a><a id="3410" class="Symbol">)</a>
  <a id="3414" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.


## Proof by induction

Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today.

    -- on the second day, two properties are known
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new.

    -- on the third day, three properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now.

    -- on the fourth day, four properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-assoc"></a><a id="7653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7653" class="Function">+-assoc</a> <a id="7661" class="Symbol">:</a> <a id="7663" class="Symbol">∀</a> <a id="7665" class="Symbol">(</a><a id="7666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7666" class="Bound">m</a> <a id="7668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7668" class="Bound">n</a> <a id="7670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7670" class="Bound">p</a> <a id="7672" class="Symbol">:</a> <a id="7674" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7675" class="Symbol">)</a> <a id="7677" class="Symbol">→</a> <a id="7679" class="Symbol">(</a><a id="7680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7666" class="Bound">m</a> <a id="7682" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7668" class="Bound">n</a><a id="7685" class="Symbol">)</a> <a id="7687" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7670" class="Bound">p</a> <a id="7691" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7666" class="Bound">m</a> <a id="7695" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7697" class="Symbol">(</a><a id="7698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7668" class="Bound">n</a> <a id="7700" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7670" class="Bound">p</a><a id="7703" class="Symbol">)</a>
<a id="7705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7653" class="Function">+-assoc</a> <a id="7713" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7718" class="Bound">n</a> <a id="7720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7720" class="Bound">p</a> <a id="7722" class="Symbol">=</a>
  <a id="7726" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="7736" class="Symbol">(</a><a id="7737" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7742" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7718" class="Bound">n</a><a id="7745" class="Symbol">)</a> <a id="7747" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7720" class="Bound">p</a>
  <a id="7753" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="7761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7718" class="Bound">n</a> <a id="7763" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7720" class="Bound">p</a>
  <a id="7769" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
   <a id="7776" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7781" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7783" class="Symbol">(</a><a id="7784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7718" class="Bound">n</a> <a id="7786" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7720" class="Bound">p</a><a id="7789" class="Symbol">)</a>
  <a id="7793" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="7795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7653" class="Function">+-assoc</a> <a id="7803" class="Symbol">(</a><a id="7804" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7808" class="Bound">m</a><a id="7809" class="Symbol">)</a> <a id="7811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7811" class="Bound">n</a> <a id="7813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7813" class="Bound">p</a> <a id="7815" class="Symbol">=</a>
  <a id="7819" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="7829" class="Symbol">(</a><a id="7830" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7808" class="Bound">m</a> <a id="7836" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7811" class="Bound">n</a><a id="7839" class="Symbol">)</a> <a id="7841" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7813" class="Bound">p</a>
  <a id="7847" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="7855" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7859" class="Symbol">(</a><a id="7860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7808" class="Bound">m</a> <a id="7862" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7811" class="Bound">n</a><a id="7865" class="Symbol">)</a> <a id="7867" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7813" class="Bound">p</a>
  <a id="7873" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="7881" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7885" class="Symbol">((</a><a id="7887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7808" class="Bound">m</a> <a id="7889" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7811" class="Bound">n</a><a id="7892" class="Symbol">)</a> <a id="7894" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7813" class="Bound">p</a><a id="7897" class="Symbol">)</a>
  <a id="7901" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="7904" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="7909" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7913" class="Symbol">(</a><a id="7914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7653" class="Function">+-assoc</a> <a id="7922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7808" class="Bound">m</a> <a id="7924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7811" class="Bound">n</a> <a id="7926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7813" class="Bound">p</a><a id="7927" class="Symbol">)</a> <a id="7929" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="7935" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7939" class="Symbol">(</a><a id="7940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7808" class="Bound">m</a> <a id="7942" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7944" class="Symbol">(</a><a id="7945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7811" class="Bound">n</a> <a id="7947" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7813" class="Bound">p</a><a id="7950" class="Symbol">))</a>
  <a id="7955" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="7963" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7808" class="Bound">m</a> <a id="7969" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7971" class="Symbol">(</a><a id="7972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7811" class="Bound">n</a> <a id="7974" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7813" class="Bound">p</a><a id="7977" class="Symbol">)</a>
  <a id="7981" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provide evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p` that
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.


## Our second proof: commutativity

Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-identityʳ"></a><a id="11315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11315" class="Function">+-identityʳ</a> <a id="11327" class="Symbol">:</a> <a id="11329" class="Symbol">∀</a> <a id="11331" class="Symbol">(</a><a id="11332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11332" class="Bound">m</a> <a id="11334" class="Symbol">:</a> <a id="11336" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11337" class="Symbol">)</a> <a id="11339" class="Symbol">→</a> <a id="11341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11332" class="Bound">m</a> <a id="11343" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11345" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11350" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11332" class="Bound">m</a>
<a id="11354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11315" class="Function">+-identityʳ</a> <a id="11366" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11371" class="Symbol">=</a>
  <a id="11375" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="11385" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11390" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="11399" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11407" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="11414" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="11416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11315" class="Function">+-identityʳ</a> <a id="11428" class="Symbol">(</a><a id="11429" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11433" class="Bound">m</a><a id="11434" class="Symbol">)</a> <a id="11436" class="Symbol">=</a>
  <a id="11440" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="11450" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11433" class="Bound">m</a> <a id="11456" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11458" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="11465" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11473" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11477" class="Symbol">(</a><a id="11478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11433" class="Bound">m</a> <a id="11480" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11482" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="11486" class="Symbol">)</a>
  <a id="11490" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="11493" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="11498" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11502" class="Symbol">(</a><a id="11503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11315" class="Function">+-identityʳ</a> <a id="11515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11433" class="Bound">m</a><a id="11516" class="Symbol">)</a> <a id="11518" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="11524" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11433" class="Bound">m</a>
  <a id="11532" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-suc"></a><a id="12988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12988" class="Function">+-suc</a> <a id="12994" class="Symbol">:</a> <a id="12996" class="Symbol">∀</a> <a id="12998" class="Symbol">(</a><a id="12999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12999" class="Bound">m</a> <a id="13001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13001" class="Bound">n</a> <a id="13003" class="Symbol">:</a> <a id="13005" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13006" class="Symbol">)</a> <a id="13008" class="Symbol">→</a> <a id="13010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12999" class="Bound">m</a> <a id="13012" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13014" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13001" class="Bound">n</a> <a id="13020" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13022" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13026" class="Symbol">(</a><a id="13027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12999" class="Bound">m</a> <a id="13029" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13001" class="Bound">n</a><a id="13032" class="Symbol">)</a>
<a id="13034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12988" class="Function">+-suc</a> <a id="13040" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13045" class="Bound">n</a> <a id="13047" class="Symbol">=</a>
  <a id="13051" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="13061" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13066" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13068" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13045" class="Bound">n</a>
  <a id="13076" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="13084" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13045" class="Bound">n</a>
  <a id="13092" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="13100" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13104" class="Symbol">(</a><a id="13105" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13110" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13045" class="Bound">n</a><a id="13113" class="Symbol">)</a>
  <a id="13117" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="13119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12988" class="Function">+-suc</a> <a id="13125" class="Symbol">(</a><a id="13126" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13130" class="Bound">m</a><a id="13131" class="Symbol">)</a> <a id="13133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13133" class="Bound">n</a> <a id="13135" class="Symbol">=</a>
  <a id="13139" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="13149" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13130" class="Bound">m</a> <a id="13155" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13157" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13133" class="Bound">n</a>
  <a id="13165" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="13173" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13177" class="Symbol">(</a><a id="13178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13130" class="Bound">m</a> <a id="13180" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13182" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13133" class="Bound">n</a><a id="13187" class="Symbol">)</a>
  <a id="13191" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="13194" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="13199" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13203" class="Symbol">(</a><a id="13204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12988" class="Function">+-suc</a> <a id="13210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13130" class="Bound">m</a> <a id="13212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13133" class="Bound">n</a><a id="13213" class="Symbol">)</a> <a id="13215" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="13221" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13225" class="Symbol">(</a><a id="13226" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13230" class="Symbol">(</a><a id="13231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13130" class="Bound">m</a> <a id="13233" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13133" class="Bound">n</a><a id="13236" class="Symbol">))</a>
  <a id="13241" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="13249" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13253" class="Symbol">(</a><a id="13254" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13130" class="Bound">m</a> <a id="13260" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13133" class="Bound">n</a><a id="13263" class="Symbol">)</a>
  <a id="13267" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="14577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14577" class="Function">+-comm</a> <a id="14584" class="Symbol">:</a> <a id="14586" class="Symbol">∀</a> <a id="14588" class="Symbol">(</a><a id="14589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14589" class="Bound">m</a> <a id="14591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14591" class="Bound">n</a> <a id="14593" class="Symbol">:</a> <a id="14595" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14596" class="Symbol">)</a> <a id="14598" class="Symbol">→</a> <a id="14600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14589" class="Bound">m</a> <a id="14602" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14591" class="Bound">n</a> <a id="14606" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="14608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14591" class="Bound">n</a> <a id="14610" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14589" class="Bound">m</a>
<a id="14614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14577" class="Function">+-comm</a> <a id="14621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14621" class="Bound">m</a> <a id="14623" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14628" class="Symbol">=</a>
  <a id="14632" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="14642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14621" class="Bound">m</a> <a id="14644" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14646" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="14653" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="14656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11315" class="Function">+-identityʳ</a> <a id="14668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14621" class="Bound">m</a> <a id="14670" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="14676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14621" class="Bound">m</a>
  <a id="14680" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="14688" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14693" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14621" class="Bound">m</a>
  <a id="14699" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="14701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14577" class="Function">+-comm</a> <a id="14708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14708" class="Bound">m</a> <a id="14710" class="Symbol">(</a><a id="14711" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14715" class="Bound">n</a><a id="14716" class="Symbol">)</a> <a id="14718" class="Symbol">=</a>
  <a id="14722" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="14732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14708" class="Bound">m</a> <a id="14734" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14736" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14715" class="Bound">n</a>
  <a id="14744" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="14747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12988" class="Function">+-suc</a> <a id="14753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14708" class="Bound">m</a> <a id="14755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14715" class="Bound">n</a> <a id="14757" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="14763" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14767" class="Symbol">(</a><a id="14768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14708" class="Bound">m</a> <a id="14770" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14715" class="Bound">n</a><a id="14773" class="Symbol">)</a>
  <a id="14777" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="14780" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="14785" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14789" class="Symbol">(</a><a id="14790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14577" class="Function">+-comm</a> <a id="14797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14708" class="Bound">m</a> <a id="14799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14715" class="Bound">n</a><a id="14800" class="Symbol">)</a> <a id="14802" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="14808" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14812" class="Symbol">(</a><a id="14813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14715" class="Bound">n</a> <a id="14815" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14708" class="Bound">m</a><a id="14818" class="Symbol">)</a>
  <a id="14822" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="14830" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14715" class="Bound">n</a> <a id="14836" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14708" class="Bound">m</a>
  <a id="14842" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The the remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.


## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgements asserting associativity.

     -- in the beginning, we know nothing about associativity

Now, we apply the rules to all the judgements we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments.

    -- on the first day, we know about associativity of 0
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgements from the day before, plus any judgements added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgements.

    -- on the second day, we know about associativity of 0 and 1
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again.

    -- on the third day, we know about associativity of 0, 1, and 2
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now.

    -- on the fourth day, we know about associativity of 0, 1, 2, and 3
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the _m_'th day we will know all the
judgements where the first number is less than _m_.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

#### Exercise `finite-+-assoc` {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier]({{ site.baseurl }}{% link out/plfa/Naturals.md %}#finite-creation).


## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations.
<pre class="Agda">{% raw %}<a id="+-assoc′"></a><a id="18935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18935" class="Function">+-assoc′</a> <a id="18944" class="Symbol">:</a> <a id="18946" class="Symbol">∀</a> <a id="18948" class="Symbol">(</a><a id="18949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18949" class="Bound">m</a> <a id="18951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18951" class="Bound">n</a> <a id="18953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18953" class="Bound">p</a> <a id="18955" class="Symbol">:</a> <a id="18957" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18958" class="Symbol">)</a> <a id="18960" class="Symbol">→</a> <a id="18962" class="Symbol">(</a><a id="18963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18949" class="Bound">m</a> <a id="18965" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18951" class="Bound">n</a><a id="18968" class="Symbol">)</a> <a id="18970" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18953" class="Bound">p</a> <a id="18974" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="18976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18949" class="Bound">m</a> <a id="18978" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18980" class="Symbol">(</a><a id="18981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18951" class="Bound">n</a> <a id="18983" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18953" class="Bound">p</a><a id="18986" class="Symbol">)</a>
<a id="18988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18935" class="Function">+-assoc′</a> <a id="18997" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="19005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19005" class="Bound">n</a> <a id="19007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19007" class="Bound">p</a>                          <a id="19034" class="Symbol">=</a>  <a id="19037" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="19042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18935" class="Function">+-assoc′</a> <a id="19051" class="Symbol">(</a><a id="19052" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19056" class="Bound">m</a><a id="19057" class="Symbol">)</a> <a id="19059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19059" class="Bound">n</a> <a id="19061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19061" class="Bound">p</a>  <a id="19064" class="Keyword">rewrite</a> <a id="19072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18935" class="Function">+-assoc′</a> <a id="19081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19056" class="Bound">m</a> <a id="19083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19059" class="Bound">n</a> <a id="19085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#19061" class="Bound">p</a>  <a id="19088" class="Symbol">=</a>  <a id="19091" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations.
<pre class="Agda">{% raw %}<a id="+-identity′"></a><a id="20010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20010" class="Function">+-identity′</a> <a id="20022" class="Symbol">:</a> <a id="20024" class="Symbol">∀</a> <a id="20026" class="Symbol">(</a><a id="20027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20027" class="Bound">n</a> <a id="20029" class="Symbol">:</a> <a id="20031" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20032" class="Symbol">)</a> <a id="20034" class="Symbol">→</a> <a id="20036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20027" class="Bound">n</a> <a id="20038" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20040" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="20045" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="20047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20027" class="Bound">n</a>
<a id="20049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20010" class="Function">+-identity′</a> <a id="20061" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="20066" class="Symbol">=</a> <a id="20068" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="20073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20010" class="Function">+-identity′</a> <a id="20085" class="Symbol">(</a><a id="20086" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20090" class="Bound">n</a><a id="20091" class="Symbol">)</a> <a id="20093" class="Keyword">rewrite</a> <a id="20101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20010" class="Function">+-identity′</a> <a id="20113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20090" class="Bound">n</a> <a id="20115" class="Symbol">=</a> <a id="20117" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="20123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20123" class="Function">+-suc′</a> <a id="20130" class="Symbol">:</a> <a id="20132" class="Symbol">∀</a> <a id="20134" class="Symbol">(</a><a id="20135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20135" class="Bound">m</a> <a id="20137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20137" class="Bound">n</a> <a id="20139" class="Symbol">:</a> <a id="20141" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20142" class="Symbol">)</a> <a id="20144" class="Symbol">→</a> <a id="20146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20135" class="Bound">m</a> <a id="20148" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20150" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20137" class="Bound">n</a> <a id="20156" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="20158" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20162" class="Symbol">(</a><a id="20163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20135" class="Bound">m</a> <a id="20165" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20137" class="Bound">n</a><a id="20168" class="Symbol">)</a>
<a id="20170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20123" class="Function">+-suc′</a> <a id="20177" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="20182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20182" class="Bound">n</a> <a id="20184" class="Symbol">=</a> <a id="20186" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="20191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20123" class="Function">+-suc′</a> <a id="20198" class="Symbol">(</a><a id="20199" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20203" class="Bound">m</a><a id="20204" class="Symbol">)</a> <a id="20206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20206" class="Bound">n</a> <a id="20208" class="Keyword">rewrite</a> <a id="20216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20123" class="Function">+-suc′</a> <a id="20223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20203" class="Bound">m</a> <a id="20225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20206" class="Bound">n</a> <a id="20227" class="Symbol">=</a> <a id="20229" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="20235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20235" class="Function">+-comm′</a> <a id="20243" class="Symbol">:</a> <a id="20245" class="Symbol">∀</a> <a id="20247" class="Symbol">(</a><a id="20248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20248" class="Bound">m</a> <a id="20250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20250" class="Bound">n</a> <a id="20252" class="Symbol">:</a> <a id="20254" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20255" class="Symbol">)</a> <a id="20257" class="Symbol">→</a> <a id="20259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20248" class="Bound">m</a> <a id="20261" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20250" class="Bound">n</a> <a id="20265" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="20267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20250" class="Bound">n</a> <a id="20269" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20248" class="Bound">m</a>
<a id="20273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20235" class="Function">+-comm′</a> <a id="20281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20281" class="Bound">m</a> <a id="20283" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="20288" class="Keyword">rewrite</a> <a id="20296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20010" class="Function">+-identity′</a> <a id="20308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20281" class="Bound">m</a> <a id="20310" class="Symbol">=</a> <a id="20312" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="20317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20235" class="Function">+-comm′</a> <a id="20325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20325" class="Bound">m</a> <a id="20327" class="Symbol">(</a><a id="20328" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20332" class="Bound">n</a><a id="20333" class="Symbol">)</a> <a id="20335" class="Keyword">rewrite</a> <a id="20343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20123" class="Function">+-suc′</a> <a id="20350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20325" class="Bound">m</a> <a id="20352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20332" class="Bound">n</a> <a id="20354" class="Symbol">|</a> <a id="20356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20235" class="Function">+-comm′</a> <a id="20364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20325" class="Bound">m</a> <a id="20366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20332" class="Bound">n</a> <a id="20368" class="Symbol">=</a> <a id="20370" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgement.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in,
renumbering the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


#### Exercise `+-swap` {#plus-swap} 

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

#### Exercise `*-distrib-+` {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that 
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md %}#Bin)
defines a datatype of bitstrings representing natural numbers
<pre class="Agda">{% raw %}<a id="25042" class="Keyword">data</a> <a id="Bin"></a><a id="25047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25047" class="Datatype">Bin</a> <a id="25051" class="Symbol">:</a> <a id="25053" class="PrimitiveType">Set</a> <a id="25057" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="25065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25065" class="InductiveConstructor">nil</a> <a id="25069" class="Symbol">:</a> <a id="25071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25047" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="25077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25077" class="InductiveConstructor Operator">x0_</a> <a id="25081" class="Symbol">:</a> <a id="25083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25047" class="Datatype">Bin</a> <a id="25087" class="Symbol">→</a> <a id="25089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25047" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="25095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25095" class="InductiveConstructor Operator">x1_</a> <a id="25099" class="Symbol">:</a> <a id="25101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25047" class="Datatype">Bin</a> <a id="25105" class="Symbol">→</a> <a id="25107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#25047" class="Datatype">Bin</a>{% endraw %}</pre>
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Standard library

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="25562" class="Keyword">import</a> <a id="25569" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25589" class="Keyword">using</a> <a id="25595" class="Symbol">(</a><a id="25596" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7782" class="Function">+-assoc</a><a id="25603" class="Symbol">;</a> <a id="25605" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7938" class="Function">+-identityʳ</a><a id="25616" class="Symbol">;</a> <a id="25618" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7679" class="Function">+-suc</a><a id="25623" class="Symbol">;</a> <a id="25625" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a><a id="25631" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ∀  U+2200  FOR ALL (\forall)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
