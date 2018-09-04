---
src       : src/plfa/Equality.lagda
title     : "Equality: Equality and equational reasoning"
layout    : page
permalink : /Equality/
---

<pre class="Agda">{% raw %}<a id="121" class="Keyword">module</a> <a id="128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="142" class="Keyword">where</a>{% endraw %}</pre>

Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda, imports equality.  Since we define equality
here, any import would create a conflict.


## Equality

We declare equality as follows.
<pre class="Agda">{% raw %}<a id="678" class="Keyword">data</a> <a id="_≡_"></a><a id="683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">_≡_</a> <a id="687" class="Symbol">{</a><a id="688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#688" class="Bound">A</a> <a id="690" class="Symbol">:</a> <a id="692" class="PrimitiveType">Set</a><a id="695" class="Symbol">}</a> <a id="697" class="Symbol">(</a><a id="698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#698" class="Bound">x</a> <a id="700" class="Symbol">:</a> <a id="702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#688" class="Bound">A</a><a id="703" class="Symbol">)</a> <a id="705" class="Symbol">:</a> <a id="707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#688" class="Bound">A</a> <a id="709" class="Symbol">→</a> <a id="711" class="PrimitiveType">Set</a> <a id="715" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a> <a id="728" class="Symbol">:</a> <a id="730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#698" class="Bound">x</a> <a id="732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#698" class="Bound">x</a>{% endraw %}</pre>
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equivalent to itself, and we have no other way of showing values
are equivalent.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.

We declare the precedence of equivalence as follows.
<pre class="Agda">{% raw %}<a id="1416" class="Keyword">infix</a> <a id="1422" class="Number">4</a> <a id="1424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">_≡_</a>{% endraw %}</pre>
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equivalence, via the
constructor `refl`.  It is straightforward to show symmetry.
<pre class="Agda">{% raw %}<a id="sym"></a><a id="1898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1898" class="Function">sym</a> <a id="1902" class="Symbol">:</a> <a id="1904" class="Symbol">∀</a> <a id="1906" class="Symbol">{</a><a id="1907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1907" class="Bound">A</a> <a id="1909" class="Symbol">:</a> <a id="1911" class="PrimitiveType">Set</a><a id="1914" class="Symbol">}</a> <a id="1916" class="Symbol">{</a><a id="1917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1917" class="Bound">x</a> <a id="1919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1919" class="Bound">y</a> <a id="1921" class="Symbol">:</a> <a id="1923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1907" class="Bound">A</a><a id="1924" class="Symbol">}</a>
  <a id="1928" class="Symbol">→</a> <a id="1930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1917" class="Bound">x</a> <a id="1932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="1934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1919" class="Bound">y</a>
    <a id="1940" class="Comment">-----</a>
  <a id="1948" class="Symbol">→</a> <a id="1950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1919" class="Bound">y</a> <a id="1952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="1954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1917" class="Bound">x</a>
<a id="1956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1898" class="Function">sym</a> <a id="1960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a> <a id="1965" class="Symbol">=</a> <a id="1967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>{% endraw %}</pre>
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type.

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward.
<pre class="Agda">{% raw %}<a id="trans"></a><a id="3642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3642" class="Function">trans</a> <a id="3648" class="Symbol">:</a> <a id="3650" class="Symbol">∀</a> <a id="3652" class="Symbol">{</a><a id="3653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3653" class="Bound">A</a> <a id="3655" class="Symbol">:</a> <a id="3657" class="PrimitiveType">Set</a><a id="3660" class="Symbol">}</a> <a id="3662" class="Symbol">{</a><a id="3663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3663" class="Bound">x</a> <a id="3665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3665" class="Bound">y</a> <a id="3667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3667" class="Bound">z</a> <a id="3669" class="Symbol">:</a> <a id="3671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3653" class="Bound">A</a><a id="3672" class="Symbol">}</a>
  <a id="3676" class="Symbol">→</a> <a id="3678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3663" class="Bound">x</a> <a id="3680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="3682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3665" class="Bound">y</a>
  <a id="3686" class="Symbol">→</a> <a id="3688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3665" class="Bound">y</a> <a id="3690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="3692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3667" class="Bound">z</a>
    <a id="3698" class="Comment">-----</a>
  <a id="3706" class="Symbol">→</a> <a id="3708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3663" class="Bound">x</a> <a id="3710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="3712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3667" class="Bound">z</a>
<a id="3714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3642" class="Function">trans</a> <a id="3720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a> <a id="3725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>  <a id="3731" class="Symbol">=</a>  <a id="3734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>{% endraw %}</pre>
Again, a useful exercise is to carry out an interactive development, checking
how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution {#cong}

Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both.
<pre class="Agda">{% raw %}<a id="cong"></a><a id="4074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4074" class="Function">cong</a> <a id="4079" class="Symbol">:</a> <a id="4081" class="Symbol">∀</a> <a id="4083" class="Symbol">{</a><a id="4084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4084" class="Bound">A</a> <a id="4086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4086" class="Bound">B</a> <a id="4088" class="Symbol">:</a> <a id="4090" class="PrimitiveType">Set</a><a id="4093" class="Symbol">}</a> <a id="4095" class="Symbol">(</a><a id="4096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4096" class="Bound">f</a> <a id="4098" class="Symbol">:</a> <a id="4100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4084" class="Bound">A</a> <a id="4102" class="Symbol">→</a> <a id="4104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4086" class="Bound">B</a><a id="4105" class="Symbol">)</a> <a id="4107" class="Symbol">{</a><a id="4108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4108" class="Bound">x</a> <a id="4110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4110" class="Bound">y</a> <a id="4112" class="Symbol">:</a> <a id="4114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4084" class="Bound">A</a><a id="4115" class="Symbol">}</a>
  <a id="4119" class="Symbol">→</a> <a id="4121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4108" class="Bound">x</a> <a id="4123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4110" class="Bound">y</a>
    <a id="4131" class="Comment">---------</a>
  <a id="4143" class="Symbol">→</a> <a id="4145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4096" class="Bound">f</a> <a id="4147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4108" class="Bound">x</a> <a id="4149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4096" class="Bound">f</a> <a id="4153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4110" class="Bound">y</a>
<a id="4155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4074" class="Function">cong</a> <a id="4160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4160" class="Bound">f</a> <a id="4162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>  <a id="4168" class="Symbol">=</a>  <a id="4171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Congruence of functions with two arguments is similar.
<pre class="Agda">{% raw %}<a id="cong₂"></a><a id="4256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4256" class="Function">cong₂</a> <a id="4262" class="Symbol">:</a> <a id="4264" class="Symbol">∀</a> <a id="4266" class="Symbol">{</a><a id="4267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4267" class="Bound">A</a> <a id="4269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4269" class="Bound">B</a> <a id="4271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4271" class="Bound">C</a> <a id="4273" class="Symbol">:</a> <a id="4275" class="PrimitiveType">Set</a><a id="4278" class="Symbol">}</a> <a id="4280" class="Symbol">(</a><a id="4281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4281" class="Bound">f</a> <a id="4283" class="Symbol">:</a> <a id="4285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4267" class="Bound">A</a> <a id="4287" class="Symbol">→</a> <a id="4289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4269" class="Bound">B</a> <a id="4291" class="Symbol">→</a> <a id="4293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4271" class="Bound">C</a><a id="4294" class="Symbol">)</a> <a id="4296" class="Symbol">{</a><a id="4297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4297" class="Bound">u</a> <a id="4299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4299" class="Bound">x</a> <a id="4301" class="Symbol">:</a> <a id="4303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4267" class="Bound">A</a><a id="4304" class="Symbol">}</a> <a id="4306" class="Symbol">{</a><a id="4307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4307" class="Bound">v</a> <a id="4309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4309" class="Bound">y</a> <a id="4311" class="Symbol">:</a> <a id="4313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4269" class="Bound">B</a><a id="4314" class="Symbol">}</a>
  <a id="4318" class="Symbol">→</a> <a id="4320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4297" class="Bound">u</a> <a id="4322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4299" class="Bound">x</a>
  <a id="4328" class="Symbol">→</a> <a id="4330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4307" class="Bound">v</a> <a id="4332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4309" class="Bound">y</a>
    <a id="4340" class="Comment">-------------</a>
  <a id="4356" class="Symbol">→</a> <a id="4358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4281" class="Bound">f</a> <a id="4360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4297" class="Bound">u</a> <a id="4362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4307" class="Bound">v</a> <a id="4364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4281" class="Bound">f</a> <a id="4368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4299" class="Bound">x</a> <a id="4370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4309" class="Bound">y</a>
<a id="4372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4256" class="Function">cong₂</a> <a id="4378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4378" class="Bound">f</a> <a id="4380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a> <a id="4385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>  <a id="4391" class="Symbol">=</a>  <a id="4394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms.
<pre class="Agda">{% raw %}<a id="cong-app"></a><a id="4582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4582" class="Function">cong-app</a> <a id="4591" class="Symbol">:</a> <a id="4593" class="Symbol">∀</a> <a id="4595" class="Symbol">{</a><a id="4596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4596" class="Bound">A</a> <a id="4598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4598" class="Bound">B</a> <a id="4600" class="Symbol">:</a> <a id="4602" class="PrimitiveType">Set</a><a id="4605" class="Symbol">}</a> <a id="4607" class="Symbol">{</a><a id="4608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4608" class="Bound">f</a> <a id="4610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4610" class="Bound">g</a> <a id="4612" class="Symbol">:</a> <a id="4614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4596" class="Bound">A</a> <a id="4616" class="Symbol">→</a> <a id="4618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4598" class="Bound">B</a><a id="4619" class="Symbol">}</a>
  <a id="4623" class="Symbol">→</a> <a id="4625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4608" class="Bound">f</a> <a id="4627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4610" class="Bound">g</a>
    <a id="4635" class="Comment">---------------------</a>
  <a id="4659" class="Symbol">→</a> <a id="4661" class="Symbol">∀</a> <a id="4663" class="Symbol">(</a><a id="4664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4664" class="Bound">x</a> <a id="4666" class="Symbol">:</a> <a id="4668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4596" class="Bound">A</a><a id="4669" class="Symbol">)</a> <a id="4671" class="Symbol">→</a> <a id="4673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4608" class="Bound">f</a> <a id="4675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4664" class="Bound">x</a> <a id="4677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4610" class="Bound">g</a> <a id="4681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4664" class="Bound">x</a>
<a id="4683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4582" class="Function">cong-app</a> <a id="4692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a> <a id="4697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4697" class="Bound">x</a> <a id="4699" class="Symbol">=</a> <a id="4701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second.
<pre class="Agda">{% raw %}<a id="subst"></a><a id="4864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4864" class="Function">subst</a> <a id="4870" class="Symbol">:</a> <a id="4872" class="Symbol">∀</a> <a id="4874" class="Symbol">{</a><a id="4875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4875" class="Bound">A</a> <a id="4877" class="Symbol">:</a> <a id="4879" class="PrimitiveType">Set</a><a id="4882" class="Symbol">}</a> <a id="4884" class="Symbol">{</a><a id="4885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4885" class="Bound">x</a> <a id="4887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4887" class="Bound">y</a> <a id="4889" class="Symbol">:</a> <a id="4891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4875" class="Bound">A</a><a id="4892" class="Symbol">}</a> <a id="4894" class="Symbol">(</a><a id="4895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4895" class="Bound">P</a> <a id="4897" class="Symbol">:</a> <a id="4899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4875" class="Bound">A</a> <a id="4901" class="Symbol">→</a> <a id="4903" class="PrimitiveType">Set</a><a id="4906" class="Symbol">)</a>
  <a id="4910" class="Symbol">→</a> <a id="4912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4885" class="Bound">x</a> <a id="4914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="4916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4887" class="Bound">y</a>
    <a id="4922" class="Comment">---------</a>
  <a id="4934" class="Symbol">→</a> <a id="4936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4895" class="Bound">P</a> <a id="4938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4885" class="Bound">x</a> <a id="4940" class="Symbol">→</a> <a id="4942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4895" class="Bound">P</a> <a id="4944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4887" class="Bound">y</a>
<a id="4946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4864" class="Function">subst</a> <a id="4952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4952" class="Bound">P</a> <a id="4954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a> <a id="4959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4959" class="Bound">px</a> <a id="4962" class="Symbol">=</a> <a id="4964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4959" class="Bound">px</a>{% endraw %}</pre>


## Chains of equations

Here we show how to support reasoning with chains of equations
as used throughout the book.  We package the declarations
into a module, named `≡-Reasoning`, to match the format used in Agda's
standard library.
<pre class="Agda">{% raw %}<a id="5227" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="5234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5234" class="Module">≡-Reasoning</a> <a id="5246" class="Symbol">{</a><a id="5247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5247" class="Bound">A</a> <a id="5249" class="Symbol">:</a> <a id="5251" class="PrimitiveType">Set</a><a id="5254" class="Symbol">}</a> <a id="5256" class="Keyword">where</a>

  <a id="5265" class="Keyword">infix</a>  <a id="5272" class="Number">1</a> <a id="5274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5322" class="Function Operator">begin_</a>
  <a id="5283" class="Keyword">infixr</a> <a id="5290" class="Number">2</a> <a id="5292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5402" class="Function Operator">_≡⟨⟩_</a> <a id="5298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">_≡⟨_⟩_</a>
  <a id="5307" class="Keyword">infix</a>  <a id="5314" class="Number">3</a> <a id="5316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="5322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5322" class="Function Operator">begin_</a> <a id="5329" class="Symbol">:</a> <a id="5331" class="Symbol">∀</a> <a id="5333" class="Symbol">{</a><a id="5334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5334" class="Bound">x</a> <a id="5336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5336" class="Bound">y</a> <a id="5338" class="Symbol">:</a> <a id="5340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5247" class="Bound">A</a><a id="5341" class="Symbol">}</a>
    <a id="5347" class="Symbol">→</a> <a id="5349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5334" class="Bound">x</a> <a id="5351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5336" class="Bound">y</a>
      <a id="5361" class="Comment">-----</a>
    <a id="5371" class="Symbol">→</a> <a id="5373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5334" class="Bound">x</a> <a id="5375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5336" class="Bound">y</a>
  <a id="5381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5322" class="Function Operator">begin</a> <a id="5387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5387" class="Bound">x≡y</a>  <a id="5392" class="Symbol">=</a>  <a id="5395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5387" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="5402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5402" class="Function Operator">_≡⟨⟩_</a> <a id="5408" class="Symbol">:</a> <a id="5410" class="Symbol">∀</a> <a id="5412" class="Symbol">(</a><a id="5413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5413" class="Bound">x</a> <a id="5415" class="Symbol">:</a> <a id="5417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5247" class="Bound">A</a><a id="5418" class="Symbol">)</a> <a id="5420" class="Symbol">{</a><a id="5421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5421" class="Bound">y</a> <a id="5423" class="Symbol">:</a> <a id="5425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5247" class="Bound">A</a><a id="5426" class="Symbol">}</a>
    <a id="5432" class="Symbol">→</a> <a id="5434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5413" class="Bound">x</a> <a id="5436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5421" class="Bound">y</a>
      <a id="5446" class="Comment">-----</a>
    <a id="5456" class="Symbol">→</a> <a id="5458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5413" class="Bound">x</a> <a id="5460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5421" class="Bound">y</a>
  <a id="5466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5466" class="Bound">x</a> <a id="5468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5402" class="Function Operator">≡⟨⟩</a> <a id="5472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5472" class="Bound">x≡y</a>  <a id="5477" class="Symbol">=</a>  <a id="5480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5472" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="5487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">_≡⟨_⟩_</a> <a id="5494" class="Symbol">:</a> <a id="5496" class="Symbol">∀</a> <a id="5498" class="Symbol">(</a><a id="5499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5499" class="Bound">x</a> <a id="5501" class="Symbol">:</a> <a id="5503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5247" class="Bound">A</a><a id="5504" class="Symbol">)</a> <a id="5506" class="Symbol">{</a><a id="5507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5507" class="Bound">y</a> <a id="5509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5509" class="Bound">z</a> <a id="5511" class="Symbol">:</a> <a id="5513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5247" class="Bound">A</a><a id="5514" class="Symbol">}</a>
    <a id="5520" class="Symbol">→</a> <a id="5522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5499" class="Bound">x</a> <a id="5524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5507" class="Bound">y</a>
    <a id="5532" class="Symbol">→</a> <a id="5534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5507" class="Bound">y</a> <a id="5536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5509" class="Bound">z</a>
      <a id="5546" class="Comment">-----</a>
    <a id="5556" class="Symbol">→</a> <a id="5558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5499" class="Bound">x</a> <a id="5560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5509" class="Bound">z</a>
  <a id="5566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5566" class="Bound">x</a> <a id="5568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">≡⟨</a> <a id="5571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5571" class="Bound">x≡y</a> <a id="5575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">⟩</a> <a id="5577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5577" class="Bound">y≡z</a>  <a id="5582" class="Symbol">=</a>  <a id="5585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3642" class="Function">trans</a> <a id="5591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5571" class="Bound">x≡y</a> <a id="5595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5577" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="5602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Function Operator">_∎</a> <a id="5605" class="Symbol">:</a> <a id="5607" class="Symbol">∀</a> <a id="5609" class="Symbol">(</a><a id="5610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5610" class="Bound">x</a> <a id="5612" class="Symbol">:</a> <a id="5614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5247" class="Bound">A</a><a id="5615" class="Symbol">)</a>
      <a id="5623" class="Comment">-----</a>
    <a id="5633" class="Symbol">→</a> <a id="5635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5610" class="Bound">x</a> <a id="5637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="5639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5610" class="Bound">x</a>
  <a id="5643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5643" class="Bound">x</a> <a id="5645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Function Operator">∎</a>  <a id="5648" class="Symbol">=</a>  <a id="5651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>

<a id="5657" class="Keyword">open</a> <a id="5662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5234" class="Module">≡-Reasoning</a>{% endraw %}</pre>
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.

As an example, let's look at a proof of transitivity
as a chain of equations.
<pre class="Agda">{% raw %}<a id="trans′"></a><a id="6303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6303" class="Function">trans′</a> <a id="6310" class="Symbol">:</a> <a id="6312" class="Symbol">∀</a> <a id="6314" class="Symbol">{</a><a id="6315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6315" class="Bound">A</a> <a id="6317" class="Symbol">:</a> <a id="6319" class="PrimitiveType">Set</a><a id="6322" class="Symbol">}</a> <a id="6324" class="Symbol">{</a><a id="6325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6325" class="Bound">x</a> <a id="6327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6327" class="Bound">y</a> <a id="6329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6329" class="Bound">z</a> <a id="6331" class="Symbol">:</a> <a id="6333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6315" class="Bound">A</a><a id="6334" class="Symbol">}</a>
  <a id="6338" class="Symbol">→</a> <a id="6340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6325" class="Bound">x</a> <a id="6342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="6344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6327" class="Bound">y</a>
  <a id="6348" class="Symbol">→</a> <a id="6350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6327" class="Bound">y</a> <a id="6352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="6354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6329" class="Bound">z</a>
    <a id="6360" class="Comment">-----</a>
  <a id="6368" class="Symbol">→</a> <a id="6370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6325" class="Bound">x</a> <a id="6372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="6374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6329" class="Bound">z</a>
<a id="6376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6303" class="Function">trans′</a> <a id="6383" class="Symbol">{</a><a id="6384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6384" class="Bound">A</a><a id="6385" class="Symbol">}</a> <a id="6387" class="Symbol">{</a><a id="6388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6388" class="Bound">x</a><a id="6389" class="Symbol">}</a> <a id="6391" class="Symbol">{</a><a id="6392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6392" class="Bound">y</a><a id="6393" class="Symbol">}</a> <a id="6395" class="Symbol">{</a><a id="6396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6396" class="Bound">z</a><a id="6397" class="Symbol">}</a> <a id="6399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6399" class="Bound">x≡y</a> <a id="6403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6403" class="Bound">y≡z</a> <a id="6407" class="Symbol">=</a>
  <a id="6411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5322" class="Function Operator">begin</a>
    <a id="6421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6388" class="Bound">x</a>
  <a id="6425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">≡⟨</a> <a id="6428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6399" class="Bound">x≡y</a> <a id="6432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">⟩</a>
    <a id="6438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6392" class="Bound">y</a>
  <a id="6442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">≡⟨</a> <a id="6445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6403" class="Bound">y≡z</a> <a id="6449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">⟩</a>
    <a id="6455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6396" class="Bound">z</a>
  <a id="6459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Function Operator">∎</a>{% endraw %}</pre>
According to the fixity declarations, the body parses as follows:

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` than ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict.
<pre class="Agda">{% raw %}<a id="8160" class="Keyword">data</a> <a id="ℕ"></a><a id="8165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a> <a id="8167" class="Symbol">:</a> <a id="8169" class="PrimitiveType">Set</a> <a id="8173" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="8181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a> <a id="8186" class="Symbol">:</a> <a id="8188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="8192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a>  <a id="8197" class="Symbol">:</a> <a id="8199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a> <a id="8201" class="Symbol">→</a> <a id="8203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="8206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">_+_</a> <a id="8210" class="Symbol">:</a> <a id="8212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a> <a id="8214" class="Symbol">→</a> <a id="8216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a> <a id="8218" class="Symbol">→</a> <a id="8220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a>
<a id="8222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a>    <a id="8230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8232" class="Bound">n</a>  <a id="8235" class="Symbol">=</a>  <a id="8238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8232" class="Bound">n</a>
<a id="8240" class="Symbol">(</a><a id="8241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="8245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="Bound">m</a><a id="8246" class="Symbol">)</a> <a id="8248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8250" class="Bound">n</a>  <a id="8253" class="Symbol">=</a>  <a id="8256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="8260" class="Symbol">(</a><a id="8261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="Bound">m</a> <a id="8263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8250" class="Bound">n</a><a id="8266" class="Symbol">)</a>{% endraw %}</pre>

To save space we postulate (rather than prove in full) two lemmas.
<pre class="Agda">{% raw %}<a id="8360" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="8372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8372" class="Postulate">+-identity</a> <a id="8383" class="Symbol">:</a> <a id="8385" class="Symbol">∀</a> <a id="8387" class="Symbol">(</a><a id="8388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8388" class="Bound">m</a> <a id="8390" class="Symbol">:</a> <a id="8392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="8393" class="Symbol">)</a> <a id="8395" class="Symbol">→</a> <a id="8397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8388" class="Bound">m</a> <a id="8399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a> <a id="8406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="8408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8388" class="Bound">m</a>
  <a id="+-suc"></a><a id="8412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8412" class="Postulate">+-suc</a> <a id="8418" class="Symbol">:</a> <a id="8420" class="Symbol">∀</a> <a id="8422" class="Symbol">(</a><a id="8423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8423" class="Bound">m</a> <a id="8425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Bound">n</a> <a id="8427" class="Symbol">:</a> <a id="8429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="8430" class="Symbol">)</a> <a id="8432" class="Symbol">→</a> <a id="8434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8423" class="Bound">m</a> <a id="8436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="8442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Bound">n</a> <a id="8444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="8446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="8450" class="Symbol">(</a><a id="8451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8423" class="Bound">m</a> <a id="8453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Bound">n</a><a id="8456" class="Symbol">)</a>{% endraw %}</pre>
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="8822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="8829" class="Symbol">:</a> <a id="8831" class="Symbol">∀</a> <a id="8833" class="Symbol">(</a><a id="8834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8834" class="Bound">m</a> <a id="8836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8836" class="Bound">n</a> <a id="8838" class="Symbol">:</a> <a id="8840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="8841" class="Symbol">)</a> <a id="8843" class="Symbol">→</a> <a id="8845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8834" class="Bound">m</a> <a id="8847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8836" class="Bound">n</a> <a id="8851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="8853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8836" class="Bound">n</a> <a id="8855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8834" class="Bound">m</a>
<a id="8859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="8866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8866" class="Bound">m</a> <a id="8868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a> <a id="8873" class="Symbol">=</a>
  <a id="8877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5322" class="Function Operator">begin</a>
    <a id="8887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8866" class="Bound">m</a> <a id="8889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a>
  <a id="8898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">≡⟨</a> <a id="8901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8372" class="Postulate">+-identity</a> <a id="8912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8866" class="Bound">m</a> <a id="8914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">⟩</a>
    <a id="8920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8866" class="Bound">m</a>
  <a id="8924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5402" class="Function Operator">≡⟨⟩</a>
    <a id="8932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a> <a id="8937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8866" class="Bound">m</a>
  <a id="8943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Function Operator">∎</a>
<a id="8945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="8952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8952" class="Bound">m</a> <a id="8954" class="Symbol">(</a><a id="8955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="8959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8959" class="Bound">n</a><a id="8960" class="Symbol">)</a> <a id="8962" class="Symbol">=</a>
  <a id="8966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5322" class="Function Operator">begin</a>
    <a id="8976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8952" class="Bound">m</a> <a id="8978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="8980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="8984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8959" class="Bound">n</a>
  <a id="8988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">≡⟨</a> <a id="8991" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8412" class="Postulate">+-suc</a> <a id="8997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8952" class="Bound">m</a> <a id="8999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8959" class="Bound">n</a> <a id="9001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">⟩</a>
    <a id="9007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="9011" class="Symbol">(</a><a id="9012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8952" class="Bound">m</a> <a id="9014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="9016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8959" class="Bound">n</a><a id="9017" class="Symbol">)</a>
  <a id="9021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">≡⟨</a> <a id="9024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4074" class="Function">cong</a> <a id="9029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="9033" class="Symbol">(</a><a id="9034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="9041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8952" class="Bound">m</a> <a id="9043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8959" class="Bound">n</a><a id="9044" class="Symbol">)</a> <a id="9046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5487" class="Function Operator">⟩</a>
    <a id="9052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="9056" class="Symbol">(</a><a id="9057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8959" class="Bound">n</a> <a id="9059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="9061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8952" class="Bound">m</a><a id="9062" class="Symbol">)</a>
  <a id="9066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5402" class="Function Operator">≡⟨⟩</a>
    <a id="9074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="9078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8959" class="Bound">n</a> <a id="9080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="9082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8952" class="Bound">m</a>
  <a id="9086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Function Operator">∎</a>{% endraw %}</pre>
The reasoning here is similar to that in the
preceding section, the one addition being the use of
`_≡⟨⟩_`, which we use when no justification is required.
One can think of occurrences of `≡⟨⟩` as an equivalent
to `≡⟨ refl ⟩`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.


#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md %})
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition.
<pre class="Agda">{% raw %}<a id="10351" class="Keyword">data</a> <a id="even"></a><a id="10356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="10361" class="Symbol">:</a> <a id="10363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a> <a id="10365" class="Symbol">→</a> <a id="10367" class="PrimitiveType">Set</a>
<a id="10371" class="Keyword">data</a> <a id="odd"></a><a id="10376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10376" class="Datatype">odd</a>  <a id="10381" class="Symbol">:</a> <a id="10383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a> <a id="10385" class="Symbol">→</a> <a id="10387" class="PrimitiveType">Set</a>

<a id="10392" class="Keyword">data</a> <a id="10397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="10402" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="10411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10411" class="InductiveConstructor">even-zero</a> <a id="10421" class="Symbol">:</a> <a id="10423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="10428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="10436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10436" class="InductiveConstructor">even-suc</a> <a id="10445" class="Symbol">:</a> <a id="10447" class="Symbol">∀</a> <a id="10449" class="Symbol">{</a><a id="10450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10450" class="Bound">n</a> <a id="10452" class="Symbol">:</a> <a id="10454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="10455" class="Symbol">}</a>
    <a id="10461" class="Symbol">→</a> <a id="10463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10376" class="Datatype">odd</a> <a id="10467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10450" class="Bound">n</a>
      <a id="10475" class="Comment">------------</a>
    <a id="10492" class="Symbol">→</a> <a id="10494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="10499" class="Symbol">(</a><a id="10500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="10504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10450" class="Bound">n</a><a id="10505" class="Symbol">)</a>

<a id="10508" class="Keyword">data</a> <a id="10513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10376" class="Datatype">odd</a> <a id="10517" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="10525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10525" class="InductiveConstructor">odd-suc</a> <a id="10533" class="Symbol">:</a> <a id="10535" class="Symbol">∀</a> <a id="10537" class="Symbol">{</a><a id="10538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10538" class="Bound">n</a> <a id="10540" class="Symbol">:</a> <a id="10542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="10543" class="Symbol">}</a>
    <a id="10549" class="Symbol">→</a> <a id="10551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="10556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10538" class="Bound">n</a>
      <a id="10564" class="Comment">-----------</a>
    <a id="10580" class="Symbol">→</a> <a id="10582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10376" class="Datatype">odd</a> <a id="10586" class="Symbol">(</a><a id="10587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="10591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10538" class="Bound">n</a><a id="10592" class="Symbol">)</a>{% endraw %}</pre>
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.

Agda includes special notation to support just this kind of reasoning.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equivalence.
<pre class="Agda">{% raw %}<a id="10962" class="Symbol">{-#</a> <a id="10966" class="Keyword">BUILTIN</a> EQUALITY <a id="10983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">_≡_</a> <a id="10987" class="Symbol">#-}</a>{% endraw %}</pre>

We can then prove the desired property as follows.
<pre class="Agda">{% raw %}<a id="even-comm"></a><a id="11067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11067" class="Function">even-comm</a> <a id="11077" class="Symbol">:</a> <a id="11079" class="Symbol">∀</a> <a id="11081" class="Symbol">(</a><a id="11082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11082" class="Bound">m</a> <a id="11084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11084" class="Bound">n</a> <a id="11086" class="Symbol">:</a> <a id="11088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="11089" class="Symbol">)</a>
  <a id="11093" class="Symbol">→</a> <a id="11095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="11100" class="Symbol">(</a><a id="11101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11082" class="Bound">m</a> <a id="11103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="11105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11084" class="Bound">n</a><a id="11106" class="Symbol">)</a>
    <a id="11112" class="Comment">------------</a>
  <a id="11127" class="Symbol">→</a> <a id="11129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="11134" class="Symbol">(</a><a id="11135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11084" class="Bound">n</a> <a id="11137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="11139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11082" class="Bound">m</a><a id="11140" class="Symbol">)</a>
<a id="11142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11067" class="Function">even-comm</a> <a id="11152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11152" class="Bound">m</a> <a id="11154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="Bound">n</a> <a id="11156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11156" class="Bound">ev</a>  <a id="11160" class="Keyword">rewrite</a> <a id="11168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="11175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11152" class="Bound">m</a> <a id="11177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11154" class="Bound">n</a>  <a id="11180" class="Symbol">=</a>  <a id="11183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11156" class="Bound">ev</a>{% endraw %}</pre>
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it is also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equivalence, and that equivalence is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite.

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm m n = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (n + m)
    n  : ℕ
    m  : ℕ

The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities.
<pre class="Agda">{% raw %}<a id="+-comm′"></a><a id="12737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12737" class="Function">+-comm′</a> <a id="12745" class="Symbol">:</a> <a id="12747" class="Symbol">∀</a> <a id="12749" class="Symbol">(</a><a id="12750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12750" class="Bound">m</a> <a id="12752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12752" class="Bound">n</a> <a id="12754" class="Symbol">:</a> <a id="12756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="12757" class="Symbol">)</a> <a id="12759" class="Symbol">→</a> <a id="12761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12750" class="Bound">m</a> <a id="12763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="12765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12752" class="Bound">n</a> <a id="12767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="12769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12752" class="Bound">n</a> <a id="12771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="12773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12750" class="Bound">m</a>
<a id="12775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12737" class="Function">+-comm′</a> <a id="12783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8181" class="InductiveConstructor">zero</a>    <a id="12791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12791" class="Bound">n</a>  <a id="12794" class="Keyword">rewrite</a> <a id="12802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8372" class="Postulate">+-identity</a> <a id="12813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12791" class="Bound">n</a>            <a id="12826" class="Symbol">=</a>  <a id="12829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>
<a id="12834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12737" class="Function">+-comm′</a> <a id="12842" class="Symbol">(</a><a id="12843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8192" class="InductiveConstructor">suc</a> <a id="12847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12847" class="Bound">m</a><a id="12848" class="Symbol">)</a> <a id="12850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12850" class="Bound">n</a>  <a id="12853" class="Keyword">rewrite</a> <a id="12861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8412" class="Postulate">+-suc</a> <a id="12867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12850" class="Bound">n</a> <a id="12869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12847" class="Bound">m</a> <a id="12871" class="Symbol">|</a> <a id="12873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="12880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12847" class="Bound">m</a> <a id="12882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12850" class="Bound">n</a>  <a id="12885" class="Symbol">=</a>  <a id="12888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>{% endraw %}</pre>
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction.
<pre class="Agda">{% raw %}<a id="even-comm′"></a><a id="13453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13453" class="Function">even-comm′</a> <a id="13464" class="Symbol">:</a> <a id="13466" class="Symbol">∀</a> <a id="13468" class="Symbol">(</a><a id="13469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13469" class="Bound">m</a> <a id="13471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13471" class="Bound">n</a> <a id="13473" class="Symbol">:</a> <a id="13475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="13476" class="Symbol">)</a>
  <a id="13480" class="Symbol">→</a> <a id="13482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="13487" class="Symbol">(</a><a id="13488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13469" class="Bound">m</a> <a id="13490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="13492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13471" class="Bound">n</a><a id="13493" class="Symbol">)</a>
    <a id="13499" class="Comment">------------</a>
  <a id="13514" class="Symbol">→</a> <a id="13516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="13521" class="Symbol">(</a><a id="13522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13471" class="Bound">n</a> <a id="13524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="13526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13469" class="Bound">m</a><a id="13527" class="Symbol">)</a>
<a id="13529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13453" class="Function">even-comm′</a> <a id="13540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13540" class="Bound">m</a> <a id="13542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13542" class="Bound">n</a> <a id="13544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13544" class="Bound">ev</a> <a id="13547" class="Keyword">with</a>   <a id="13554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13540" class="Bound">m</a> <a id="13556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="13558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13542" class="Bound">n</a>  <a id="13561" class="Symbol">|</a> <a id="13563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="13570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13540" class="Bound">m</a> <a id="13572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13542" class="Bound">n</a>
<a id="13574" class="Symbol">...</a>                  <a id="13595" class="Symbol">|</a> <a id="13597" class="DottedPattern Symbol">.(</a><a id="13599" class="DottedPattern Bound">n</a> <a id="13601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="DottedPattern Function Operator">+</a> <a id="13603" class="DottedPattern Bound">m</a><a id="13604" class="DottedPattern Symbol">)</a> <a id="13606" class="Symbol">|</a> <a id="13608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>        <a id="13620" class="Symbol">=</a> <a id="13622" class="Bound">ev</a>{% endraw %}</pre>
The first clause asserts that `m + n` and `n + m` are identical, and
the second clause justifies that assertion with evidence of the
appropriate equivalence.  Note the use of the _dot pattern_, `.(n +
m)`.  A dot pattern consists of a dot followed by an expression, and
is used when other information forces the value matched to be equal to
the value of the expression in the dot pattern.  In this case, the
identification of `m + n` and `n + m` is justified by the subsequent
matching of `+-comm m n` against `refl`.  One might think that the
first clause is redundant as the information is inherent in the second
clause, but in fact Agda is rather picky on this point: omitting the
first clause or reversing the order of the clauses will cause Agda to
report an error.  (Try it and see!)

In this case, we can avoid rewrite by simply applying substitution.
<pre class="Agda">{% raw %}<a id="even-comm″"></a><a id="14508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14508" class="Function">even-comm″</a> <a id="14519" class="Symbol">:</a> <a id="14521" class="Symbol">∀</a> <a id="14523" class="Symbol">(</a><a id="14524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14524" class="Bound">m</a> <a id="14526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14526" class="Bound">n</a> <a id="14528" class="Symbol">:</a> <a id="14530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8165" class="Datatype">ℕ</a><a id="14531" class="Symbol">)</a>
  <a id="14535" class="Symbol">→</a> <a id="14537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="14542" class="Symbol">(</a><a id="14543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14524" class="Bound">m</a> <a id="14545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="14547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14526" class="Bound">n</a><a id="14548" class="Symbol">)</a>
    <a id="14554" class="Comment">------------</a>
  <a id="14569" class="Symbol">→</a> <a id="14571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="14576" class="Symbol">(</a><a id="14577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14526" class="Bound">n</a> <a id="14579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8206" class="Function Operator">+</a> <a id="14581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14524" class="Bound">m</a><a id="14582" class="Symbol">)</a>
<a id="14584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14508" class="Function">even-comm″</a> <a id="14595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14595" class="Bound">m</a> <a id="14597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14597" class="Bound">n</a>  <a id="14600" class="Symbol">=</a>  <a id="14603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4864" class="Function">subst</a> <a id="14609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10356" class="Datatype">even</a> <a id="14614" class="Symbol">(</a><a id="14615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8822" class="Function">+-comm</a> <a id="14622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14595" class="Bound">m</a> <a id="14624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14597" class="Bound">n</a><a id="14625" class="Symbol">)</a>{% endraw %}</pre>
Nonetheless, rewrite is a vital part of the Agda toolkit,
as earlier examples have shown.


## Leibniz equality

The form of asserting equivalence that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equivalence.

Leibniz equality is usually formalised to state that `x ≐ y`
holds if every property `P` that holds of `x` also holds of
`y`.  Perhaps surprisingly, this definition is
sufficient to also ensure the converse, that every property `P` that
holds of `y` also holds of `x`.

Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`.
<pre class="Agda">{% raw %}<a id="_≐_"></a><a id="15749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">_≐_</a> <a id="15753" class="Symbol">:</a> <a id="15755" class="Symbol">∀</a> <a id="15757" class="Symbol">{</a><a id="15758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15758" class="Bound">A</a> <a id="15760" class="Symbol">:</a> <a id="15762" class="PrimitiveType">Set</a><a id="15765" class="Symbol">}</a> <a id="15767" class="Symbol">(</a><a id="15768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15768" class="Bound">x</a> <a id="15770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15770" class="Bound">y</a> <a id="15772" class="Symbol">:</a> <a id="15774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15758" class="Bound">A</a><a id="15775" class="Symbol">)</a> <a id="15777" class="Symbol">→</a> <a id="15779" class="PrimitiveType">Set₁</a>
<a id="15784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">_≐_</a> <a id="15788" class="Symbol">{</a><a id="15789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15789" class="Bound">A</a><a id="15790" class="Symbol">}</a> <a id="15792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15792" class="Bound">x</a> <a id="15794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15794" class="Bound">y</a> <a id="15796" class="Symbol">=</a> <a id="15798" class="Symbol">∀</a> <a id="15800" class="Symbol">(</a><a id="15801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15801" class="Bound">P</a> <a id="15803" class="Symbol">:</a> <a id="15805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15789" class="Bound">A</a> <a id="15807" class="Symbol">→</a> <a id="15809" class="PrimitiveType">Set</a><a id="15812" class="Symbol">)</a> <a id="15814" class="Symbol">→</a> <a id="15816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15801" class="Bound">P</a> <a id="15818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15792" class="Bound">x</a> <a id="15820" class="Symbol">→</a> <a id="15822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15801" class="Bound">P</a> <a id="15824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15794" class="Bound">y</a>{% endraw %}</pre>
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russel's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition.
<pre class="Agda">{% raw %}<a id="refl-≐"></a><a id="16663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16663" class="Function">refl-≐</a> <a id="16670" class="Symbol">:</a> <a id="16672" class="Symbol">∀</a> <a id="16674" class="Symbol">{</a><a id="16675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16675" class="Bound">A</a> <a id="16677" class="Symbol">:</a> <a id="16679" class="PrimitiveType">Set</a><a id="16682" class="Symbol">}</a> <a id="16684" class="Symbol">{</a><a id="16685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16685" class="Bound">x</a> <a id="16687" class="Symbol">:</a> <a id="16689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16675" class="Bound">A</a><a id="16690" class="Symbol">}</a>
  <a id="16694" class="Symbol">→</a> <a id="16696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16685" class="Bound">x</a> <a id="16698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="16700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16685" class="Bound">x</a>
<a id="16702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16663" class="Function">refl-≐</a> <a id="16709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16709" class="Bound">P</a> <a id="16711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16711" class="Bound">Px</a>  <a id="16715" class="Symbol">=</a>  <a id="16718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16711" class="Bound">Px</a>

<a id="trans-≐"></a><a id="16722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16722" class="Function">trans-≐</a> <a id="16730" class="Symbol">:</a> <a id="16732" class="Symbol">∀</a> <a id="16734" class="Symbol">{</a><a id="16735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16735" class="Bound">A</a> <a id="16737" class="Symbol">:</a> <a id="16739" class="PrimitiveType">Set</a><a id="16742" class="Symbol">}</a> <a id="16744" class="Symbol">{</a><a id="16745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16745" class="Bound">x</a> <a id="16747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16747" class="Bound">y</a> <a id="16749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16749" class="Bound">z</a> <a id="16751" class="Symbol">:</a> <a id="16753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16735" class="Bound">A</a><a id="16754" class="Symbol">}</a>
  <a id="16758" class="Symbol">→</a> <a id="16760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16745" class="Bound">x</a> <a id="16762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="16764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16747" class="Bound">y</a>
  <a id="16768" class="Symbol">→</a> <a id="16770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16747" class="Bound">y</a> <a id="16772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="16774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16749" class="Bound">z</a>
    <a id="16780" class="Comment">-----</a>
  <a id="16788" class="Symbol">→</a> <a id="16790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16745" class="Bound">x</a> <a id="16792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="16794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16749" class="Bound">z</a>
<a id="16796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16722" class="Function">trans-≐</a> <a id="16804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16804" class="Bound">x≐y</a> <a id="16808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16808" class="Bound">y≐z</a> <a id="16812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16812" class="Bound">P</a> <a id="16814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16814" class="Bound">Px</a>  <a id="16818" class="Symbol">=</a>  <a id="16821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16808" class="Bound">y≐z</a> <a id="16825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16812" class="Bound">P</a> <a id="16827" class="Symbol">(</a><a id="16828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16804" class="Bound">x≐y</a> <a id="16832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16812" class="Bound">P</a> <a id="16834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16814" class="Bound">Px</a><a id="16836" class="Symbol">)</a>{% endraw %}</pre>

Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well.
<pre class="Agda">{% raw %}<a id="sym-≐"></a><a id="17014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17014" class="Function">sym-≐</a> <a id="17020" class="Symbol">:</a> <a id="17022" class="Symbol">∀</a> <a id="17024" class="Symbol">{</a><a id="17025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17025" class="Bound">A</a> <a id="17027" class="Symbol">:</a> <a id="17029" class="PrimitiveType">Set</a><a id="17032" class="Symbol">}</a> <a id="17034" class="Symbol">{</a><a id="17035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17035" class="Bound">x</a> <a id="17037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17037" class="Bound">y</a> <a id="17039" class="Symbol">:</a> <a id="17041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17025" class="Bound">A</a><a id="17042" class="Symbol">}</a>
  <a id="17046" class="Symbol">→</a> <a id="17048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17035" class="Bound">x</a> <a id="17050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="17052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17037" class="Bound">y</a>
    <a id="17058" class="Comment">-----</a>
  <a id="17066" class="Symbol">→</a> <a id="17068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17037" class="Bound">y</a> <a id="17070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="17072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17035" class="Bound">x</a>
<a id="17074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17014" class="Function">sym-≐</a> <a id="17080" class="Symbol">{</a><a id="17081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17081" class="Bound">A</a><a id="17082" class="Symbol">}</a> <a id="17084" class="Symbol">{</a><a id="17085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17085" class="Bound">x</a><a id="17086" class="Symbol">}</a> <a id="17088" class="Symbol">{</a><a id="17089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17089" class="Bound">y</a><a id="17090" class="Symbol">}</a> <a id="17092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17092" class="Bound">x≐y</a> <a id="17096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17096" class="Bound">P</a>  <a id="17099" class="Symbol">=</a>  <a id="17102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17184" class="Function">Qy</a>
  <a id="17107" class="Keyword">where</a>
    <a id="17117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Function">Q</a> <a id="17119" class="Symbol">:</a> <a id="17121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17081" class="Bound">A</a> <a id="17123" class="Symbol">→</a> <a id="17125" class="PrimitiveType">Set</a>
    <a id="17133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Function">Q</a> <a id="17135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17135" class="Bound">z</a> <a id="17137" class="Symbol">=</a> <a id="17139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17096" class="Bound">P</a> <a id="17141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17135" class="Bound">z</a> <a id="17143" class="Symbol">→</a> <a id="17145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17096" class="Bound">P</a> <a id="17147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17085" class="Bound">x</a>
    <a id="17153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17153" class="Function">Qx</a> <a id="17156" class="Symbol">:</a> <a id="17158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Function">Q</a> <a id="17160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17085" class="Bound">x</a>
    <a id="17166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17153" class="Function">Qx</a> <a id="17169" class="Symbol">=</a> <a id="17171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16663" class="Function">refl-≐</a> <a id="17178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17096" class="Bound">P</a>
    <a id="17184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17184" class="Function">Qy</a> <a id="17187" class="Symbol">:</a> <a id="17189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Function">Q</a> <a id="17191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17089" class="Bound">y</a>
    <a id="17197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17184" class="Function">Qy</a> <a id="17200" class="Symbol">=</a> <a id="17202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17092" class="Bound">x≐y</a> <a id="17206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Function">Q</a> <a id="17208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17153" class="Function">Qx</a>{% endraw %}</pre>
Given `x ≐ y`, a specific `P`, a proof of `P y`, we have to
construct a proof of `P x`.  To do so, we instantiate the equality
with a predicate `Q` such that `Q z` holds if `P z` implies `P x`.
The property `Q x` is trivial by reflexivity, and hence `Q y` follows
from `x ≐ y`.  But `Q y` is exactly a proof of what we require, that
`P y` implies `P x`.

We now show that Martin Löf equivalence implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equivalence of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`.
<pre class="Agda">{% raw %}<a id="≡-implies-≐"></a><a id="17891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17891" class="Function">≡-implies-≐</a> <a id="17903" class="Symbol">:</a> <a id="17905" class="Symbol">∀</a> <a id="17907" class="Symbol">{</a><a id="17908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17908" class="Bound">A</a> <a id="17910" class="Symbol">:</a> <a id="17912" class="PrimitiveType">Set</a><a id="17915" class="Symbol">}</a> <a id="17917" class="Symbol">{</a><a id="17918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17918" class="Bound">x</a> <a id="17920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17920" class="Bound">y</a> <a id="17922" class="Symbol">:</a> <a id="17924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17908" class="Bound">A</a><a id="17925" class="Symbol">}</a>
  <a id="17929" class="Symbol">→</a> <a id="17931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17918" class="Bound">x</a> <a id="17933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="17935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17920" class="Bound">y</a>
    <a id="17941" class="Comment">-----</a>
  <a id="17949" class="Symbol">→</a> <a id="17951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17918" class="Bound">x</a> <a id="17953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="17955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17920" class="Bound">y</a>
<a id="17957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17891" class="Function">≡-implies-≐</a> <a id="17969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17969" class="Bound">x≡y</a> <a id="17973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17973" class="Bound">P</a>  <a id="17976" class="Symbol">=</a>  <a id="17979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4864" class="Function">subst</a> <a id="17985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17973" class="Bound">P</a> <a id="17987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17969" class="Bound">x≡y</a>{% endraw %}</pre>
This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`. 
<pre class="Agda">{% raw %}<a id="≐-implies-≡"></a><a id="18207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18207" class="Function">≐-implies-≡</a> <a id="18219" class="Symbol">:</a> <a id="18221" class="Symbol">∀</a> <a id="18223" class="Symbol">{</a><a id="18224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18224" class="Bound">A</a> <a id="18226" class="Symbol">:</a> <a id="18228" class="PrimitiveType">Set</a><a id="18231" class="Symbol">}</a> <a id="18233" class="Symbol">{</a><a id="18234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18234" class="Bound">x</a> <a id="18236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18236" class="Bound">y</a> <a id="18238" class="Symbol">:</a> <a id="18240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18224" class="Bound">A</a><a id="18241" class="Symbol">}</a>
  <a id="18245" class="Symbol">→</a> <a id="18247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18234" class="Bound">x</a> <a id="18249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15749" class="Function Operator">≐</a> <a id="18251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18236" class="Bound">y</a>
    <a id="18257" class="Comment">-----</a>
  <a id="18265" class="Symbol">→</a> <a id="18267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18234" class="Bound">x</a> <a id="18269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="18271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18236" class="Bound">y</a>
<a id="18273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18207" class="Function">≐-implies-≡</a> <a id="18285" class="Symbol">{</a><a id="18286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18286" class="Bound">A</a><a id="18287" class="Symbol">}</a> <a id="18289" class="Symbol">{</a><a id="18290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18290" class="Bound">x</a><a id="18291" class="Symbol">}</a> <a id="18293" class="Symbol">{</a><a id="18294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18294" class="Bound">y</a><a id="18295" class="Symbol">}</a> <a id="18297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18297" class="Bound">x≐y</a>  <a id="18302" class="Symbol">=</a>  <a id="18305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18379" class="Function">Qy</a>
  <a id="18310" class="Keyword">where</a>
    <a id="18320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18320" class="Function">Q</a> <a id="18322" class="Symbol">:</a> <a id="18324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18286" class="Bound">A</a> <a id="18326" class="Symbol">→</a> <a id="18328" class="PrimitiveType">Set</a>
    <a id="18336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18320" class="Function">Q</a> <a id="18338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18338" class="Bound">z</a> <a id="18340" class="Symbol">=</a> <a id="18342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18290" class="Bound">x</a> <a id="18344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#683" class="Datatype Operator">≡</a> <a id="18346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18338" class="Bound">z</a>
    <a id="18352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18352" class="Function">Qx</a> <a id="18355" class="Symbol">:</a> <a id="18357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18320" class="Function">Q</a> <a id="18359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18290" class="Bound">x</a>
    <a id="18365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18352" class="Function">Qx</a> <a id="18368" class="Symbol">=</a> <a id="18370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#723" class="InductiveConstructor">refl</a>
    <a id="18379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18379" class="Function">Qy</a> <a id="18382" class="Symbol">:</a> <a id="18384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18320" class="Function">Q</a> <a id="18386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18294" class="Bound">y</a>
    <a id="18392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18379" class="Function">Qy</a> <a id="18395" class="Symbol">=</a> <a id="18397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18297" class="Bound">x≐y</a> <a id="18401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18320" class="Function">Q</a> <a id="18403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18352" class="Function">Qx</a>{% endraw %}</pre>
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equivalence, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following.
<pre class="Agda">{% raw %}<a id="19577" class="Keyword">open</a> <a id="19582" class="Keyword">import</a> <a id="19589" href="https://agda.github.io/agda-stdlib/Level.html" class="Module">Level</a> <a id="19595" class="Keyword">using</a> <a id="19601" class="Symbol">(</a><a id="19602" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="19607" class="Symbol">;</a> <a id="19609" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="19612" class="Symbol">)</a> <a id="19614" class="Keyword">renaming</a> <a id="19623" class="Symbol">(</a><a id="19624" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">suc</a> <a id="19628" class="Symbol">to</a> <a id="19631" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="19635" class="Symbol">;</a> <a id="19637" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">zero</a> <a id="19642" class="Symbol">to</a> <a id="19645" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">lzero</a><a id="19650" class="Symbol">)</a>{% endraw %}</pre>
Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level.
<pre class="Agda">{% raw %}<a id="20123" class="Keyword">data</a> <a id="_≡′_"></a><a id="20128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20128" class="Datatype Operator">_≡′_</a> <a id="20133" class="Symbol">{</a><a id="20134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20134" class="Bound">ℓ</a> <a id="20136" class="Symbol">:</a> <a id="20138" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20143" class="Symbol">}</a> <a id="20145" class="Symbol">{</a><a id="20146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20146" class="Bound">A</a> <a id="20148" class="Symbol">:</a> <a id="20150" class="PrimitiveType">Set</a> <a id="20154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20134" class="Bound">ℓ</a><a id="20155" class="Symbol">}</a> <a id="20157" class="Symbol">:</a> <a id="20159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20146" class="Bound">A</a> <a id="20161" class="Symbol">→</a> <a id="20163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20146" class="Bound">A</a> <a id="20165" class="Symbol">→</a> <a id="20167" class="PrimitiveType">Set</a> <a id="20171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20134" class="Bound">ℓ</a> <a id="20173" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="20181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20181" class="InductiveConstructor">refl′</a> <a id="20187" class="Symbol">:</a> <a id="20189" class="Symbol">∀</a> <a id="20191" class="Symbol">{</a><a id="20192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20192" class="Bound">x</a> <a id="20194" class="Symbol">:</a> <a id="20196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20146" class="Bound">A</a><a id="20197" class="Symbol">}</a> <a id="20199" class="Symbol">→</a> <a id="20201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20192" class="Bound">x</a> <a id="20203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20128" class="Datatype Operator">≡′</a> <a id="20206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20192" class="Bound">x</a>{% endraw %}</pre>
Similarly, here is the generalised definition of symmetry.
<pre class="Agda">{% raw %}<a id="sym′"></a><a id="20291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20291" class="Function">sym′</a> <a id="20296" class="Symbol">:</a> <a id="20298" class="Symbol">∀</a> <a id="20300" class="Symbol">{</a><a id="20301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20301" class="Bound">ℓ</a> <a id="20303" class="Symbol">:</a> <a id="20305" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20310" class="Symbol">}</a> <a id="20312" class="Symbol">{</a><a id="20313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20313" class="Bound">A</a> <a id="20315" class="Symbol">:</a> <a id="20317" class="PrimitiveType">Set</a> <a id="20321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20301" class="Bound">ℓ</a><a id="20322" class="Symbol">}</a> <a id="20324" class="Symbol">{</a><a id="20325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20325" class="Bound">x</a> <a id="20327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20327" class="Bound">y</a> <a id="20329" class="Symbol">:</a> <a id="20331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20313" class="Bound">A</a><a id="20332" class="Symbol">}</a> <a id="20334" class="Symbol">→</a>  <a id="20337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20325" class="Bound">x</a> <a id="20339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20128" class="Datatype Operator">≡′</a> <a id="20342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20327" class="Bound">y</a> <a id="20344" class="Symbol">→</a> <a id="20346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20327" class="Bound">y</a> <a id="20348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20128" class="Datatype Operator">≡′</a> <a id="20351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20325" class="Bound">x</a>
<a id="20353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20291" class="Function">sym′</a> <a id="20358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20181" class="InductiveConstructor">refl′</a> <a id="20364" class="Symbol">=</a> <a id="20366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20181" class="InductiveConstructor">refl′</a>{% endraw %}</pre>
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality.
<pre class="Agda">{% raw %}<a id="_≐′_"></a><a id="20660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20660" class="Function Operator">_≐′_</a> <a id="20665" class="Symbol">:</a> <a id="20667" class="Symbol">∀</a> <a id="20669" class="Symbol">{</a><a id="20670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20670" class="Bound">ℓ</a> <a id="20672" class="Symbol">:</a> <a id="20674" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20679" class="Symbol">}</a> <a id="20681" class="Symbol">{</a><a id="20682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20682" class="Bound">A</a> <a id="20684" class="Symbol">:</a> <a id="20686" class="PrimitiveType">Set</a> <a id="20690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20670" class="Bound">ℓ</a><a id="20691" class="Symbol">}</a> <a id="20693" class="Symbol">(</a><a id="20694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20694" class="Bound">x</a> <a id="20696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20696" class="Bound">y</a> <a id="20698" class="Symbol">:</a> <a id="20700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20682" class="Bound">A</a><a id="20701" class="Symbol">)</a> <a id="20703" class="Symbol">→</a> <a id="20705" class="PrimitiveType">Set</a> <a id="20709" class="Symbol">(</a><a id="20710" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="20715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20670" class="Bound">ℓ</a><a id="20716" class="Symbol">)</a>
<a id="20718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20660" class="Function Operator">_≐′_</a> <a id="20723" class="Symbol">{</a><a id="20724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20724" class="Bound">ℓ</a><a id="20725" class="Symbol">}</a> <a id="20727" class="Symbol">{</a><a id="20728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20728" class="Bound">A</a><a id="20729" class="Symbol">}</a> <a id="20731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20731" class="Bound">x</a> <a id="20733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20733" class="Bound">y</a> <a id="20735" class="Symbol">=</a> <a id="20737" class="Symbol">∀</a> <a id="20739" class="Symbol">(</a><a id="20740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20740" class="Bound">P</a> <a id="20742" class="Symbol">:</a> <a id="20744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20728" class="Bound">A</a> <a id="20746" class="Symbol">→</a> <a id="20748" class="PrimitiveType">Set</a> <a id="20752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20724" class="Bound">ℓ</a><a id="20753" class="Symbol">)</a> <a id="20755" class="Symbol">→</a> <a id="20757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20740" class="Bound">P</a> <a id="20759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20731" class="Bound">x</a> <a id="20761" class="Symbol">→</a> <a id="20763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20740" class="Bound">P</a> <a id="20765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20733" class="Bound">y</a>{% endraw %}</pre>
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (suc ℓ)` as the type of a
term that includes `Set ℓ`.

Further information on levels can be found in
the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## Standard library

Definitions similar to those in this chapter can be found in the
standard library.
<pre class="Agda">{% raw %}<a id="21229" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="21283" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="21347" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>{% endraw %}</pre>
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.


## Unicode

This chapter uses the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
