---
src       : src/plfa/Relations.lagda
title     : "Relations: Inductive definition of relations"
layout    : page
permalink : /Relations/
---

<pre class="Agda">{% raw %}<a id="123" class="Keyword">module</a> <a id="130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="145" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<pre class="Agda">{% raw %}<a id="326" class="Keyword">import</a> <a id="333" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="371" class="Symbol">as</a> <a id="374" class="Module">Eq</a>
<a id="377" class="Keyword">open</a> <a id="382" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="385" class="Keyword">using</a> <a id="391" class="Symbol">(</a><a id="392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="395" class="Symbol">;</a> <a id="397" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="401" class="Symbol">;</a> <a id="403" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a><a id="407" class="Symbol">;</a> <a id="409" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#560" class="Function">sym</a><a id="412" class="Symbol">)</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="435" class="Keyword">using</a> <a id="441" class="Symbol">(</a><a id="442" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="443" class="Symbol">;</a> <a id="445" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="449" class="Symbol">;</a> <a id="451" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="454" class="Symbol">;</a> <a id="456" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="459" class="Symbol">;</a> <a id="461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="464" class="Symbol">;</a> <a id="466" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="469" class="Symbol">)</a>
<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="503" class="Keyword">using</a> <a id="509" class="Symbol">(</a><a id="510" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a><a id="516" class="Symbol">;</a> <a id="518" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7679" class="Function">+-suc</a><a id="523" class="Symbol">)</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="https://agda.github.io/agda-stdlib/Data.List.html" class="Module">Data.List</a> <a id="547" class="Keyword">using</a> <a id="553" class="Symbol">(</a><a id="554" href="https://agda.github.io/agda-stdlib/Agda.Builtin.List.html#80" class="Datatype">List</a><a id="558" class="Symbol">;</a> <a id="560" href="https://agda.github.io/agda-stdlib/Data.List.Base.html#7506" class="InductiveConstructor">[]</a><a id="562" class="Symbol">;</a> <a id="564" href="https://agda.github.io/agda-stdlib/Agda.Builtin.List.html#132" class="InductiveConstructor Operator">_∷_</a><a id="567" class="Symbol">)</a>
<a id="569" class="Keyword">open</a> <a id="574" class="Keyword">import</a> <a id="581" href="https://agda.github.io/agda-stdlib/Function.html" class="Module">Function</a> <a id="590" class="Keyword">using</a> <a id="596" class="Symbol">(</a><a id="597" href="https://agda.github.io/agda-stdlib/Function.html#1058" class="Function">id</a><a id="599" class="Symbol">;</a> <a id="601" href="https://agda.github.io/agda-stdlib/Function.html#759" class="Function Operator">_∘_</a><a id="604" class="Symbol">)</a>
<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="635" class="Keyword">using</a> <a id="641" class="Symbol">(</a><a id="642" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="644" class="Symbol">)</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="https://agda.github.io/agda-stdlib/Data.Empty.html" class="Module">Data.Empty</a> <a id="669" class="Keyword">using</a> <a id="675" class="Symbol">(</a><a id="676" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a><a id="677" class="Symbol">;</a> <a id="679" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a><a id="685" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1362" class="Keyword">data</a> <a id="_≤_"></a><a id="1367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">_≤_</a> <a id="1371" class="Symbol">:</a> <a id="1373" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1375" class="Symbol">→</a> <a id="1377" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1379" class="Symbol">→</a> <a id="1381" class="PrimitiveType">Set</a> <a id="1385" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a> <a id="1398" class="Symbol">:</a> <a id="1400" class="Symbol">∀</a> <a id="1402" class="Symbol">{</a><a id="1403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1403" class="Bound">n</a> <a id="1405" class="Symbol">:</a> <a id="1407" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1408" class="Symbol">}</a>
      <a id="1416" class="Comment">--------</a>
    <a id="1429" class="Symbol">→</a> <a id="1431" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="1438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1403" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="1447" class="Symbol">:</a> <a id="1449" class="Symbol">∀</a> <a id="1451" class="Symbol">{</a><a id="1452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1452" class="Bound">m</a> <a id="1454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1454" class="Bound">n</a> <a id="1456" class="Symbol">:</a> <a id="1458" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1459" class="Symbol">}</a>
    <a id="1465" class="Symbol">→</a> <a id="1467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1452" class="Bound">m</a> <a id="1469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="1471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1454" class="Bound">n</a>
      <a id="1479" class="Comment">-------------</a>
    <a id="1497" class="Symbol">→</a> <a id="1499" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1452" class="Bound">m</a> <a id="1505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="1507" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1454" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}<a id="2788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2788" class="Function">_</a> <a id="2790" class="Symbol">:</a> <a id="2792" class="Number">2</a> <a id="2794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="2796" class="Number">4</a>
<a id="2798" class="Symbol">_</a> <a id="2800" class="Symbol">=</a> <a id="2802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="2806" class="Symbol">(</a><a id="2807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="2811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a><a id="2814" class="Symbol">)</a>{% endraw %}</pre>


## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}<a id="3807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3807" class="Function">_</a> <a id="3809" class="Symbol">:</a> <a id="3811" class="Number">2</a> <a id="3813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="3815" class="Number">4</a>
<a id="3817" class="Symbol">_</a> <a id="3819" class="Symbol">=</a> <a id="3821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="3825" class="Symbol">{</a><a id="3826" class="Number">1</a><a id="3827" class="Symbol">}</a> <a id="3829" class="Symbol">{</a><a id="3830" class="Number">3</a><a id="3831" class="Symbol">}</a> <a id="3833" class="Symbol">(</a><a id="3834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="3838" class="Symbol">{</a><a id="3839" class="Number">0</a><a id="3840" class="Symbol">}</a> <a id="3842" class="Symbol">{</a><a id="3843" class="Number">2</a><a id="3844" class="Symbol">}</a> <a id="3846" class="Symbol">(</a><a id="3847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a> <a id="3851" class="Symbol">{</a><a id="3852" class="Number">2</a><a id="3853" class="Symbol">}))</a>{% endraw %}</pre>
One may also identify implicit arguments by name.
<pre class="Agda">{% raw %}<a id="3931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3931" class="Function">_</a> <a id="3933" class="Symbol">:</a> <a id="3935" class="Number">2</a> <a id="3937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="3939" class="Number">4</a>
<a id="3941" class="Symbol">_</a> <a id="3943" class="Symbol">=</a> <a id="3945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="3949" class="Symbol">{</a><a id="3950" class="Argument">m</a> <a id="3952" class="Symbol">=</a> <a id="3954" class="Number">1</a><a id="3955" class="Symbol">}</a> <a id="3957" class="Symbol">{</a><a id="3958" class="Argument">n</a> <a id="3960" class="Symbol">=</a> <a id="3962" class="Number">3</a><a id="3963" class="Symbol">}</a> <a id="3965" class="Symbol">(</a><a id="3966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="3970" class="Symbol">{</a><a id="3971" class="Argument">m</a> <a id="3973" class="Symbol">=</a> <a id="3975" class="Number">0</a><a id="3976" class="Symbol">}</a> <a id="3978" class="Symbol">{</a><a id="3979" class="Argument">n</a> <a id="3981" class="Symbol">=</a> <a id="3983" class="Number">2</a><a id="3984" class="Symbol">}</a> <a id="3986" class="Symbol">(</a><a id="3987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a> <a id="3991" class="Symbol">{</a><a id="3992" class="Argument">n</a> <a id="3994" class="Symbol">=</a> <a id="3996" class="Number">2</a><a id="3997" class="Symbol">}))</a>{% endraw %}</pre>
In the latter format, you may only supply some implicit arguments.
<pre class="Agda">{% raw %}<a id="4092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#4092" class="Function">_</a> <a id="4094" class="Symbol">:</a> <a id="4096" class="Number">2</a> <a id="4098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="4100" class="Number">4</a>
<a id="4102" class="Symbol">_</a> <a id="4104" class="Symbol">=</a> <a id="4106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="4110" class="Symbol">{</a><a id="4111" class="Argument">n</a> <a id="4113" class="Symbol">=</a> <a id="4115" class="Number">3</a><a id="4116" class="Symbol">}</a> <a id="4118" class="Symbol">(</a><a id="4119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="4123" class="Symbol">{</a><a id="4124" class="Argument">n</a> <a id="4126" class="Symbol">=</a> <a id="4128" class="Number">2</a><a id="4129" class="Symbol">}</a> <a id="4131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a><a id="4134" class="Symbol">)</a>{% endraw %}</pre>
It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}<a id="4295" class="Keyword">infix</a> <a id="4301" class="Number">4</a> <a id="4303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md %}).


## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_ For all `n`, the relation `n ≤ n` holds.
* _Transitive_ For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_ For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_ For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_ Any relation that is reflexive and transitive.
* _Partial order_ Any preorder that is also anti-symmetric.
* _Total order_ Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
a partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflection.
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="6731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6731" class="Function">≤-refl</a> <a id="6738" class="Symbol">:</a> <a id="6740" class="Symbol">∀</a> <a id="6742" class="Symbol">{</a><a id="6743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6743" class="Bound">n</a> <a id="6745" class="Symbol">:</a> <a id="6747" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6748" class="Symbol">}</a>
    <a id="6754" class="Comment">-----</a>
  <a id="6762" class="Symbol">→</a> <a id="6764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6743" class="Bound">n</a> <a id="6766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="6768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6743" class="Bound">n</a>
<a id="6770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6731" class="Function">≤-refl</a> <a id="6777" class="Symbol">{</a><a id="6778" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="6782" class="Symbol">}</a>   <a id="6786" class="Symbol">=</a>  <a id="6789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="6793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6731" class="Function">≤-refl</a> <a id="6800" class="Symbol">{</a><a id="6801" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="6805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6805" class="Bound">n</a><a id="6806" class="Symbol">}</a>  <a id="6809" class="Symbol">=</a>  <a id="6812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="6816" class="Symbol">(</a><a id="6817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6731" class="Function">≤-refl</a> <a id="6824" class="Symbol">{</a><a id="6825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6805" class="Bound">n</a><a id="6826" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit.
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="7475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7475" class="Function">≤-trans</a> <a id="7483" class="Symbol">:</a> <a id="7485" class="Symbol">∀</a> <a id="7487" class="Symbol">{</a><a id="7488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7488" class="Bound">m</a> <a id="7490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7490" class="Bound">n</a> <a id="7492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Bound">p</a> <a id="7494" class="Symbol">:</a> <a id="7496" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7497" class="Symbol">}</a>
  <a id="7501" class="Symbol">→</a> <a id="7503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7488" class="Bound">m</a> <a id="7505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="7507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7490" class="Bound">n</a>
  <a id="7511" class="Symbol">→</a> <a id="7513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7490" class="Bound">n</a> <a id="7515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="7517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Bound">p</a>
    <a id="7523" class="Comment">-----</a>
  <a id="7531" class="Symbol">→</a> <a id="7533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7488" class="Bound">m</a> <a id="7535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="7537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Bound">p</a>
<a id="7539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7475" class="Function">≤-trans</a> <a id="7547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>       <a id="7557" class="Symbol">_</a>          <a id="7568" class="Symbol">=</a>  <a id="7571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="7575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7475" class="Function">≤-trans</a> <a id="7583" class="Symbol">(</a><a id="7584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="7588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7588" class="Bound">m≤n</a><a id="7591" class="Symbol">)</a> <a id="7593" class="Symbol">(</a><a id="7594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="7598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7598" class="Bound">n≤p</a><a id="7601" class="Symbol">)</a>  <a id="7604" class="Symbol">=</a>  <a id="7607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="7611" class="Symbol">(</a><a id="7612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7475" class="Function">≤-trans</a> <a id="7620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7588" class="Bound">m≤n</a> <a id="7624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7598" class="Bound">n≤p</a><a id="7627" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="8604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8604" class="Function">≤-trans′</a> <a id="8613" class="Symbol">:</a> <a id="8615" class="Symbol">∀</a> <a id="8617" class="Symbol">(</a><a id="8618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8618" class="Bound">m</a> <a id="8620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8620" class="Bound">n</a> <a id="8622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8622" class="Bound">p</a> <a id="8624" class="Symbol">:</a> <a id="8626" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8627" class="Symbol">)</a>
  <a id="8631" class="Symbol">→</a> <a id="8633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8618" class="Bound">m</a> <a id="8635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="8637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8620" class="Bound">n</a>
  <a id="8641" class="Symbol">→</a> <a id="8643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8620" class="Bound">n</a> <a id="8645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="8647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8622" class="Bound">p</a>
    <a id="8653" class="Comment">-----</a>
  <a id="8661" class="Symbol">→</a> <a id="8663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8618" class="Bound">m</a> <a id="8665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="8667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8622" class="Bound">p</a>
<a id="8669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8604" class="Function">≤-trans′</a> <a id="8678" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="8686" class="Symbol">_</a>       <a id="8694" class="Symbol">_</a>       <a id="8702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>       <a id="8712" class="Symbol">_</a>          <a id="8723" class="Symbol">=</a>  <a id="8726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="8730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8604" class="Function">≤-trans′</a> <a id="8739" class="Symbol">(</a><a id="8740" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8744" class="Bound">m</a><a id="8745" class="Symbol">)</a> <a id="8747" class="Symbol">(</a><a id="8748" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8752" class="Bound">n</a><a id="8753" class="Symbol">)</a> <a id="8755" class="Symbol">(</a><a id="8756" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8760" class="Bound">p</a><a id="8761" class="Symbol">)</a> <a id="8763" class="Symbol">(</a><a id="8764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="8768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8768" class="Bound">m≤n</a><a id="8771" class="Symbol">)</a> <a id="8773" class="Symbol">(</a><a id="8774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="8778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8778" class="Bound">n≤p</a><a id="8781" class="Symbol">)</a>  <a id="8784" class="Symbol">=</a>  <a id="8787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="8791" class="Symbol">(</a><a id="8792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8604" class="Function">≤-trans′</a> <a id="8801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8744" class="Bound">m</a> <a id="8803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8752" class="Bound">n</a> <a id="8805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8760" class="Bound">p</a> <a id="8807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8768" class="Bound">m≤n</a> <a id="8811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8778" class="Bound">n≤p</a><a id="8814" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on 
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds.
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="9576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9576" class="Function">≤-antisym</a> <a id="9586" class="Symbol">:</a> <a id="9588" class="Symbol">∀</a> <a id="9590" class="Symbol">{</a><a id="9591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9591" class="Bound">m</a> <a id="9593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Bound">n</a> <a id="9595" class="Symbol">:</a> <a id="9597" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9598" class="Symbol">}</a>
  <a id="9602" class="Symbol">→</a> <a id="9604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9591" class="Bound">m</a> <a id="9606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="9608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Bound">n</a>
  <a id="9612" class="Symbol">→</a> <a id="9614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Bound">n</a> <a id="9616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="9618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9591" class="Bound">m</a>
    <a id="9624" class="Comment">-----</a>
  <a id="9632" class="Symbol">→</a> <a id="9634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9591" class="Bound">m</a> <a id="9636" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Bound">n</a>
<a id="9640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9576" class="Function">≤-antisym</a> <a id="9650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>       <a id="9660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>        <a id="9671" class="Symbol">=</a>  <a id="9674" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="9679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9576" class="Function">≤-antisym</a> <a id="9689" class="Symbol">(</a><a id="9690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="9694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Bound">m≤n</a><a id="9697" class="Symbol">)</a> <a id="9699" class="Symbol">(</a><a id="9700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="9704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9704" class="Bound">n≤m</a><a id="9707" class="Symbol">)</a>  <a id="9710" class="Symbol">=</a>  <a id="9713" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="9718" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9722" class="Symbol">(</a><a id="9723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9576" class="Function">≤-antisym</a> <a id="9733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Bound">m≤n</a> <a id="9737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9704" class="Bound">n≤m</a><a id="9740" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
<pre class="Agda">{% raw %}<a id="10774" class="Keyword">data</a> <a id="Total"></a><a id="10779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="10785" class="Symbol">(</a><a id="10786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10786" class="Bound">m</a> <a id="10788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10788" class="Bound">n</a> <a id="10790" class="Symbol">:</a> <a id="10792" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10793" class="Symbol">)</a> <a id="10795" class="Symbol">:</a> <a id="10797" class="PrimitiveType">Set</a> <a id="10801" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="10810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="10818" class="Symbol">:</a>
      <a id="10826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10786" class="Bound">m</a> <a id="10828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="10830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10788" class="Bound">n</a>
      <a id="10838" class="Comment">---------</a>
    <a id="10852" class="Symbol">→</a> <a id="10854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="10860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10786" class="Bound">m</a> <a id="10862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10788" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="10867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="10875" class="Symbol">:</a>
      <a id="10883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10788" class="Bound">n</a> <a id="10885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="10887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10786" class="Bound">m</a>
      <a id="10895" class="Comment">---------</a>
    <a id="10909" class="Symbol">→</a> <a id="10911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="10917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10786" class="Bound">m</a> <a id="10919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10788" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
<pre class="Agda">{% raw %}<a id="11238" class="Keyword">data</a> <a id="Total′"></a><a id="11243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11243" class="Datatype">Total′</a> <a id="11250" class="Symbol">:</a> <a id="11252" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11254" class="Symbol">→</a> <a id="11256" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11258" class="Symbol">→</a> <a id="11260" class="PrimitiveType">Set</a> <a id="11264" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="11273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11273" class="InductiveConstructor">forward′</a> <a id="11282" class="Symbol">:</a> <a id="11284" class="Symbol">∀</a> <a id="11286" class="Symbol">{</a><a id="11287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11287" class="Bound">m</a> <a id="11289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11289" class="Bound">n</a> <a id="11291" class="Symbol">:</a> <a id="11293" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11294" class="Symbol">}</a>
    <a id="11300" class="Symbol">→</a> <a id="11302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11287" class="Bound">m</a> <a id="11304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="11306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11289" class="Bound">n</a>
      <a id="11314" class="Comment">----------</a>
    <a id="11329" class="Symbol">→</a> <a id="11331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11243" class="Datatype">Total′</a> <a id="11338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11287" class="Bound">m</a> <a id="11340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11289" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="11345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11345" class="InductiveConstructor">flipped′</a> <a id="11354" class="Symbol">:</a> <a id="11356" class="Symbol">∀</a> <a id="11358" class="Symbol">{</a><a id="11359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11359" class="Bound">m</a> <a id="11361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11361" class="Bound">n</a> <a id="11363" class="Symbol">:</a> <a id="11365" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11366" class="Symbol">}</a>
    <a id="11372" class="Symbol">→</a> <a id="11374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11361" class="Bound">n</a> <a id="11376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="11378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11359" class="Bound">m</a>
      <a id="11386" class="Comment">----------</a>
    <a id="11401" class="Symbol">→</a> <a id="11403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11243" class="Datatype">Total′</a> <a id="11410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11359" class="Bound">m</a> <a id="11412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11361" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occcasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="11948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11948" class="Function">≤-total</a> <a id="11956" class="Symbol">:</a> <a id="11958" class="Symbol">∀</a> <a id="11960" class="Symbol">(</a><a id="11961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11961" class="Bound">m</a> <a id="11963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11963" class="Bound">n</a> <a id="11965" class="Symbol">:</a> <a id="11967" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11968" class="Symbol">)</a> <a id="11970" class="Symbol">→</a> <a id="11972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="11978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11961" class="Bound">m</a> <a id="11980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11963" class="Bound">n</a>
<a id="11982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11948" class="Function">≤-total</a> <a id="11990" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="11998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11998" class="Bound">n</a>                         <a id="12024" class="Symbol">=</a>  <a id="12027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="12035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="12039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11948" class="Function">≤-total</a> <a id="12047" class="Symbol">(</a><a id="12048" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12052" class="Bound">m</a><a id="12053" class="Symbol">)</a> <a id="12055" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="12081" class="Symbol">=</a>  <a id="12084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="12092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="12096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11948" class="Function">≤-total</a> <a id="12104" class="Symbol">(</a><a id="12105" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12109" class="Bound">m</a><a id="12110" class="Symbol">)</a> <a id="12112" class="Symbol">(</a><a id="12113" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12117" class="Bound">n</a><a id="12118" class="Symbol">)</a> <a id="12120" class="Keyword">with</a> <a id="12125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11948" class="Function">≤-total</a> <a id="12133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12109" class="Bound">m</a> <a id="12135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12117" class="Bound">n</a>
<a id="12137" class="Symbol">...</a>                        <a id="12164" class="Symbol">|</a> <a id="12166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="12174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12174" class="Bound">m≤n</a>  <a id="12179" class="Symbol">=</a>  <a id="12182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="12190" class="Symbol">(</a><a id="12191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="12195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12174" class="Bound">m≤n</a><a id="12198" class="Symbol">)</a>
<a id="12200" class="Symbol">...</a>                        <a id="12227" class="Symbol">|</a> <a id="12229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="12237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12237" class="Bound">n≤m</a>  <a id="12242" class="Symbol">=</a>  <a id="12245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="12253" class="Symbol">(</a><a id="12254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="12258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12237" class="Bound">n≤m</a><a id="12261" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="13769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13769" class="Function">≤-total′</a> <a id="13778" class="Symbol">:</a> <a id="13780" class="Symbol">∀</a> <a id="13782" class="Symbol">(</a><a id="13783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13783" class="Bound">m</a> <a id="13785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13785" class="Bound">n</a> <a id="13787" class="Symbol">:</a> <a id="13789" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13790" class="Symbol">)</a> <a id="13792" class="Symbol">→</a> <a id="13794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="13800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13783" class="Bound">m</a> <a id="13802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13785" class="Bound">n</a>
<a id="13804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13769" class="Function">≤-total′</a> <a id="13813" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13821" class="Bound">n</a>        <a id="13830" class="Symbol">=</a>  <a id="13833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="13841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="13845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13769" class="Function">≤-total′</a> <a id="13854" class="Symbol">(</a><a id="13855" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13859" class="Bound">m</a><a id="13860" class="Symbol">)</a> <a id="13862" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="13871" class="Symbol">=</a>  <a id="13874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="13882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="13886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13769" class="Function">≤-total′</a> <a id="13895" class="Symbol">(</a><a id="13896" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13900" class="Bound">m</a><a id="13901" class="Symbol">)</a> <a id="13903" class="Symbol">(</a><a id="13904" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13908" class="Bound">n</a><a id="13909" class="Symbol">)</a>  <a id="13912" class="Symbol">=</a>  <a id="13915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13947" class="Function">helper</a> <a id="13922" class="Symbol">(</a><a id="13923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13769" class="Function">≤-total′</a> <a id="13932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13900" class="Bound">m</a> <a id="13934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13908" class="Bound">n</a><a id="13935" class="Symbol">)</a>
  <a id="13939" class="Keyword">where</a>
  <a id="13947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13947" class="Function">helper</a> <a id="13954" class="Symbol">:</a> <a id="13956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="13962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13900" class="Bound">m</a> <a id="13964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13908" class="Bound">n</a> <a id="13966" class="Symbol">→</a> <a id="13968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="13974" class="Symbol">(</a><a id="13975" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13900" class="Bound">m</a><a id="13980" class="Symbol">)</a> <a id="13982" class="Symbol">(</a><a id="13983" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13908" class="Bound">n</a><a id="13988" class="Symbol">)</a>
  <a id="13992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13947" class="Function">helper</a> <a id="13999" class="Symbol">(</a><a id="14000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="14008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14008" class="Bound">m≤n</a><a id="14011" class="Symbol">)</a>  <a id="14014" class="Symbol">=</a>  <a id="14017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="14025" class="Symbol">(</a><a id="14026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="14030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14008" class="Bound">m≤n</a><a id="14033" class="Symbol">)</a>
  <a id="14037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13947" class="Function">helper</a> <a id="14044" class="Symbol">(</a><a id="14045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="14053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14053" class="Bound">n≤m</a><a id="14056" class="Symbol">)</a>  <a id="14059" class="Symbol">=</a>  <a id="14062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="14070" class="Symbol">(</a><a id="14071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="14075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14053" class="Bound">n≤m</a><a id="14078" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="14716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14716" class="Function">≤-total″</a> <a id="14725" class="Symbol">:</a> <a id="14727" class="Symbol">∀</a> <a id="14729" class="Symbol">(</a><a id="14730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14730" class="Bound">m</a> <a id="14732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14732" class="Bound">n</a> <a id="14734" class="Symbol">:</a> <a id="14736" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14737" class="Symbol">)</a> <a id="14739" class="Symbol">→</a> <a id="14741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10779" class="Datatype">Total</a> <a id="14747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14730" class="Bound">m</a> <a id="14749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14732" class="Bound">n</a>
<a id="14751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14716" class="Function">≤-total″</a> <a id="14760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14760" class="Bound">m</a>       <a id="14768" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="14794" class="Symbol">=</a>  <a id="14797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="14805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="14809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14716" class="Function">≤-total″</a> <a id="14818" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14826" class="Symbol">(</a><a id="14827" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14831" class="Bound">n</a><a id="14832" class="Symbol">)</a>                   <a id="14852" class="Symbol">=</a>  <a id="14855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="14863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1394" class="InductiveConstructor">z≤n</a>
<a id="14867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14716" class="Function">≤-total″</a> <a id="14876" class="Symbol">(</a><a id="14877" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14881" class="Bound">m</a><a id="14882" class="Symbol">)</a> <a id="14884" class="Symbol">(</a><a id="14885" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14889" class="Bound">n</a><a id="14890" class="Symbol">)</a> <a id="14892" class="Keyword">with</a> <a id="14897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14716" class="Function">≤-total″</a> <a id="14906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14881" class="Bound">m</a> <a id="14908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14889" class="Bound">n</a>
<a id="14910" class="Symbol">...</a>                        <a id="14937" class="Symbol">|</a> <a id="14939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="14947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14947" class="Bound">m≤n</a>   <a id="14953" class="Symbol">=</a>  <a id="14956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10810" class="InductiveConstructor">forward</a> <a id="14964" class="Symbol">(</a><a id="14965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="14969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14947" class="Bound">m≤n</a><a id="14972" class="Symbol">)</a>
<a id="14974" class="Symbol">...</a>                        <a id="15001" class="Symbol">|</a> <a id="15003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="15011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15011" class="Bound">n≤m</a>   <a id="15017" class="Symbol">=</a>  <a id="15020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10867" class="InductiveConstructor">flipped</a> <a id="15028" class="Symbol">(</a><a id="15029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="15033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15011" class="Bound">n≤m</a><a id="15036" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="15640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Function">+-monoʳ-≤</a> <a id="15650" class="Symbol">:</a> <a id="15652" class="Symbol">∀</a> <a id="15654" class="Symbol">(</a><a id="15655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15655" class="Bound">m</a> <a id="15657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15657" class="Bound">p</a> <a id="15659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15659" class="Bound">q</a> <a id="15661" class="Symbol">:</a> <a id="15663" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15664" class="Symbol">)</a>
  <a id="15668" class="Symbol">→</a> <a id="15670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15657" class="Bound">p</a> <a id="15672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="15674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15659" class="Bound">q</a>
    <a id="15680" class="Comment">-------------</a>
  <a id="15696" class="Symbol">→</a> <a id="15698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15655" class="Bound">m</a> <a id="15700" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15657" class="Bound">p</a> <a id="15704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="15706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15655" class="Bound">m</a> <a id="15708" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15659" class="Bound">q</a>
<a id="15712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Function">+-monoʳ-≤</a> <a id="15722" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15730" class="Bound">p</a> <a id="15732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15732" class="Bound">q</a> <a id="15734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15734" class="Bound">p≤q</a>  <a id="15739" class="Symbol">=</a>  <a id="15742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15734" class="Bound">p≤q</a>
<a id="15746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Function">+-monoʳ-≤</a> <a id="15756" class="Symbol">(</a><a id="15757" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15761" class="Bound">m</a><a id="15762" class="Symbol">)</a> <a id="15764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15764" class="Bound">p</a> <a id="15766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15766" class="Bound">q</a> <a id="15768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15768" class="Bound">p≤q</a>  <a id="15773" class="Symbol">=</a>  <a id="15776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1443" class="InductiveConstructor">s≤s</a> <a id="15780" class="Symbol">(</a><a id="15781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Function">+-monoʳ-≤</a> <a id="15791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15761" class="Bound">m</a> <a id="15793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15764" class="Bound">p</a> <a id="15795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15766" class="Bound">q</a> <a id="15797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15768" class="Bound">p≤q</a><a id="15800" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="16456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16456" class="Function">+-monoˡ-≤</a> <a id="16466" class="Symbol">:</a> <a id="16468" class="Symbol">∀</a> <a id="16470" class="Symbol">(</a><a id="16471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16471" class="Bound">m</a> <a id="16473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16473" class="Bound">n</a> <a id="16475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16475" class="Bound">p</a> <a id="16477" class="Symbol">:</a> <a id="16479" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16480" class="Symbol">)</a>
  <a id="16484" class="Symbol">→</a> <a id="16486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16471" class="Bound">m</a> <a id="16488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="16490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16473" class="Bound">n</a>
    <a id="16496" class="Comment">-------------</a>
  <a id="16512" class="Symbol">→</a> <a id="16514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16471" class="Bound">m</a> <a id="16516" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16475" class="Bound">p</a> <a id="16520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="16522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16473" class="Bound">n</a> <a id="16524" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16475" class="Bound">p</a>
<a id="16528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16456" class="Function">+-monoˡ-≤</a> <a id="16538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16538" class="Bound">m</a> <a id="16540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16540" class="Bound">n</a> <a id="16542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16542" class="Bound">p</a> <a id="16544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16544" class="Bound">m≤n</a>  <a id="16549" class="Keyword">rewrite</a> <a id="16557" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="16564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16538" class="Bound">m</a> <a id="16566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16542" class="Bound">p</a> <a id="16568" class="Symbol">|</a> <a id="16570" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="16577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16540" class="Bound">n</a> <a id="16579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16542" class="Bound">p</a>  <a id="16582" class="Symbol">=</a> <a id="16584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Function">+-monoʳ-≤</a> <a id="16594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16542" class="Bound">p</a> <a id="16596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16538" class="Bound">m</a> <a id="16598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16540" class="Bound">n</a> <a id="16600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16544" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="16814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16814" class="Function">+-mono-≤</a> <a id="16823" class="Symbol">:</a> <a id="16825" class="Symbol">∀</a> <a id="16827" class="Symbol">(</a><a id="16828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16828" class="Bound">m</a> <a id="16830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16830" class="Bound">n</a> <a id="16832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16832" class="Bound">p</a> <a id="16834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16834" class="Bound">q</a> <a id="16836" class="Symbol">:</a> <a id="16838" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16839" class="Symbol">)</a>
  <a id="16843" class="Symbol">→</a> <a id="16845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16828" class="Bound">m</a> <a id="16847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="16849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16830" class="Bound">n</a>
  <a id="16853" class="Symbol">→</a> <a id="16855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16832" class="Bound">p</a> <a id="16857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="16859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16834" class="Bound">q</a>
    <a id="16865" class="Comment">-------------</a>
  <a id="16881" class="Symbol">→</a> <a id="16883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16828" class="Bound">m</a> <a id="16885" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16832" class="Bound">p</a> <a id="16889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1367" class="Datatype Operator">≤</a> <a id="16891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16830" class="Bound">n</a> <a id="16893" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16834" class="Bound">q</a>
<a id="16897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16814" class="Function">+-mono-≤</a> <a id="16906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16906" class="Bound">m</a> <a id="16908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16908" class="Bound">n</a> <a id="16910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16910" class="Bound">p</a> <a id="16912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16912" class="Bound">q</a> <a id="16914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16914" class="Bound">m≤n</a> <a id="16918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16918" class="Bound">p≤q</a>  <a id="16923" class="Symbol">=</a>  <a id="16926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7475" class="Function">≤-trans</a> <a id="16934" class="Symbol">(</a><a id="16935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16456" class="Function">+-monoˡ-≤</a> <a id="16945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16906" class="Bound">m</a> <a id="16947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16908" class="Bound">n</a> <a id="16949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16910" class="Bound">p</a> <a id="16951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16914" class="Bound">m≤n</a><a id="16954" class="Symbol">)</a> <a id="16956" class="Symbol">(</a><a id="16957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15640" class="Function">+-monoʳ-≤</a> <a id="16967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16908" class="Bound">n</a> <a id="16969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16910" class="Bound">p</a> <a id="16971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16912" class="Bound">q</a> <a id="16973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16918" class="Bound">p≤q</a><a id="16976" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality.
<pre class="Agda">{% raw %}<a id="17402" class="Keyword">infix</a> <a id="17408" class="Number">4</a> <a id="17410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17420" class="Datatype Operator">_&lt;_</a>

<a id="17415" class="Keyword">data</a> <a id="_&lt;_"></a><a id="17420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17420" class="Datatype Operator">_&lt;_</a> <a id="17424" class="Symbol">:</a> <a id="17426" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17428" class="Symbol">→</a> <a id="17430" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17432" class="Symbol">→</a> <a id="17434" class="PrimitiveType">Set</a> <a id="17438" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="17447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17447" class="InductiveConstructor">z&lt;s</a> <a id="17451" class="Symbol">:</a> <a id="17453" class="Symbol">∀</a> <a id="17455" class="Symbol">{</a><a id="17456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17456" class="Bound">n</a> <a id="17458" class="Symbol">:</a> <a id="17460" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17461" class="Symbol">}</a>
      <a id="17469" class="Comment">------------</a>
    <a id="17486" class="Symbol">→</a> <a id="17488" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17420" class="Datatype Operator">&lt;</a> <a id="17495" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17456" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="17504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17504" class="InductiveConstructor">s&lt;s</a> <a id="17508" class="Symbol">:</a> <a id="17510" class="Symbol">∀</a> <a id="17512" class="Symbol">{</a><a id="17513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17513" class="Bound">m</a> <a id="17515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17515" class="Bound">n</a> <a id="17517" class="Symbol">:</a> <a id="17519" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17520" class="Symbol">}</a>
    <a id="17526" class="Symbol">→</a> <a id="17528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17513" class="Bound">m</a> <a id="17530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17420" class="Datatype Operator">&lt;</a> <a id="17532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17515" class="Bound">n</a>
      <a id="17540" class="Comment">-------------</a>
    <a id="17558" class="Symbol">→</a> <a id="17560" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17513" class="Bound">m</a> <a id="17566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17420" class="Datatype Operator">&lt;</a> <a id="17568" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17515" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md %}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` {#less-trans}

Show that strict inequality is transitive.

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}{% link out/plfa/Negation.md %}).)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_.
<pre class="Agda">{% raw %}<a id="19957" class="Keyword">data</a> <a id="even"></a><a id="19962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="19967" class="Symbol">:</a> <a id="19969" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="19971" class="Symbol">→</a> <a id="19973" class="PrimitiveType">Set</a>
<a id="19977" class="Keyword">data</a> <a id="odd"></a><a id="19982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19982" class="Datatype">odd</a>  <a id="19987" class="Symbol">:</a> <a id="19989" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="19991" class="Symbol">→</a> <a id="19993" class="PrimitiveType">Set</a>

<a id="19998" class="Keyword">data</a> <a id="20003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="20008" class="Keyword">where</a>

  <a id="even.zero"></a><a id="20017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20017" class="InductiveConstructor">zero</a> <a id="20022" class="Symbol">:</a>
      <a id="20030" class="Comment">---------</a>
      <a id="20046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="20051" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="20059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20059" class="InductiveConstructor">suc</a>  <a id="20064" class="Symbol">:</a> <a id="20066" class="Symbol">∀</a> <a id="20068" class="Symbol">{</a><a id="20069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20069" class="Bound">n</a> <a id="20071" class="Symbol">:</a> <a id="20073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20074" class="Symbol">}</a>
    <a id="20080" class="Symbol">→</a> <a id="20082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19982" class="Datatype">odd</a> <a id="20086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20069" class="Bound">n</a>
      <a id="20094" class="Comment">------------</a>
    <a id="20111" class="Symbol">→</a> <a id="20113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="20118" class="Symbol">(</a><a id="20119" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20069" class="Bound">n</a><a id="20124" class="Symbol">)</a>

<a id="20127" class="Keyword">data</a> <a id="20132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19982" class="Datatype">odd</a> <a id="20136" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="20145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20145" class="InductiveConstructor">suc</a>   <a id="20151" class="Symbol">:</a> <a id="20153" class="Symbol">∀</a> <a id="20155" class="Symbol">{</a><a id="20156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20156" class="Bound">n</a> <a id="20158" class="Symbol">:</a> <a id="20160" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20161" class="Symbol">}</a>
    <a id="20167" class="Symbol">→</a> <a id="20169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="20174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20156" class="Bound">n</a>
      <a id="20182" class="Comment">-----------</a>
    <a id="20198" class="Symbol">→</a> <a id="20200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19982" class="Datatype">odd</a> <a id="20204" class="Symbol">(</a><a id="20205" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20156" class="Bound">n</a><a id="20210" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : `ℕ → `ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even.
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="21388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21388" class="Function">e+e≡e</a> <a id="21394" class="Symbol">:</a> <a id="21396" class="Symbol">∀</a> <a id="21398" class="Symbol">{</a><a id="21399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21399" class="Bound">m</a> <a id="21401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21401" class="Bound">n</a> <a id="21403" class="Symbol">:</a> <a id="21405" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21406" class="Symbol">}</a>
  <a id="21410" class="Symbol">→</a> <a id="21412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="21417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21399" class="Bound">m</a>
  <a id="21421" class="Symbol">→</a> <a id="21423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="21428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21401" class="Bound">n</a>
    <a id="21434" class="Comment">------------</a>
  <a id="21449" class="Symbol">→</a> <a id="21451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="21456" class="Symbol">(</a><a id="21457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21399" class="Bound">m</a> <a id="21459" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21401" class="Bound">n</a><a id="21462" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="21465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21465" class="Function">o+e≡o</a> <a id="21471" class="Symbol">:</a> <a id="21473" class="Symbol">∀</a> <a id="21475" class="Symbol">{</a><a id="21476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21476" class="Bound">m</a> <a id="21478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21478" class="Bound">n</a> <a id="21480" class="Symbol">:</a> <a id="21482" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21483" class="Symbol">}</a>
  <a id="21487" class="Symbol">→</a> <a id="21489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19982" class="Datatype">odd</a> <a id="21493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21476" class="Bound">m</a>
  <a id="21497" class="Symbol">→</a> <a id="21499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19962" class="Datatype">even</a> <a id="21504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21478" class="Bound">n</a>
    <a id="21510" class="Comment">-----------</a>
  <a id="21524" class="Symbol">→</a> <a id="21526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19982" class="Datatype">odd</a> <a id="21530" class="Symbol">(</a><a id="21531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21476" class="Bound">m</a> <a id="21533" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21478" class="Bound">n</a><a id="21536" class="Symbol">)</a>

<a id="21539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21388" class="Function">e+e≡e</a> <a id="21545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20017" class="InductiveConstructor">zero</a>     <a id="21554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21554" class="Bound">en</a>  <a id="21558" class="Symbol">=</a>  <a id="21561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21554" class="Bound">en</a>
<a id="21564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21388" class="Function">e+e≡e</a> <a id="21570" class="Symbol">(</a><a id="21571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20059" class="InductiveConstructor">suc</a> <a id="21575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21575" class="Bound">om</a><a id="21577" class="Symbol">)</a> <a id="21579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21579" class="Bound">en</a>  <a id="21583" class="Symbol">=</a>  <a id="21586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20059" class="InductiveConstructor">suc</a> <a id="21590" class="Symbol">(</a><a id="21591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21465" class="Function">o+e≡o</a> <a id="21597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21575" class="Bound">om</a> <a id="21600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21579" class="Bound">en</a><a id="21602" class="Symbol">)</a>

<a id="21605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21465" class="Function">o+e≡o</a> <a id="21611" class="Symbol">(</a><a id="21612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20145" class="InductiveConstructor">suc</a> <a id="21616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21616" class="Bound">em</a><a id="21618" class="Symbol">)</a> <a id="21620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21620" class="Bound">en</a>  <a id="21624" class="Symbol">=</a>  <a id="21627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20145" class="InductiveConstructor">suc</a> <a id="21631" class="Symbol">(</a><a id="21632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21388" class="Function">e+e≡e</a> <a id="21638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21616" class="Bound">em</a> <a id="21641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21620" class="Bound">en</a><a id="21643" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md %}#Bin)
defines a datatype of bitstrings representing natural numbers.
<pre class="Agda">{% raw %}<a id="22993" class="Keyword">data</a> <a id="Bin"></a><a id="22998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22998" class="Datatype">Bin</a> <a id="23002" class="Symbol">:</a> <a id="23004" class="PrimitiveType">Set</a> <a id="23008" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="23016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23016" class="InductiveConstructor">nil</a> <a id="23020" class="Symbol">:</a> <a id="23022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22998" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="23028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23028" class="InductiveConstructor Operator">x0_</a> <a id="23032" class="Symbol">:</a> <a id="23034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22998" class="Datatype">Bin</a> <a id="23038" class="Symbol">→</a> <a id="23040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22998" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="23046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23046" class="InductiveConstructor Operator">x1_</a> <a id="23050" class="Symbol">:</a> <a id="23052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22998" class="Datatype">Bin</a> <a id="23056" class="Symbol">→</a> <a id="23058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22998" class="Datatype">Bin</a>{% endraw %}</pre>
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

\end{code}
(Hint: For each of these, you may first need to prove related
properties of `One`.)

## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="24270" class="Keyword">import</a> <a id="24277" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="24286" class="Keyword">using</a> <a id="24292" class="Symbol">(</a><a id="24293" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#802" class="Datatype Operator">_≤_</a><a id="24296" class="Symbol">;</a> <a id="24298" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#833" class="InductiveConstructor">z≤n</a><a id="24301" class="Symbol">;</a> <a id="24303" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#875" class="InductiveConstructor">s≤s</a><a id="24306" class="Symbol">)</a>
<a id="24308" class="Keyword">import</a> <a id="24315" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="24335" class="Keyword">using</a> <a id="24341" class="Symbol">(</a><a id="24342" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1902" class="Function">≤-refl</a><a id="24348" class="Symbol">;</a> <a id="24350" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2095" class="Function">≤-trans</a><a id="24357" class="Symbol">;</a> <a id="24359" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1952" class="Function">≤-antisym</a><a id="24368" class="Symbol">;</a> <a id="24370" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2207" class="Function">≤-total</a><a id="24377" class="Symbol">;</a>
                                  <a id="24413" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#11056" class="Function">+-monoʳ-≤</a><a id="24422" class="Symbol">;</a> <a id="24424" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10966" class="Function">+-monoˡ-≤</a><a id="24433" class="Symbol">;</a> <a id="24435" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10810" class="Function">+-mono-≤</a><a id="24443" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md %})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
