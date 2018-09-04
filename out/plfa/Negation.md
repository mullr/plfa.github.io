---
src       : src/plfa/Negation.lagda
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
permalink : /Negation/
---

<pre class="Agda">{% raw %}<a id="137" class="Keyword">module</a> <a id="144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}" class="Module">plfa.Negation</a> <a id="158" class="Keyword">where</a>{% endraw %}</pre>

This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

<pre class="Agda">{% raw %}<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="336" class="Keyword">using</a> <a id="342" class="Symbol">(</a><a id="343" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="346" class="Symbol">;</a> <a id="348" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="352" class="Symbol">)</a>
<a id="354" class="Keyword">open</a> <a id="359" class="Keyword">import</a> <a id="366" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="375" class="Keyword">using</a> <a id="381" class="Symbol">(</a><a id="382" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="383" class="Symbol">;</a> <a id="385" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="389" class="Symbol">;</a> <a id="391" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="394" class="Symbol">)</a>
<a id="396" class="Keyword">open</a> <a id="401" class="Keyword">import</a> <a id="408" href="https://agda.github.io/agda-stdlib/Data.Empty.html" class="Module">Data.Empty</a> <a id="419" class="Keyword">using</a> <a id="425" class="Symbol">(</a><a id="426" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a><a id="427" class="Symbol">;</a> <a id="429" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a><a id="435" class="Symbol">)</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="https://agda.github.io/agda-stdlib/Data.Sum.html" class="Module">Data.Sum</a> <a id="458" class="Keyword">using</a> <a id="464" class="Symbol">(</a><a id="465" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">_⊎_</a><a id="468" class="Symbol">;</a> <a id="470" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#470" class="InductiveConstructor">inj₁</a><a id="474" class="Symbol">;</a> <a id="476" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#495" class="InductiveConstructor">inj₂</a><a id="480" class="Symbol">)</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="https://agda.github.io/agda-stdlib/Data.Product.html" class="Module">Data.Product</a> <a id="507" class="Keyword">using</a> <a id="513" class="Symbol">(</a><a id="514" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">_×_</a><a id="517" class="Symbol">;</a> <a id="519" href="https://agda.github.io/agda-stdlib/Data.Product.html#559" class="Field">proj₁</a><a id="524" class="Symbol">;</a> <a id="526" href="https://agda.github.io/agda-stdlib/Data.Product.html#573" class="Field">proj₂</a><a id="531" class="Symbol">)</a> <a id="533" class="Keyword">renaming</a> <a id="542" class="Symbol">(</a><a id="543" href="https://agda.github.io/agda-stdlib/Data.Product.html#543" class="InductiveConstructor Operator">_,_</a> <a id="547" class="Symbol">to</a> <a id="550" href="https://agda.github.io/agda-stdlib/Data.Product.html#543" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="555" class="Symbol">)</a>
<a id="557" class="Keyword">open</a> <a id="562" class="Keyword">import</a> <a id="569" href="https://agda.github.io/agda-stdlib/Function.html" class="Module">Function</a> <a id="578" class="Keyword">using</a> <a id="584" class="Symbol">(</a><a id="585" href="https://agda.github.io/agda-stdlib/Function.html#759" class="Function Operator">_∘_</a><a id="588" class="Symbol">)</a>
<a id="590" class="Keyword">open</a> <a id="595" class="Keyword">import</a> <a id="602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="619" class="Keyword">using</a> <a id="625" class="Symbol">(</a><a id="626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4175" class="Record Operator">_≃_</a><a id="629" class="Symbol">;</a> <a id="631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6873" class="Function">≃-sym</a><a id="636" class="Symbol">;</a> <a id="638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7214" class="Function">≃-trans</a><a id="645" class="Symbol">;</a> <a id="647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9084" class="Record Operator">_≲_</a><a id="650" class="Symbol">)</a>{% endraw %}</pre>


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false.
<pre class="Agda">{% raw %}<a id="¬_"></a><a id="846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬_</a> <a id="849" class="Symbol">:</a> <a id="851" class="PrimitiveType">Set</a> <a id="855" class="Symbol">→</a> <a id="857" class="PrimitiveType">Set</a>
<a id="861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#863" class="Bound">A</a> <a id="865" class="Symbol">=</a> <a id="867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#863" class="Bound">A</a> <a id="869" class="Symbol">→</a> <a id="871" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>{% endraw %}</pre>
This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction.
<pre class="Agda">{% raw %}<a id="¬-elim"></a><a id="1443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1443" class="Function">¬-elim</a> <a id="1450" class="Symbol">:</a> <a id="1452" class="Symbol">∀</a> <a id="1454" class="Symbol">{</a><a id="1455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1455" class="Bound">A</a> <a id="1457" class="Symbol">:</a> <a id="1459" class="PrimitiveType">Set</a><a id="1462" class="Symbol">}</a>
  <a id="1466" class="Symbol">→</a> <a id="1468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="1470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1455" class="Bound">A</a>
  <a id="1474" class="Symbol">→</a> <a id="1476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1455" class="Bound">A</a>
    <a id="1482" class="Comment">---</a>
  <a id="1488" class="Symbol">→</a> <a id="1490" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="1492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1443" class="Function">¬-elim</a> <a id="1499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1499" class="Bound">¬x</a> <a id="1502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1502" class="Bound">x</a> <a id="1504" class="Symbol">=</a> <a id="1506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1499" class="Bound">¬x</a> <a id="1509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1502" class="Bound">x</a>{% endraw %}</pre>
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else.
<pre class="Agda">{% raw %}<a id="1910" class="Keyword">infix</a> <a id="1916" class="Number">3</a> <a id="1918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬_</a>{% endraw %}</pre>
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬-intro"></a><a id="2223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2223" class="Function">¬¬-intro</a> <a id="2232" class="Symbol">:</a> <a id="2234" class="Symbol">∀</a> <a id="2236" class="Symbol">{</a><a id="2237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2237" class="Bound">A</a> <a id="2239" class="Symbol">:</a> <a id="2241" class="PrimitiveType">Set</a><a id="2244" class="Symbol">}</a>
  <a id="2248" class="Symbol">→</a> <a id="2250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2237" class="Bound">A</a>
    <a id="2256" class="Comment">-----</a>
  <a id="2264" class="Symbol">→</a> <a id="2266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2237" class="Bound">A</a>
<a id="2272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2223" class="Function">¬¬-intro</a> <a id="2281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2281" class="Bound">x</a> <a id="2283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2283" class="Bound">¬x</a> <a id="2286" class="Symbol">=</a> <a id="2288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2283" class="Bound">¬x</a> <a id="2291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2281" class="Bound">x</a>{% endraw %}</pre>
Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬¬-elim"></a><a id="2649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2649" class="Function">¬¬¬-elim</a> <a id="2658" class="Symbol">:</a> <a id="2660" class="Symbol">∀</a> <a id="2662" class="Symbol">{</a><a id="2663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2663" class="Bound">A</a> <a id="2665" class="Symbol">:</a> <a id="2667" class="PrimitiveType">Set</a><a id="2670" class="Symbol">}</a>
  <a id="2674" class="Symbol">→</a> <a id="2676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2663" class="Bound">A</a>
    <a id="2688" class="Comment">-------</a>
  <a id="2698" class="Symbol">→</a> <a id="2700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2663" class="Bound">A</a>
<a id="2704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2649" class="Function">¬¬¬-elim</a> <a id="2713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2713" class="Bound">¬¬¬x</a> <a id="2718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2718" class="Bound">x</a> <a id="2720" class="Symbol">=</a> <a id="2722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2713" class="Bound">¬¬¬x</a> <a id="2727" class="Symbol">(</a><a id="2728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2223" class="Function">¬¬-intro</a> <a id="2737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2718" class="Bound">x</a><a id="2738" class="Symbol">)</a>{% endraw %}</pre>
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="contraposition"></a><a id="3216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3216" class="Function">contraposition</a> <a id="3231" class="Symbol">:</a> <a id="3233" class="Symbol">∀</a> <a id="3235" class="Symbol">{</a><a id="3236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3236" class="Bound">A</a> <a id="3238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3238" class="Bound">B</a> <a id="3240" class="Symbol">:</a> <a id="3242" class="PrimitiveType">Set</a><a id="3245" class="Symbol">}</a>
  <a id="3249" class="Symbol">→</a> <a id="3251" class="Symbol">(</a><a id="3252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3236" class="Bound">A</a> <a id="3254" class="Symbol">→</a> <a id="3256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3238" class="Bound">B</a><a id="3257" class="Symbol">)</a>
    <a id="3263" class="Comment">-----------</a>
  <a id="3277" class="Symbol">→</a> <a id="3279" class="Symbol">(</a><a id="3280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="3282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3238" class="Bound">B</a> <a id="3284" class="Symbol">→</a> <a id="3286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="3288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3236" class="Bound">A</a><a id="3289" class="Symbol">)</a>
<a id="3291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3216" class="Function">contraposition</a> <a id="3306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3306" class="Bound">f</a> <a id="3308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3308" class="Bound">¬y</a> <a id="3311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3311" class="Bound">x</a> <a id="3313" class="Symbol">=</a> <a id="3315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3308" class="Bound">¬y</a> <a id="3318" class="Symbol">(</a><a id="3319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3306" class="Bound">f</a> <a id="3321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3311" class="Bound">x</a><a id="3322" class="Symbol">)</a>{% endraw %}</pre>
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.

Using negation, it is straightforward to define inequality.
<pre class="Agda">{% raw %}<a id="_≢_"></a><a id="3754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3754" class="Function Operator">_≢_</a> <a id="3758" class="Symbol">:</a> <a id="3760" class="Symbol">∀</a> <a id="3762" class="Symbol">{</a><a id="3763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3763" class="Bound">A</a> <a id="3765" class="Symbol">:</a> <a id="3767" class="PrimitiveType">Set</a><a id="3770" class="Symbol">}</a> <a id="3772" class="Symbol">→</a> <a id="3774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3763" class="Bound">A</a> <a id="3776" class="Symbol">→</a> <a id="3778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3763" class="Bound">A</a> <a id="3780" class="Symbol">→</a> <a id="3782" class="PrimitiveType">Set</a>
<a id="3786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3786" class="Bound">x</a> <a id="3788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3754" class="Function Operator">≢</a> <a id="3790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3790" class="Bound">y</a>  <a id="3793" class="Symbol">=</a>  <a id="3796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="3798" class="Symbol">(</a><a id="3799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3786" class="Bound">x</a> <a id="3801" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3790" class="Bound">y</a><a id="3804" class="Symbol">)</a>{% endraw %}</pre>
It is trivial to show distinct numbers are not equal.
<pre class="Agda">{% raw %}<a id="3884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3884" class="Function">_</a> <a id="3886" class="Symbol">:</a> <a id="3888" class="Number">1</a> <a id="3890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3754" class="Function Operator">≢</a> <a id="3892" class="Number">2</a>
<a id="3894" class="Symbol">_</a> <a id="3896" class="Symbol">=</a> <a id="3898" class="Symbol">λ()</a>{% endraw %}</pre>
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number.
<pre class="Agda">{% raw %}<a id="peano"></a><a id="4307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4307" class="Function">peano</a> <a id="4313" class="Symbol">:</a> <a id="4315" class="Symbol">∀</a> <a id="4317" class="Symbol">{</a><a id="4318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4318" class="Bound">m</a> <a id="4320" class="Symbol">:</a> <a id="4322" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4323" class="Symbol">}</a> <a id="4325" class="Symbol">→</a> <a id="4327" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="4332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3754" class="Function Operator">≢</a> <a id="4334" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4318" class="Bound">m</a>
<a id="4340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4307" class="Function">peano</a> <a id="4346" class="Symbol">=</a> <a id="4348" class="Symbol">λ()</a>{% endraw %}</pre>
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.
<pre class="Agda">{% raw %}<a id="id"></a><a id="4805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4805" class="Function">id</a> <a id="4808" class="Symbol">:</a> <a id="4810" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a> <a id="4812" class="Symbol">→</a> <a id="4814" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="4816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4805" class="Function">id</a> <a id="4819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4819" class="Bound">x</a> <a id="4821" class="Symbol">=</a> <a id="4823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4819" class="Bound">x</a>{% endraw %}</pre>
It is easy to see there are no possible values of type `A → ⊥`
unless `A` is equivalent to `⊥`.  We have that `⊥ → A`
always holds, by `⊥-elim`, and hence if `A → ⊥` holds then
`A` must be equivalent to `⊥`, in the sense that each implies
the other.



#### Exercise `<-irrerflexive`

Using negation, show that
[strict inequality]({{ site.baseurl }}{% link out/plfa/Relations.md %}/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}{% link out/plfa/Relations.md %}/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one of the three must hold, and each implies the
negation of the other two.


#### Exercise `⊎-dual-×`

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Is there also a term of the following type?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, explain why.


## Intuitive and Classical logic

In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows.
<pre class="Agda">{% raw %}<a id="8341" class="Keyword">postulate</a>
  <a id="em"></a><a id="8353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8353" class="Postulate">em</a> <a id="8356" class="Symbol">:</a> <a id="8358" class="Symbol">∀</a> <a id="8360" class="Symbol">{</a><a id="8361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8361" class="Bound">A</a> <a id="8363" class="Symbol">:</a> <a id="8365" class="PrimitiveType">Set</a><a id="8368" class="Symbol">}</a> <a id="8370" class="Symbol">→</a> <a id="8372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8361" class="Bound">A</a> <a id="8374" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="8376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8361" class="Bound">A</a>{% endraw %}</pre>
As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable).
<pre class="Agda">{% raw %}<a id="em-irrefutable"></a><a id="8638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8638" class="Function">em-irrefutable</a> <a id="8653" class="Symbol">:</a> <a id="8655" class="Symbol">∀</a> <a id="8657" class="Symbol">{</a><a id="8658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8658" class="Bound">A</a> <a id="8660" class="Symbol">:</a> <a id="8662" class="PrimitiveType">Set</a><a id="8665" class="Symbol">}</a> <a id="8667" class="Symbol">→</a> <a id="8669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8673" class="Symbol">(</a><a id="8674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8658" class="Bound">A</a> <a id="8676" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="8678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8658" class="Bound">A</a><a id="8681" class="Symbol">)</a>
<a id="8683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8638" class="Function">em-irrefutable</a> <a id="8698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8698" class="Bound">k</a> <a id="8700" class="Symbol">=</a> <a id="8702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8698" class="Bound">k</a> <a id="8704" class="Symbol">(</a><a id="8705" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#495" class="InductiveConstructor">inj₂</a> <a id="8710" class="Symbol">λ{</a> <a id="8713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8713" class="Bound">x</a> <a id="8715" class="Symbol">→</a> <a id="8717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8698" class="Bound">k</a> <a id="8719" class="Symbol">(</a><a id="8720" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#470" class="InductiveConstructor">inj₁</a> <a id="8725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8713" class="Bound">x</a><a id="8726" class="Symbol">)</a> <a id="8728" class="Symbol">})</a>{% endraw %}</pre>
The best way to explain this code is to develop it interactively.

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that give a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly.

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct.

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly.

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct.

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof.

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)


#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
<pre class="Agda">{% raw %}<a id="Stable"></a><a id="12242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12242" class="Function">Stable</a> <a id="12249" class="Symbol">:</a> <a id="12251" class="PrimitiveType">Set</a> <a id="12255" class="Symbol">→</a> <a id="12257" class="PrimitiveType">Set</a>
<a id="12261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12242" class="Function">Stable</a> <a id="12268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12268" class="Bound">A</a> <a id="12270" class="Symbol">=</a> <a id="12272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="12274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="12276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12268" class="Bound">A</a> <a id="12278" class="Symbol">→</a> <a id="12280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12268" class="Bound">A</a>{% endraw %}</pre>
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="12511" class="Keyword">import</a> <a id="12518" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="12535" class="Keyword">using</a> <a id="12541" class="Symbol">(</a><a id="12542" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="12544" class="Symbol">)</a>
<a id="12546" class="Keyword">import</a> <a id="12553" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="12579" class="Keyword">using</a> <a id="12585" class="Symbol">(</a><a id="12586" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html#688" class="Function">contraposition</a><a id="12600" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ¬  U+00AC  NOT SIGN (\neg)
