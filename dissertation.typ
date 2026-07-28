// AMS template
#import "custom-ams.typ": ams-article, proof

#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)
#let mythmbox = thmbox.with(
  breakable: true,
)
#let theoremthmbox = mythmbox.with(
  fill: rgb("#ffefff"),
  breakable: false,
)
#let examplethmbox = mythmbox.with(
  fill: rgb("#f3f3ff"),
  breakable: true,
)
#let definitionthmbox = mythmbox.with(
  fill: rgb("#eeffee"),
)
#let notethmbox = mythmbox.with(
  inset: 0pt,
)
#let remarkthmbox = mythmbox.with(
  inset: 0pt,
)
#let theorem = theoremthmbox("common", "Theorem")
#let proposition = theoremthmbox("common", "Proposition")
#let lemma = theoremthmbox("common", "Lemma")
#let corollary = theoremthmbox("common", "Corollary", base: "common")
#let definition = definitionthmbox("common", "Definition")
#let example = examplethmbox("common", "Example")
#let remark = remarkthmbox("common", "Remark")
#let note = notethmbox("common", "Note")
#let proof = thmproof(
  "proof",
  "Proof",
  stroke: (left: 0.2pt + black),
  radius: 0pt,
  inset: (left: 10pt),
)


// Proof trees
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

// Diagrams
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

// Helper functions
#let linkref(target, supplement: none) = {
  link(target, ref(target, supplement: supplement))
}
#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)
#let pair(..args) = {
  sym.chevron.l
  args.pos().join([,#h(0.16em)])
  sym.chevron.r
}

// Formatting
#show selector(link).or(cite): it => {
  set text(navy)
  underline(it)
}
#set text(12pt)
#set par(
  leading: 0.85em,
  spacing: 0.85em,
)
#set page(margin: (
  left: 77pt,
  right: 77pt,
  top: 80pt,
  bottom: 60pt,
))
#show math.equation.where(block: false): box

// Citations
// #let citation-style = "harvard-cite-them-right"
// #let citation-style = "./american-mathematical-society-label.csl"
// #let citation-style = "./american-mathematical-society-numeric.csl"
#let citation-style = "ieee"
#set cite(style: citation-style)

// Template parameters
#show: ams-article.with(
  title: [
    A title],
  authors: (
    (
      name: "Jo MacMahon",
      department: [Department of Mathematics],
      organization: [University of Manchester],
      paper-size: "a4",
      location: [Oxford Rd, Manchester M13 9PL, United Kingdom],
      email: "jo.macmahon@postgrad.manchester.ac.uk",
      // url: "https://personalpages.manchester.ac.uk/postgrad/jo.macmahon",
    ),
  ),
  abstract: [
    An abstract
  ],
  bibliography: bibliography(
    "dissertation.bib",
    style: citation-style,
  ),
)

// #set text(font: "Libertinus Serif")

// Numbering
#show ref: it => {
  let eq = math.equation
  let el = it.element
  if el != none and el.func() == eq and el.numbering != none {
    // Override equation references.
    numbering(
      el.numbering,
      ..counter(eq).at(el.location()),
    )
  } else {
    // Other references as usual.
    it
  }
}

#show: body => {
  for elem in body.children {
    if elem.func() == math.equation and elem.block {
      let numbering = if "label" in elem.fields().keys() { "(1)" } else { none }
      set math.equation(numbering: numbering)
      elem
    } else {
      elem
    }
  }
}

#pagebreak()

// Body

#let sd = $thin . thin$
#let UU = $cal(U)$
#let peq = $equiv$
#let rec = $sans("rec")$
#let ind = $sans("ind")$
#let one = $bold(1)$
#let zero = $bold(0)$
#let ctx = $sans("ctx")$
#let Fin = $"Fin"$
#let inl = $sans("inl")$
#let inr = $sans("inr")$
#let succ = $sans("succ")$
#let pt(label: none, ..args) = {
  if label != none {
    [#math.equation(
        block: true,
        numbering: "(1)",
        ..args,
      )
      #std.label(label)
    ]
  } else {
    math.equation(
      block: true,
      ..args,
    )
  }
  v(0.5em)
}

= Type theory

Type theory is a logical system, encoding *types* and *terms*, which is used as a foundation
of mathematics. Loosely, a type may be considered as an object which contains elements,
similar to a set in set theory. However, type theory is distinct from set theory in that
every object in type theory has a type. In mathematics, we might make statements such as
_"Let $n$ be a natural number. Then $n$ has a successor."_ What is meant by this in a
set-theoretic context is something like "let $n$ denote something", and then "if $n in NN$,
then $n$ has a successor". In type theory this is not allowed: every object we consider must
be constrained by its type. Supposing we have defined a type $NN$ of natural numbers (which
we will do later), we would write $n : NN$ to indicate that $n$ is a natural number. We may
then proceed with the claim about its successor.

== Terms

As type theory is syntactic system, we define the construction of its terms. In our
presentation the basic terms may be _variables_, _primitive constants_ or _defined
constants_. Terms are formed according to the rule

$
  t ::= x | lambda x sd t | t(t') | c | f.
$
TODO: or
$
  t ::= x | lambda (x : t) sd t | t(t') | c | f.
$

Here, $x$ stands for any variable, $t$ is any term, $c$ is any primitive constant and $f$ is
any defined constant.

The distinction between primitive and defined constants is that primitive constants are used
to encode new syntax, and will not be able to be reduced by some definition, while defined
constants are taken to be equivalent to some term (by a judgmental equality, which we will
introduce in the next subsection) and thus able to be eliminated or reduced.

TODO: discuss how to write definitions in open form for defined constants.

The third term-forming rule, $t(t')$, represents function application, and we take the
convention that it associates to the left, i.e. $t_1(t_2)(t_3)$ means $(t_1(t_2))(t_3)$. We
will also write repeated application as $t_1(t_2, t_3)$, for reasons which will become clear
soon.

Note that we do not distinguish between the language of types and the language of terms.
Since we will be presenting a dependent type theory, types may depend on terms and vice
versa, so they are part of the same language.

// == Variables

// The concept of a variable is familiar to logicians. They are denoted by a single lowercase
// letter, usually taken from $x, y, z$, with an optional subscript. To indicate $n$ variables
// we will use $x_1, x_2, ..., x_n$. In type theory, all variables are of a particular type,
// which is written $x : A$.

== Judgments

We introduce three kinds of judgments in our presentation of type theory, namely *context
judgments*, *typing judgments* and *judgmental equalities*.

We will present context judgments in the next subsection, but for now suffice to say they
have the form
$
  Gamma ctx.
$

Typing judgments are of the form
$
  t : A
$
which is to be read as "the term $t$ is of the type $A$". Typing judgments are useful for
demonstrating the existence of a term of a particular type.

The final kind of judgment is the judgmental equality, which takes the form
$
  t peq t' : A.
$
Sometimes the type annotation "$: A$" will be omitted when it is clear from context. This
judgment is a metatheoretic equality, which is to be contrasted with "internal" equality
which we will introduce later. It says that whenever we see the term $t$, we may rewrite it
as $t'$ and vice versa. (TODO: does $t$ need to have no free variables?)

We write deductive rules in the "proof tree" style, where antecedents are written above a
line and consequents below it:
#pt(prooftree(rule($cal(J)_1$, $cal(J)_2$, $cal(J)_3$)))
This deduction says that from the judgments $cal(J)_1$ and $cal(J)_2$ we may conclude
$cal(J)_3$.

== Universes and contexts

In order to avoid a situation similar to Russell's paradox (TODO cite and/or clarify), we
define a hierarchy of *universes*, denoted

$ UU_0 quad UU_1 quad UU_2 quad ... quad UU_i quad ... $

Each $UU_i$ is an element of $UU_(i + 1)$, and furthermore every universe contains all the
types contained in previous universes. I.e. if $x : UU_i$ then $x : UU_j$ for all $j >= i$.
This is known as the *cumulative* property. When we say $A$ is a type, what we mean is that
$A : UU_i$ for some universe $UU_i$. When working with (a finite number of) types in
different universes, the cumulative property guarantees that we can always find a universe
in which all our types are present.

A *context* is a (possibly empty) ordered list of distinct variables and their types, for
example $x_1 : A_1, x_2 : A_2$. Since types are terms, each type may use variables occurring
before it in the list, hence the order being important. Contexts are denoted by an uppercase
Greek letter, usually $Gamma$ or $Delta$. The judgment that $Gamma$ is a well-formed context
is denoted $Gamma ctx$, and the empty context is denoted $dot$.

Contexts appear on the left-hand side of a $tack$ symbol, with a judgment on the right, as
in
$
  Gamma tack cal(J).
$
This is to be read as "in the context $Gamma$, $cal(J)$ holds", and means that the judgment
$cal(J)$ contains variables (TODO and types?) declared in the context $Gamma$.

We have the following rules for universes and contexts.

#pt(rule-set(
  prooftree(rule($dot ctx$)),
  prooftree(rule(
    $x_1 : A_1, ..., x_(n-1) : A_(n-1) tack A_n : UU_i$,
    $(x_1 : A_1, ..., x_n : A_n) ctx$,
  )),
  prooftree(rule($Gamma ctx$, $Gamma tack UU_i : UU_(i+1)$)),
  prooftree(rule($Gamma tack A : UU_i$, $Gamma tack A : UU_(i+1)$)),
))

TODO: note about assuming that types appearing in contexts exist

== Structural rules

TODO: which of these do we need?

== Data for types

For each new type we introduce, we give the following data

- *Formation rules* which specify how to make the type out of existing types.
- *Introduction rules* which specify how to construct terms of the new type.
- *Elimination rules* which specify how to reduce terms of the new type to terms of a
  simpler type.
- *Computation rules* which specify how elimination interacts with construction.
- *Uniqueness principle* (optional) which ???

== Function types

The first type we will introduce is the (non-dependent) *function type*. We introduce a
primitive constant $c_(->)$, and we will write $c_(->)(A, B)$ using the syntactic sugar
$A -> B$.

Conceptually, functions take a value and return a value, so a term of type $A -> B$ takes a
value of type $A$ and returns a value of type $B$. Functions of multiple variables are
represented in *curried* form (after Haskell Curry), meaning that they are of type
$A -> (B -> C)$. That is, they are represented as a function which takes an $A$ and returns
another function of type $B -> C$. We will use the convention that $->$ associates to the
right, so the above type may be written as simply $A -> B -> C$.

Function terms are written using $lambda$ syntax, so $lambda (x : A) sd t$ is conceptually a
function which binds its input to the variable $x$, and returns the term $t$ with its free
occurrences of $x$ replaced with the input.

The data for function types and terms are given by the following rules:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack A -> B : UU_i$,
    name: [$->$-Form],
  )),
  prooftree(rule(
    $Gamma tack B : UU_i$,
    $Gamma, x : A tack t : B$,
    $Gamma tack lambda(x : A) sd t : A -> B$,
    name: [$->$-Intr],
  )),
  prooftree(rule(
    $Gamma tack f : A -> B$,
    $Gamma tack t : A$,
    $Gamma tack f(t) : B$,
    name: [$->$-Elim],
  )),
  prooftree(rule(
    $Gamma tack B : UU_i$,
    $Gamma, x : A tack t : B$,
    $Gamma tack s : A$,
    $Gamma tack (lambda (x : A) sd t)(s) peq t[s slash x] : B$,
    name: [$->$-Comp ($beta$)],
  )),
  prooftree(rule(
    $Gamma tack f : A -> B$,
    $Gamma tack f peq lambda(x : A) sd f(x) : A->B$,
    name: [$->$-Uniq ($eta$)],
  )),
))

The $->$-Comp and $->$-Uniq rules are respectively also known as the $beta$ and $eta$ rules
in $lambda$-calculus.

== Type families

A type family is an element of a function type $A -> UU_i$, i.e. it is a function which
takes some parameter (of type $A$) and returns a type. In this way, we can construct types
which depend on values, which is central to dependent type theory. An example (which we will
return to later) is the type family of finite sets, $Fin : NN -> UU_i$. We have not yet
introduced the type $NN$ of natural numbers, but (we hope) readers will nevertheless be
familiar with the natural numbers and may therefore have some intuition about this type. The
type $Fin(0)$ has 0 elements, the type $Fin(1)$ has exactly 1 element, and so on. We will
precisely define $Fin$ in a later section, after defining the natural numbers.

Another example of a type family is a family $UU_i -> UU_i$, which takes a _type_ as a
parameter. This is familiar to programmers of common non-dependently-typed programming
languages such as Rust or Haskell as a _generic type parameter_. For instance, the type
family defined by
$ lambda (T : UU_i) sd (T -> T) : UU_i -> UU_i $
represents generically the type of an automorphism on $T$.

TODO talk about type families vs just using contexts

== Dependent function types

Now we have introduced function types and type families, we introduce *_dependent_ function
types*. A dependent function is one in which the output type may depend on the input
_value_. The notation for a dependent function type is $product_(x : A) B(x)$, where
$B : A -> UU_i$ is a type family. This represents the type of a function which takes a
parameter $x$ of type $A$ and returns a value of type $B(x)$. Continuing the example of
finite sets from above, we might define a function $sans("max") : product_(n : NN) Fin(n)$
which returns the highest number available in $Fin(n)$; that is, $max(1) peq 0_(Fin(1))$,
$max(2) peq 1_(Fin(2))$ etc., where we use a subscript on the numeral to emphasize that the
elements of each type $Fin(n)$ are distinct.

Using primitive constants to represent syntax, we introduce a primitive constant $c_Pi$, and
write $c_Pi (A, lambda (x : A) sd B(x))$ as $product_(x : A) B(x)$. The rules for dependent
function types correspond closely with their counterparts for non-dependent functions:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : A -> UU_i$,
    $Gamma tack product_(x : A) B(x) : UU_i$,
    name: [$Pi$-Form],
  )),
  prooftree(rule(
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack lambda (x : A) sd b : product_(x : A) B(x)$,
    name: [$Pi$-Intr],
  )),
  prooftree(rule(
    $Gamma tack f : product_(x: A) B(x)$,
    $Gamma tack a : A$,
    $Gamma tack f(a) : B(a)$,
    name: [$Pi$-Elim],
  )),
  prooftree(rule(
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack a : A$,
    $Gamma tack (lambda (x : A) sd b)(a) peq b[a slash x] : B(a)$,
    name: [$Pi$-Comp],
  )),
  prooftree(rule(
    $Gamma tack f : product_(x : A) B(x)$,
    $Gamma tack f peq lambda (x : A) sd f x : product_(x : A) B(x)$,
    name: [$Pi$-Uniq],
  )),
))

== Dependent pair types

We now introduce *pair types*. In its non-dependent variety, a pair type is written
$A times B$ and its elements are pairs $(a, b)$ of elements of $A$ and $B$ respectively.
This should be reasonably familiar to the reader from set theory or computer science. In
fact, we will not take it as an axiom that all elements of $A times B$ are such pairs, but
rather we will prove it using the uniqueness principle for functions. Generalizing this
concept to a dependent form, we may consider pair types where the second type $B$ depends on
the value of the first element of the pair. We write this as
$
  sum_(x : A) B(x)
$
where $A$ is a type and $B$ is a type family of type $A -> UU_i$.

Our formal presentation defines dependent pair types first, and considers non-dependent pair
types as a special case. Again using primitive constants to represent syntax, we introduce
primitive constants $c_Sigma$ and $c_"pair"$, and we write
$c_Sigma (A, lambda (x : A) sd B(x))$ as $sum_(x : A) B(x)$ and $c_"pair" (a, b)$ as
$(a, b)$.

These are the rules for formation and introduction of dependent pair types:
#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : A -> UU_i$,
    $Gamma tack sum_(x : A) B(x) : UU_i$,
    name: [$Sigma$-Form],
  )),
  prooftree(rule(
    $Gamma, x : A tack B(x) : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack b : B(a)$,
    $Gamma tack (a, b) : sum_(x : A) B(x)$,
    name: [$Sigma$-Intr],
  )),
))

For the special case of non-dependent pairs, where $x$ is not free in $B$, we write
$sum_(x: A) B(x)$ as $A times B$.

For the elimination and computation rules, we introduce, for each dependent pair type, a
defined constant $ind_(sum_(x : A) B(x))$ (standing for "inductor"). The point of the
inductor is to convert dependent functions of two variables into functions on dependent
pairs. Our rules say that in order to define a (dependent) function out of a pair type, it
is sufficient to provide a (dependent) function in two variables, which is applied to the
first element of the pair and then the second. For the non-dependent case, this corresponds
to the equivalence between functions $A times B -> C$ and functions $A -> B -> C$.

The action of transforming binary functions into functions on pair types is captured by the
following type of $ind_(sum_(x : A) B(x))$.

$
  ind_(sum_(x: A) B(x)) : product_(C : (sum_(x: A) B(x)) -> UU_i) ((product_(x: A) product_(y:B(x))
      C((x, y))) -> product_(p : sum_(x: A) B(x)) C(p))
$

The formal elimination and computation rules are as follows:
#pt(rule-set(
  prooftree(rule(
    $Gamma tack sum_(x: A) B(x) : UU_i$,
    $Gamma tack C : (sum_(x : A) B(x)) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B) C((x, y))$,
    // $Gamma tack p : sum_(x : A) B(x)$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g) : product_(p : sum_(x : A) B(x)) C(p)$,
    name: [$Sigma$-Elim],
  )),
  prooftree(rule(
    $Gamma tack sum_(x: A) B(x) : UU_i$, // TODO necessary?
    $Gamma tack C : sum_(x : A) B(x) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B(x)) C((x, y))$,
    $Gamma tack a : A$,
    $Gamma tack b : B(a)$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g, (a, b)) peq g(a, b)$,
    name: [$Sigma$-Comp],
  )),
))

== Coproduct types

- Constants $c_+$, $inl$, $inr$
  - $c_+(A, B)$ written as $A + B$
- Analogous to discriminated unions of two elements, aka `Either` in Haskell

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack A + B : UU_i$,
    name: [$+$-Form],
  )),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack inl(a) : A + B$,
    name: [$+$-Intr-L],
  )),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack B : UU_i$,
    $Gamma tack b : B$,
    $Gamma tack inr(b) : A + B$,
    name: [$+$-Intr-R],
  )),
))

Elim and comp:

- Constant $ind_(A+B)$ for each coproduct type

Type of $ind_(A+B)$:
$
  ind_(A+B) : product_(C:A + B -> UU_i) ((product_(x : A) C(inl(x))) -> (product_(x: B) C(inr(x))) -> product_(x : A+B) C(x))
$

Rules:

#pt(
  rule-set(
    prooftree(rule(
      $Gamma tack A + B : UU_i$, // TODO: necessary?
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack ind_(A+B) (C, f, g) : product_(x:A) C(x)$,
      name: [$+$-Elim],
    )),
    prooftree(rule(
      $Gamma tack A + B : UU_i$, // TODO: necessary?
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack a : A$,
      $Gamma tack ind_(A+B) (C, f, g, inl(a)) peq f(a)$,
      name: [$+$-Comp-L],
    )),
    prooftree(rule(
      $Gamma tack A + B : UU_i$, // TODO: necessary?
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack b : B$,
      $Gamma tack ind_(A+B) (C, f, g, inl(b)) peq g(b)$,
      name: [$+$-Comp-R],
    )),
  ),
)

== Booleans, or finite types

=== The singleton type $one$

#pt(
  rule-set(
    prooftree(rule($one : UU_i$, name: [$one$-Form])),
    prooftree(rule($star : one$, name: [$one$-Intr])),
  ),
)

- We need to define $C$ as a type family because we have not yet proved that $one$ only has
  a single element. Similarly the inductor returns a function $product_(a: one) C(a)$.

#pt(rule-set(
  prooftree(rule(
    $Gamma tack C : one -> UU_i$,
    $Gamma tack c : C(star)$,
    $Gamma tack ind_one (C, c) : product_(a : one) C(a)$,
    name: [$one$-Elim],
  )),
  prooftree(rule(
    $Gamma tack C : one -> UU_i$,
    $Gamma tack c : C(*)$,
    $Gamma tack ind_one (C, c, star) peq c$,
    name: [$one$-Comp],
  )),
))

- We can view $one$ as the "unit" for the non-dependent pair type $- times -$.

=== The empty type $zero$

- There is no introduction rule
#pt(
  rule-set(
    prooftree(rule($zero : UU_i$, name: [$zero$-Form])),
  ),
)

- There is no computation rule
#pt(rule-set(
  prooftree(rule(
    $Gamma tack C : zero -> UU_i$,
    $Gamma tack ind_zero (C) : product_(a : zero) C(a)$,
    name: [$one$-Elim],
  )),
))

- We can view $zero$ as the "unit" for the non-dependent coproduct type $- thin + thin -$.

== Natural numbers

#pt(rule-set(
  prooftree(rule($Gamma tack NN : UU_i$, name: [$NN$-Form])),
  prooftree(rule(
    $Gamma tack 0 : NN$,
    name: [$NN$-Intro-0],
  )),
  prooftree(rule(
    $Gamma tack n : NN$,
    $Gamma tack succ(n) : NN$,
    name: [$NN$-Intro-$succ$],
  )),
))

#pt(rule-set(
  prooftree(rule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack ind_NN (C, c_0, c_s) : product_(n : NN) C(n)$,
    name: [$NN$-Elim],
  )),
  prooftree(rule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack ind_NN (C, c_0, c_s, 0) peq c_0$,
    name: [$NN$-Comp-0],
  )),
  prooftree(rule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack n : NN$,
    $Gamma tack ind_NN (C, c_0, c_s, succ(n)) peq c_s (n, ind_NN (C, c_0, c_s, n))$,
    name: [$NN$-Comp-$succ$],
  )),
))

- These computation rules are known as primitive recursion
  - TODO expand on what is _primitive_ recursion
- Remark that although in defining functions out of $NN$, we have to give $c_s$, which is a
  function out of $NN$, we can always define constant functions which throw away $n$ (such
  as iterators like product, sum), which can then form a basis for $c_s$ for more complex
  functions such as factorial.
  - Define all these

// #definition[If $A$ and $B$ are types, there is a *product type* $A times B$. There is also a
//   nullary product type $one$.]

// An element of a product type may be introduced as a *pair* using bracketing notation. If
// $s : A$ and $t : B$ are terms, then $(s, t) : A times B$ is a term.

// We assume that a function out of $A times B$ is completely determined by is action on pairs,
// and a function out of $one$ is completely determined by is action on a (unique?) element
// $star : one$. Using this, we will prove (TODO) that the elements of $A times B$ are
// precisely the pairs, and $one$ has a unique element $star$.


#block[
  #set text(luma(130))
  == ... Fragments ...



  ---

  with the following rules: supposing $A$ and $B$ are types,
  - There is a *function type* $A -> B$.
  - There is a *product type* $A times B$.
  - There is a *coproduct type* $A + B$.


  ---

  - Judgemental equality vs propositional equality: $peq$ vs $=$
  - Function types
    - Definition in closed form or open form

  == Dependent functions

  Functions whose output type depends on the input (type or value). Given a type $A$ and a
  family $B : A -> UU$, write
  $ f : product_(x : A) B(x) $
  to mean a function which takes a parameter $x$ of type $A$ and returns a value of type
  $B(x)$.

  == Product types

  === "Recursor"

  - Generic way to construct functions taking product parameters, using simple functions

  $
    & rec_(A times B) : product_(C: UU) (A -> B -> C) -> A times B -> C \
    & rec_(A times B) (C, g, (a, b)) :peq g(a)(b)
  $

  Projections:
  $
    pi_1 & :peq rec_(A times B)(A, lambda a sd lambda b sd a) \
    pi_2 & :peq rec_(A times B)(B, lambda a sd lambda b sd b)
  $
]
