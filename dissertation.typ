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
#let refl = $sans("refl")$
#let bigrule = (..args) => {
  let judgments = args.pos()
  let kwargs = args.named()
  rule(
    ..judgments.map(j => block(
      inset: (left: 0em, right: 0em, top: 0em, bottom: 0.27em),
      j,
    )),
    ..kwargs,
  )
}
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

A *type family* is an element of a function type $A -> UU_i$, i.e. it is a function which
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
  prooftree(bigrule(
    $Gamma, x : A tack b : B(x)$,
    $Gamma tack lambda (x : A) sd b : product_(x : A) B(x)$,
    name: [$Pi$-Intr],
  )),
  prooftree(bigrule(
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
  prooftree(bigrule(
    $Gamma tack f : product_(x : A) B(x)$,
    $Gamma tack f peq lambda (x : A) sd f x : product_(x : A) B(x)$,
    name: [$Pi$-Uniq],
  )),
))

=== Functions in "open form" vs "closed form"

When we wish to introduce a constant which will be defined to be equal to some function, our
syntax so far allows us to write expressions such as
$
  f :peq lambda (x : A) sd t.
$
For simple functions such as this one, this form is straightforward, however when
considering functiosn of multiple arguments, the syntax quickly becomes unwieldy. Consider
the definition
$
  g :peq lambda (C : A -> UU_i) sd lambda (x : A) sd lambda (y : C(x)) sd t.
$
If $t$ itself is a complicated expression, one can see how this syntax becomes difficult to
read.

To this end, we will sometimes adopt a definition in "open form", which is presentationally
more similar to the standard mathematical style of function definition. Supposing the term
$t$ has type $B$, we first declare the type of $g$:
$ g : product_(C : A -> UU_i) product_(x : A) C(x) -> B $
and then define it for all arguments
$ g(C, x, y) :peq t. $

We hope the reader agrees that this "open form" is clearer and easier to read.

=== Discarded parameters

Furthermore, we may use the symbol $\_$ as the name of a parameter to indicate that it will
not occur freely in the definition of the function. This is to indicate "constant"
functions, which because of their type must take a parameter, but immediately discard it. A
common usage will be a type family that does not in fact use its parameter and always
returns the same type. For example, when we later work with the type of natural numbers, we
may use the type family
$
  & C : NN -> UU_i \
  & C(\_) :peq A
$
or alternatively in closed form
$
  C :peq lambda (\_: NN) sd A.
$
This indicates a type family $C$ which may theoretically depend on a natural number, but in
fact evaluates to the type $A$ at every number.

This is useful when we wish to apply our induction terms (which are expressed in full
generality using type families and dependent functions) in a way which happens to be
non-dependent.

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
    $Gamma tack B : A -> UU_i$,
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

The name "inductor" in this context is somewhat confusing, since no induction is being
performed. However, it is a concept which will be generalized to the other types we will
introduce, and in the case of the natural numbers its name will be more appropriate. It is
generally useful to have a common pattern for the computation and elimination rules of a
type, and the purpose of the inductor is to represent this pattern. In general, the inductor
provides a way to construct functions out of a type by providing simpler functions.

The action of transforming binary functions into functions on pair types is captured by the
following type of $ind_(sum_(x : A) B(x))$.

$
  ind_(sum_(x: A) B(x)) : product_(C : (sum_(x: A) B(x)) -> UU_i) ((product_(x: A) product_(y:B(x))
      C((x, y))) -> product_(p : sum_(x: A) B(x)) C(p))
$

The formal elimination and computation rules are as follows:
#pt(rule-set(
  prooftree(bigrule(
    $Gamma tack sum_(x: A) B(x) : UU_i$,
    $Gamma tack C : (sum_(x : A) B(x)) -> UU_i$,
    $Gamma tack g : product_(x : A) product_(y : B) C((x, y))$,
    // $Gamma tack p : sum_(x : A) B(x)$,
    $Gamma tack ind_(sum_(x : A) B(x)) (C, g) : product_(p : sum_(x : A) B(x)) C(p)$,
    name: [$Sigma$-Elim],
  )),
  prooftree(bigrule(
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

The next type we introduce is the coproduct. These correspond to disjoint unions from set
theory, or to discriminated unions from computer science. Conceptually, it represents a type
whose elements can be either elements of a type $A$ or elements of a type $B$. In the
functional programming language Haskell, for example, this type is called `Either`.

We introduce three more primitive constants, $c_+$, $inl$ and $inr$. We write $c_+ (A, B)$
as $A + B$. Elements of $A + B$ can be constructed by terms $inl(a)$, where $a : A$, and
$inl(b)$, where $b : B$. These are the formal rules for formation and construction of the
coproduct:

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

In order to define a function out of a coproduct type, we need to provide two functions: one
which operates on elements of type $A$ and one which operates on elements of type $B$, and
then we choose which function to use depending on the "source" type of the particular
element. We use a defined constant $ind_(A+B)$ to perform this construction, using the
pattern of the inductor established previously. This situation is captured by the following
type of $ind_(A+B)$:

$
  ind_(A+B) : product_(C:A + B -> UU_i) ((product_(x : A) C(inl(x))) -> (product_(x: B) C(inr(x))) -> product_(x : A+B) C(x))
$

The following are the elimination and computation rules for the coproduct, using the
inductor:

#pt(
  rule-set(
    prooftree(bigrule(
      $Gamma tack A + B : UU_i$, // TODO: necessary?
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack ind_(A+B) (C, f, g) : product_(x:A) C(x)$,
      name: [$+$-Elim],
    )),
    prooftree(bigrule(
      $Gamma tack A + B : UU_i$, // TODO: necessary?
      $Gamma tack C : A + B -> UU_i$,
      $Gamma tack f : product_(x : A) C(inl(x))$,
      $Gamma tack g : product_(x : B) C(inr(x))$,
      $Gamma tack a : A$,
      $Gamma tack ind_(A+B) (C, f, g, inl(a)) peq f(a)$,
      name: [$+$-Comp-L],
    )),
    prooftree(bigrule(
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

== Finite types

Having given a number of ways of forming types from existing types, we now move on to
defining some "basic" types, which exist without prerequisites. We begin with two types
related to pairs and coproducts.

=== The singleton type $one$

When considering non-dependent pair types, we note that we can recursively construct $n$-ary
tuple types by considering a $times$-chain such as $(A_1 times A_2) times A_3$ and so on.
This gives rise to the question of what we might mean by a "nullary" pair type, i.e. the
type of an empty $times$-chain. The nullary type for pairs is the *singleton type*, denoted
$one$. Unlike in set theory, where the singleton set is defined as a set with exactly one
element, we will define $one$ in our usual way with introduction and computation rules, and
_prove_ that it contains only one element.

In functional programming, this type is often known as the "unit type". In Haskell and Rust,
it is written `()`.

The formation and introduction rules for $one$ are:

#pt(
  rule-set(
    prooftree(rule($one : UU_i$, name: [$one$-Form])),
    prooftree(rule($star : one$, name: [$one$-Intr])),
  ),
)


When defining the elimination and computation rules for $one$, using the inductor, we cannot
assume that $one$ has exactly one element. Indeed, the introduction rule states only that
there is at least one element of type $one$, making no restrictions on the possibility of
other elements. As a consequence of this, the inductor must be generic over a type family
$C : one -> UU_i$, rather than a particular type $C' : UU_i$, even though we know
intuitively that each such family $C$ can only identify one type in $UU_i$.

The type of the inductor is therefore
$
  ind_one : product_(C : one -> UU_i) (C(star) -> product_(a : one) C(a)).
$

The elimination and computation rules for $one$ are as follows:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack C : one -> UU_i$,
    $Gamma tack c : C(star)$,
    $Gamma tack ind_one (C, c) : product_(a : one) C(a)$,
    name: [$one$-Elim],
  )),
  prooftree(rule(
    $Gamma tack C : one -> UU_i$,
    $Gamma tack c : C(star)$,
    $Gamma tack ind_one (C, c, star) peq c$,
    name: [$one$-Comp],
  )),
))

=== The empty type $zero$

Analogously to considering the nullary type of the pair type $times$, we may consider the
nullary type of the coproduct $+$. We call this type the *empty type*, denoted $zero$. Since
we intend this type to have no elements, it has no introduction or computation rules: the
only thing we can say about it is that it is a type (its formation rule) and that functions
out of it can be constructed (its elimination rule). The lack of a computation rule
corresponds to the idea that functions out of it cannot be evaluated, since it is impossible
to construct an element.

In functional programming, this type is often known as the "bottom type". In Haskell it is
written $bot$, and in Rust it is written `!`. It is used as the return type of functions
which diverge (i.e. either do not terminate or crash the program).

#pt(
  rule-set(
    prooftree(rule($zero : UU_i$, name: [$zero$-Form])),
    prooftree(rule(
      $Gamma tack C : zero -> UU_i$,
      $Gamma tack ind_zero (C) : product_(a : zero) C(a)$,
      name: [$one$-Elim],
    )),
  ),
)

== Natural numbers

We are now ready to introduce the type of natural numbers, $NN$. We first declare that there
is a natural number 0, and from there say that every natural number has a successor.

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

The process of defining functions out of the natural numbers is by *primitive recursion*.
That is to say, we provide the value that our desired function takes at 0, and we provide a
"successor" function which computes the value of the function at the successor of a natural
number $n$, given $n$ itself and the value at $n$.

#pt(rule-set(
  prooftree(bigrule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack ind_NN (C, c_0, c_s) : product_(n : NN) C(n)$,
    name: [$NN$-Elim],
  )),
  prooftree(bigrule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack ind_NN (C, c_0, c_s, 0) peq c_0$,
    name: [$NN$-Comp-0],
  )),
  prooftree(bigrule(
    $Gamma tack C : NN -> UU_i$,
    $Gamma tack c_0 : C(0)$,
    $Gamma tack c_s : product_(n : NN) (C(n) -> C(succ(n)))$,
    $Gamma tack n : NN$,
    $Gamma tack ind_NN (C, c_0, c_s, succ(n)) peq c_s (n, ind_NN (C, c_0, c_s, n))$,
    name: [$NN$-Comp-$succ$],
  )),
))

#remark[It may seem counterintuitive that in order to construct functions out of the natural
  numbers, we must provide a successor function $c_s$ which is itself a function out of the
  natural numbers. However, there is no circular logic here, since we may always define
  constant functions which simply throw away their argument. These kinds of successor
  functions, which ignore the first argument (the value of $n$) and consume only the second
  argument (the value of our target function at the predecessor value) are useful for
  defining "accumulator" functions such as sum and product. More complex functions which
  require knowledge of $n$ itself, such as the factorial, may then be constructed out of
  these more basic functions.]

#let add = $sans("add")$
#example(add)[
  $ add : NN -> NN -> NN $
  We introduce a defined constant $add$, and define it using the inductor, where
  - $C(\_) :peq NN$, i.e. $C$ is a constant type family always returning $NN$;
  - $c_0 :peq a$, where $a$ will be the first parameter to $add$; and
  - $c_s (\_, p) :peq succ(p)$, i.e. at every step, $c_s$ returns the successor of the value
    at the previous step.

  These amount to the following definition rule (taking $C$ and $c_s$ in their closed-form
  equivalents):
  #pt(rule-set(prooftree(rule(
    $Gamma tack a : NN$,
    $Gamma tack add(a) peq ind_NN (lambda (\_ : NN) sd NN, a, lambda (\_: NN) sd lambda (p : NN)) sd succ(p))$,
  ))))

  Using the conventional notation of $1$ for $succ(0)$, $2$ for $succ(1)$, etc., let us
  compute the value of $add(1, 1)$. In this computation we will use $C$ and $c_s$ to refer
  to the terms defined above.

  Since we have $0 : NN$, we have $1 : NN$ by rule "$NN$-Intro-$succ$", so the antecedent
  $a : NN$ is satisfied. Then using the definition rule for $add$, we have the following
  judgment for $add(1, 1)$:
  $
    add(1, 1) peq ind_NN (C, 1, c_s, 1).
  $
  Unwrapping the second occurrence of $1$ as $succ(0)$, we then use the rule
  "$NN$-Comp-$succ$". (We omit the verification that our $C$ and $c_s$ terms satisfy the
  necessary antecedents.) We obtain
  $
    add(1, 1) peq c_s (0, ind_NN (C, 1, c_s, 0)).
  $
  We use the rule "$NN$-Comp-0" on the inner $ind_NN$ term to get
  $
    add(1, 1) peq c_s (0, 1),
  $
  i.e.
  $
    add(1, 1) peq (lambda (\_ : NN) sd lambda (p : NN) sd succ(p)) (0, 1).
  $

  Using the rule "$->$-Comp" (the $beta$ rule) twice to perform the function application, we
  get
  $
    add(1, 1) peq succ(1) peq 2.
  $
]<example:add>

#let prod = $sans("prod")$
#example(prod)[
  $ prod : NN -> NN -> NN $
  Similarly to $add$, we introduce a defined constant $prod$ and define it using the
  inductor, where
  - $C(\_) :peq NN$
  - $c_0 :peq 0$
  - $c_s (\_, p) :peq add(a, p)$, where $a$ will be the first parameter to $prod$.

  These amount to the following definition rule:
  #pt(prooftree(rule(
    $Gamma tack a : NN$,
    $prod(a) peq ind_NN (lambda (\_ : NN) sd NN, 0, lambda (\_ : NN) sd lambda (p: NN) sd add(p, a))$,
  )))

  Let us again compute an example product, $prod(3, 2)$, following the convention of
  @example:add.

  We apply the definition rule to obtain
  $
    prod(3, 2) peq ind_NN (C, 0, c_s, 3, 2).
  $

  Then, unwrapping $2$ as $succ(1)$, we apply $NN$-Comp-$succ$ to obtain
  $
    prod(3, 2) peq c_s (1, ind_NN (C, 0, c_s, 1)).
  $

  Using the $beta$-rule to apply $c_s$, we get
  $
    prod(3, 2) peq add(3, ind_NN (C, 0, c_s, 1)).
  $

  By another application of $NN$-Comp-$succ$ and the $beta$-rule on the inner $ind$ term, we
  obtain
  $
    prod(3, 2) peq add(3, add(3, ind_NN (C, 0, c_s, 0))).
  $

  Now, by applying $NN$-Comp-0 to the inner $ind$ term, we obtain
  $
    prod(3, 2) peq add(3, add(3, 0)).
  $

  Finally, by computing the resulting expression using the process in @example:add, we
  arrive at
  $
    prod(3, 2) peq 6.
  $
]<example:prod>

#let fact = $sans("fact")$
#example(fact)[
  Both @example:add and @example:prod used a step function $c_s$ which ignored its first
  parameter, i.e. the recursion counter. We now demonstrate a function, namely the factorial
  function, which uses this value.

  $ fact : NN -> NN $

  We introduce a defined constant $fact$ and define it using the inductor, where
  - $C(n) :peq NN$
  - $c_0 :peq 1$
  - $c_s (s, p) :peq prod(succ(s), p)$

  These amount to the following definition rule:
  #pt(prooftree(rule(
    $fact peq ind_NN (lambda (\_ : NN) sd NN, 1, lambda (s : NN) sd lambda (p : NN) sd prod(s, p))$,
  )))

  For a demonstration, we compute $fact(3)$. We apply the definition rule to obtain
  $
    fact(3) peq ind_NN (C, 1, c_s, 3),
  $
  to which we then apply the $NN$-Comp-$succ$ rule to obtain
  $
    fact(3) peq c_s (2, ind_NN (C, 1, c_s, 2)).
  $
  Repeated applications of the $beta$-rule and $NN$-Comp-$succ$ gets us
  $
    fact(3) & peq prod(3, c_s (1, ind_NN (C, 1, c_s, 1))) \
            & peq prod(3, prod(2, c_s (0, ind_NN (C, 1, c_s, 0)))) \
            & peq prod(3, prod(2, prod(1, ind_NN (C, 1, c_s, 0)))).
  $
  Then, we apply $NN$-Comp-0 to the remaining $ind$ term to get
  $
    fact(3) peq prod(3, prod(2, prod(1, 1)))
  $
  and applying the process in @example:prod we arrive at
  $
    fact(3) peq 6.
  $
]

- TODO expand on what is _primitive_ recursion

== Propositions as types

An interesting property of type theory is that it corresponds with the principles of
(constructive) logic. Indeed, we may translate propositional logic into types as follows:
(TODO make table, cite book explicitly)
- True: $one$
- False: $zero$
- A and B: $A times B$
- A or B: $A + B$
- A implies B: $A -> B$
- Not A: $A -> zero$.

We consider a proposition to be true if its corresponding type has an element, and we call
this element a *witness* to the truth of the proposition. A worked example in (TODO: HOTT
book) gives a proof of one of de Morgan's laws,
$ "if not A and not B, then not (A or B)". $
The type translation of this is
$ (A -> zero) times (B -> zero) -> (A + B) -> zero. $
In order to prove this, we must exhibit an element of this type. Such an element is given as
$
  f((x, y), inl(z)) & :peq x(z) \
  f((x, y), inr(z)) & :peq y(z).
$
In our formal definitions this translates to
$
  C_1 &:peq lambda (\_: (A -> zero) times (B -> zero)) sd zero \
  C_2 &:peq lambda (\_: A + B) sd zero \
  g &:peq ind_(A + B) (C_2, lambda (z : A) sd x(z), lambda (z : B) sd y(z)) \
  f &:peq ind_((A -> zero) times (B -> zero)) (C_1, lambda (x : A -> zero) sd lambda (y : B -> zero) sd g).
$

#example[
  It is left as an exercise in (HOTT book) to show the converse, i.e.
  #align(center)[
    if not ($A$ or $B$) then (not $A$) and (not $B$)
  ]

  That is to say, we want to exhibit an element
  $ t : ((A + B) -> zero) -> ((A -> zero) times (B -> zero)). $

  Let $Gamma tack A : UU_i, b : UU_i, z : (A + B) -> zero$. Then we have

  #pt(prooftree(
    rule(
      rule(
        rule($Gamma, a : A tack inl(a) : A + B$, name: [$+$-Intr-L]),
        $Gamma, a : A tack f(inl(a)) : zero$,
        name: [$->$-Elim],
      ),
      $Gamma tack lambda (a : A) sd f(inl(a)) : A -> zero$,
      name: [$->$-Intr],
    ),
  ))

  By a similar deduction we get
  #pt(prooftree(rule(
    $Gamma tack lambda (b : B) sd f(inr(b)) : B -> zero$,
  )))

  Writing these as a pair, we get
  #pt(prooftree(rule(
    rule(
      $Gamma tack lambda (a : A) sd f(inl(a)) : A -> zero$,
    ),
    rule(
      $Gamma tack lambda (b : B) sd f(inr(b)) : B -> zero$,
    ),
    $Gamma tack (lambda (a : A) sd f(inl(a)), lambda (b : B) sd f (inr(b))) : (A -> zero) times (B -> zero)$,
    name: [$Sigma$-Intr],
  )))

  Then applying $->$-Intr (removing $f$ from the context) we obtain a term
  $
    lambda (f : (A + B) -> zero) sd (lambda (a : A) sd f(inl(a)), lambda (b : B) sd f(inr(b))),
  $
  which has type
  $ ((A + B) -> zero) -> ((A -> zero) times (B -> zero)) $
  as required.
]

We may use the fact that we are working in dependent type theory to move from propositional
to predicate logic by considering a type family $P : A -> UU_i$ as a predicate and
translating
- "for all $x$, $P(x)$" to $product_(x : A) P(x)$, and
- "there exists an $x$ such that $P(x)$" to $sum_(x : A) P(x)$.

#example[The statement
  #block(inset: (left: 2em, right: 2em))[#align(center)[if for all $x : A$, $P(x)$ and
    $Q(x)$, then for all $x : A$, $P(x)$ and for all $x : A$, $Q(x)$]]
  translates to the type
  $
    (product_(x : A) P(x) times Q(x)) -> (product_(x : A) P(x)) times (product_(x : A) Q(x))
  $
  which has an element
  $
    lambda (f : product_(x : A) P(x) times Q(x)) sd (lambda (x : A) sd pi_0(f(x)), lambda (x : A) sd pi_1(f(x))).
  $
]

#let leq = $sans("leq")$
#example[We define inequality on the natural numbers as a function $leq$. For ease of
  notation, we express $leq(n, m)$ and $add(a, b)$ (from @example:add) using infix notation:
  $n <= m$ and $a + b$ respectively.

  We define $leq$ as
  $
    n <= m :peq sum_(p : NN) n + p =_NN m.
  $

  We are jumping the gun here by using the identity type $=_NN$, which will be introduced in
  the next section. For now, it suffices to know that for any type $A$ and element $a : A$,
  there is a type $a =_A a$ and an element $refl_a : a =_A a$.

  Considering the statement $1 <= 2$, we translate this to the dependent pair
  $ sum_(p : NN) 1 + p =_NN 2. $
  To show this is inhabited, consider the element $refl_2 : 2 =_NN 2$. Since we have shown
  that $1 + 1 peq 2$, we may rewrite the 2 on the left hand side of $refl_2$ to get
  $refl_2 : 1 + 1 =_NN 2$. Then applying the rules for dependent pair types, we have

  #pt(prooftree(rule(
    bigrule($Gamma tack lambda (p : NN) sd 1 + p =_NN 2 : NN -> UU_i$),
    bigrule($Gamma tack 1 : NN$),
    bigrule($Gamma tack refl_2 : 1 + 1 =_NN 2$),
    $Gamma tack (1, refl_2) : sum_(p : NN) (1 + p =_NN 2)$,
    name: [$Sigma$-Intr],
  )))

  so the type $1 <= 2$ is inhabited by the pair $(1, refl_2)$.
]


== Identity types

We now arrive at one of the more powerful mechanics of dependent type theory, the concept of
the *identity type*. The identity type is a way of proving an equality _within_ type theory,
as opposed to the judgmental (metatheoretic) equality we have been using up to now. The idea
is that, since types may depend on values, we can construct a type $a =_A b$ for $a$ and $b$
terms of type $A$, and an element of this type is a witness to the equality of $a$ and $b$.

The introduction rule consists of an element $refl_a$ of type $a =_A a$, i.e. it is an axiom
that there is a witness to the equality of $a$ with itself. The formal statements of the
formation and introduction rules are:

#pt(rule-set(
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack b : B$,
    $Gamma tack a =_A b : UU_i$,
    name: [=-Form],
  )),
  prooftree(rule(
    $Gamma tack A : UU_i$,
    $Gamma tack a : A$,
    $Gamma tack refl_a : a =_A a$,
    name: [=-Intr],
  )),
))

The elimination and computation rules represent the *path induction principle*, which is
"one of the most subtle parts of type theory". We will state the formal definitions of the
rules first, and then examine their meaning using examples.

#pt(rule-set(
  prooftree(bigrule(
    $Gamma tack A : UU_i$,
    $Gamma tack C : product_(x : A) product_(y : A) (x =_A y) -> UU_i$,
    $Gamma tack c : product_(z : A) C(z, z, refl_z)$,
    $Gamma tack ind_=_A (C, c) : product_(a : A) product_(b : A) product_(p : a =_A b) C(a, b, p)$,

    name: [=-Elim],
  )),
  prooftree(bigrule(
    $Gamma tack A : UU_i$,
    $Gamma tack C : product_(x : A) product_(y : A) (x =_A y) -> UU_i$,
    $Gamma tack c : product_(z : A) C(z, z, refl_z)$,
    $Gamma tack a : A$,
    $Gamma tack ind_=_A (C, c, a, a, refl_a) peq c(a)$,
    name: [=-Comp],
  )),
))

A useful first point of understanding these rules is to compute a consequence of them, the
*indiscernibility of identicals*. In terms of types and elements, it gives us a way of
"transporting" an element of a type $C(x)$ into an element of a type $C(y)$, as long as
there is a witness to the equality of $x$ and $y$. Translated to the language of type
families as predicates, it means that predicates which are satisfied by some element remain
satisfied by any equal element, i.e. that equal terms may be substituted for each other.

#proposition([Indiscernibility of identicals])[For every type family $D : A -> UU_i$ there
  is a function
  $
    f : product_(x : A) product_(y : A) (x =_A y) -> D(x) -> D(y)
  $
  such that for all $z : A$
  $
    f(z, z, refl_z) peq id_D(z).
  $
]

#proof[
  Fix a type family $D : A -> UU_i$.

  Define $C$, as in the computation and elimination rules, as
  $
    C : product_(x : A) product_(y : A) (x =_A y) -> UU_i \
    C(x, y, \_) :peq D(x) -> D(y).
  $

  Also define $c$ as
  $
    c : product_(z : A) C(z, z, refl_z) \
    c(z, x) :peq x,
  $
  or equivalently (by judgmental equality),
  $
    c : product_(z : A) D(z) -> D(z) \
    c(z) :peq id_D(z).
  $

  Then by using the elimination rule, we obtain a function
  $
    ind_(=_A) (C, c) : product_(x : A) product_(y : A) product_(p : x =_A y) D(x) -> D(y)
  $
  and by using the computation rule (and function application), we have
  $
    ind_(=_A) (C, c, x, x, refl_x) peq id_D(x)
  $
  as required.
]

This principle says that, given $x : A$ and $y : A$, and a witness to their equality, we can
transform any witness to the predicate $D(x)$ into a witness to $D(y)$, and that when we
consider the witness $refl_x$ to the equality $x =_A x$, this transformation is the
identity.

Moving to the general form of the elimination rule, we allow $C$ to depend not only on
$x : A$ and $y : A$ (which must be equal) but also on the specific witness $p$ to their
equality. The rule supposes that we have such a family $C$, and an element of it ($c(z)$)
for all $z : A$, where we plug in the axiomatic reflexive equality of $z$ with itself. We
then get an element of $C(a, b, p)$ for all $a : A$, $b : A$ such that $a$ and $b$ are
equal. In other words, if we want to construct an element of the family $C(a, b, p)$, it is
sufficient to show an element of $C(z, z, refl_z)$. In the language of propositions and
predicates, if $C(z, z, refl_z)$ is true -- i.e. $C$ is a reflexive predicate -- then
$C(a, b, p)$ is true whenever $p$ proves that $a$ and $b$ are equal. Moreover, the general
form of the computation rule gives us a judgmental equality in the case where $a$ and $b$
are judgmentally equal.


== Proofs about our types

Now that we have defined identity types, we can make some statements about identities within
our previously-defined types.

#proposition[Every element of a pair type $A times B$ is equal to $(x, y)$, for some
  $x : A$, $y : B$.]
#proof[Since we did not mention projections from pairs earlier, we define the projections
  $pi_0$ and $pi_1$. First we define multi-parameter functions
  $
    & pi'_0 : A -> B -> A \
    & pi'_0 (x, y) :peq x \
    & pi'_1 : A -> B -> B \
    & pi'_1 (x, y) :peq y
  $
  and then define the projections as
  $
    pi_0 & :peq ind_(A times B) (lambda (\_ : A times B) sd A, pi'_0) \
    pi_1 & :peq ind_(A times B) (lambda (\_ : A times B) sd B, pi'_1)
  $
  so that $pi_0$ and $pi_1$ have types
  $
    pi_0 & : A times B -> A \
    pi_1 & : A times B -> B.
  $
  By some application of the rules for functions and pairs, it is easy to show that
  $pi_0((x, y)) peq x$ and $pi_1((x, y)) peq y$ for all pairs $(x, y) : A times B$.

  Now we define a type family $C$ as
  $
    C : A times B -> UU_i \
    C(z) :peq (pi_0(z), pi_1(z)) =_(A times B) z.
  $
  That is to say, $C(z)$ represents the proposition that $z$ is equal to the pair of its
  projections. Our aim, then, is to show that $C(z)$ is inhabited for all $z : A times B$.

  To construct a function out of a pair type $A times B$, we know by the elimination rule
  that it is sufficient to give a multi-parameter function on $A$ and $B$. So to construct a
  function $f : product_(z : A times B) C(z)$, it is sufficient to show a function
  $g : product_(x : A) product_(y : B) C((x, y))$.

  Since we know that $pi_0((x, y)) peq x$ and $pi_1((x, y)) peq y$, we see that we can
  rewrite the type of $refl_((x, y))$ as
  $ refl_((x, y)) : (pi_0((x, y)), pi_1((x, y))) =_(A times B) (x, y) $
  i.e.
  $
    refl_((x, y)) : C((x, y)).
  $

  Therefore for our function $g : product_(x : A) product_(y : B) C((x, y))$, we put
  $
    g(x, y) :peq refl_((x, y)).
  $
  Applying the inductor, we get
  $
    ind_(A times B) (C, g) : product_(z : A times B) C(z)
  $
  as required.
]


- $one$ has only one element
- Construct finite sets
- TODO Something using equality elim/comp

#block[
  #set text(luma(130))
  == ... Fragments ...
  - Judgemental equality vs propositional equality: $peq$ vs $=$
]

= Homotopy

In this section we will... TODO

We begin with a brief discursive exposition of classical homotopy theory, from the point of
view of a set-theoretic foundation of topological spaces.

In a space $X$, consisting of points equipped with a topology, a *path* from a point $x$ to
a point $y$ is a continuous map $f : [0, 1] -> X$ such that $f(0) = x$ and $f(1) = y$. We
can construct the inverse of a path, such as $f^(-1)$ which walks from $y$ back to $x$, and
also composition of paths: supposing $g : [0, 1] -> X$ is a path such that $g(0) = y$ and
$g(1) = z$, the composition $f bullet g$ is a path which walks from $x$ to $z$ via $y$.
(Note that our definition of the "inverse path" $f^(-1)$ is _not_ the inverse function of
$f$ -- in general such an inverse function need not even exist -- and our definition of path
composition is similarly unrelated to function composition, and notated in the opposite
order.)

Given spaces $X_1$, $X_2$ and two continuous maps $f, g : X_1 -> X_2$, we may consider a
continuous map $H : [0, 1] times X_1 -> X_2$ such that $H(0, -) = f$ and $H(1, -) = g$.
(Note that such a map $H$ does not in general always exist.) Such maps between maps are
called *homotopies*. We may think of a homotopy as continuously deforming the map $f$ into
$g$. If we additionally require that $H(t, 0) = x$ and $H(t, 1) = y$ for all $t in [0, 1]$,
we say that $H$ is *endpoint preserving*.

---

Given two paths $f$ and $g$, we can consider a continuous deformation $phi$ of $f$ to $g$.
The function $phi : [0, 1]^2 -> X$ must be continuous and satisfy $phi(0, -) = f$ and
$phi(1, -) = g$. We may consider $phi$ as a 2-dimensional path, or a path between paths.
Given another continuous deformation from $f$ to $g$, say $psi$, we may further consider
continuous deformations from $phi$ to $psi$, and so on. Such $n$-dimensional paths are known
as *homotopies*. Of course, if the space contains a hole, or some other kind of
discontinuity, such deformations may not be possible.

Homotopies form an equivalence relation on the paths they deform. The proofs of reflexivity
and transitivity are trivial, and the proof of symmetry is trivial in the case of a strictly
monotonic function, and easily generalizable from there. (TODO cite something?)

- Paths and paths between paths
- Structure: composition, inversion
- $infinity$-groupoid
  - associativity up to next level
  - inverses up to next level
  - identity?
