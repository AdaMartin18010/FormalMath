Shuichi Yukita

# Category Theory Using Haskell

An Introduction with Moggi and Yoneda

# Computer Science Foundations and Applied Logic

# Editorial Board

Erika Abraham, Department of Computer Science, RWTH Aachen University, Aachen, Germany

Olaf Beyersdorff, Friedrich Schiller University Jena, Jena, Germany

Jasmin Blanchette, Garching, Germany

Armin Biere, Informatik, ETH Zentrum, RZH, Computer Systems Institute, Zurich, Switzerland

Sam Buss, Department of Mathematics, University of California, San Diego, USA

Matthew England, Engineering and Computing, Coventry University, Coventry, UK

Jacques Fleuriot, The University of Edinburgh, Scotland, UK

Pascal Fontaine, University of Lorraine, Villers Les Nancy Cedex, France

Arie Gurfinkel, Pittsburgh, USA

Marijn Heule, Algorithms, University of Texas, Austin, USA

Reinhard Kahle, Departamento de Matematica, Universidade Nova de Lisboa, Caparica, Portugal

Phokion Kolaitis, University of California, Santa Cruz, USA

Antonina Kolokolova, Department of Computer Science, Memorial University of Newfoundland, St. John's, Canada

RalphMatthes,UniversitatMunchen,Munchen,Germany

Assia Mahboubi, Institut National de Recherche en Informatique et en Automatique, Nantes Cedex 3, France

Jakob Nordstrom, Stockholm, Sweden

Prakash Panangaden, School of Computer Science, McGill University, Montreal, Canada

Kristin Yvonne Rozier, Champaign, USA

Thomas Studer, Institute of Computer Science and Applied Mathematics, University of Berne, Berne, Switzerland

Cesare Tinelli, The University of Iowa, Iowa City, USA

Computer Science Foundations and Applied Logic is a growing series that focuses on the foundations of computing and their interaction with applied logic, including how science overall is driven by this. Thus, applications of computer science to mathematical logic, as well as applications of mathematical logic to computer science, will yield many topics of interest. Among other areas, it will cover combinations of logical reasoning and machine learning as applied to AI, mathematics, physics, as well as other areas of science and engineering. The series (previously known as Progress in Computer Science and Applied Logic, https://www.springer.com/series/4814) welcomes proposals for research monographs, textbooks and polished lectures, and professional text/references. The scientific content will be of strong interest to both computer scientists and logicians.

Shuichi Yukita

# Category Theory Using Haskell

An Introduction with Moggi and Yoneda

Shuichi Yukita

Department of Digital Media, Faculty

of Computer and Information Sciences

Hosei University

Koganei, Japan

ISSN 2731-5754

ISSN 2731-5762 (electronic)

Computer Science Foundations and Applied Logic

ISBN 978-3-031-68537-8

ISBN 978-3-031-68538-5 (eBook)

https://doi.org/10.1007/978-3-031-68538-5

© The Editor(s) (if applicable) and The Author(s), under exclusive license to Springer Nature Switzerland AG 2025

This work is subject to copyright. All rights are solely and exclusively licensed by the Publisher, whether the whole or part of the material is concerned, specifically the rights of translation, reprinting, reuse of illustrations, recitation, broadcasting, reproduction on microfilms or in any other physical way, and transmission or information storage and retrieval, electronic adaptation, computer software, or by similar or dissimilar methodology now known or hereafter developed.

The use of general descriptive names, registered names, trademarks, service marks, etc. in this publication does not imply, even in the absence of a specific statement, that such names are exempt from the relevant protective laws and regulations and therefore free for general use.

The publisher, the authors and the editors are safe to assume that the advice and information in this book are believed to be true and accurate at the date of publication. Neither the publisher nor the authors or the editors give a warranty, expressed or implied, with respect to the material contained herein or for any errors or omissions that may have been made. The publisher remains neutral with regard to jurisdictional claims in published maps and institutional affiliations.

This book is published under the imprint Birkhäuser, www.birkhauser-science.com by the registered company Springer Nature Switzerland AG

The registered company address is: Gewerbestrasse 11, 6330 Cham, Switzerland

If disposing of this product, please recycle the paper.

# Preface

In the first half of this Preface, we will see the outline of this book, for some readers, with unfamiliar technical terms. But just take it easy since the whole details follow soon in the coming chapters in a gentle manner. In the latter half of this Preface, the intended readers will be precisely defined.

Algebraic topology gave birth to category theory in the 1940s. Category theory became a working language in algebraic geometry and number theory in the 1950s. Algebraic analysis of Kyoto school introduced homological techniques systematically in the study of partial differential equations, and further pushed forward their theory to a more advanced level with category theory. Eilenberg and Mac Lane sought for a systematic way of describing the situations where two things are naturally or essentially the same, or something is universal among others. The first choice of textbook on category theory might be Mac Lane's famous book [1] if you are familiar with various notions in undergraduate mathematics such as groups, rings, modules, homomorphisms, tensor products, continuous mappings in general topology, homology groups in algebraic topology, and so on. Do not worry. If you are familiar with Haskell programming, this monograph is for you.

In the nineteenth century, before category theory got formal foundations, Galois had actually established an equivalence of categories between the category of fields and the category of groups, known today as the Galois connections.

Category theory began to spread to logic and computer science soon after it was born. It is also widely used in physics. In the functional programming language Haskell, libraries are defined, designed, or redesigned over revisions, from a category-theoretic point of view. In a computer algebra system Axiom, it is possible to program directly the language of category theory in a way that mathematicians do with pencil and paper. Many other popular programming languages are ready to take in category-theoretic ideas.

Under such circumstances, if you go to a bookstore, you will find many books on category theory, from introductory books to highly technical ones. A quick search on the Internet will show you that there are many publications on category theory related to mathematics, logic, computer science, and physics. The number of research papers is orders of magnitude higher.

This book is an introduction to category theory. The goal is to understand Yoneda's lemma. The Yoneda lemma is often referred to as "the hardest Trivial thing in mathematics." Mathematicians often feel frustrated and ask why we can't just say it's right even though it's self-evident. "Lemma" means usually a helper proposition for proving a big theorem, but, in some special cases, it's an honorific title for a great theorem, which is the mother of daily proved theorems by professional mathematicians. For example, Nakayama's lemma and Zorn's lemma are very well known by mathematicians all over the world and are used once for a while, or touched on once in their schooldays. Sorry, they are not mentioned in this book. In category theory, if you can understand Yoneda's lemma properly, you can consider you graduated from your introductory category theory course. No, is that too much? I must confess that it took me decades to get the Yoneda lemma as a life-long companion just like the formula for the quadratic equations. It might be better to restate that if you can get to the chapter of Yoneda, you've graduated from the introductory course on category theory.

I stuck to the explicitness of the data structure and the grammar of diagram tracing. The reason is as follows:

- Most beginners have a hard time in grasping the concept of natural transformation, the first hurdle of abstraction, unless they are conscious of types. I feel a bit awkward to take the following example, but let me try. We use expressions like "function  $f(x)$ " in a math class or daily technical conversation. But, when we bring it into a computer program, the function must be  $f$  and not  $f(x)$ . The latter expression  $f(x)$  is a function application of the function  $f$  to the data  $x$ . And even for us humans, when discussing category theory, there are times when we are required to abandon our human minds and think of ourselves as a computer. When the calculation is completed and the meaning is to be reconsidered, the human mind is allowed to reenter.  
- The word "chasing" appearing in the technical phrase "diagram chasing" refers to trying to see something that cannot be seen at a glance where one has no idea in what order the focus should be moved. Such a situation occurs everywhere in category theory.

Taking all these into account, I adopted the following policy:

- For concepts such as functors, natural transformations, cones, and limits, we give them concrete data structures, aiming that those data can be input to a computer.  
- Contains many short examples of Haskell code. The compiler scolds you if it fails to match the types, so you don't have to waste your time trying to reach a goal that you never succeed in. Running the code is not a proof of the theorem, but it does convince you that the inferences here and there in the proof are correct.  
- Samples of Haskell code are roughly classified into two types. One consists of functors and natural transformations found in the wild in the Haskell standard

libraries. On the other hand, Haskell lets you create and play with small worlds of toy categories, functors, natural transformations, and limits. I won't make the distinction between the two types explicit, but you can easily distinguish them.

- In presenting diagram chasing, the drawer's intentions are described as clearly as possible; why the arrow should be drawn at this time and at this place.  
- Diagrams have a grammar and a drawing order. I have not been able to formulate this clearly yet, but I will try to make a presentation with that necessity in mind.

I will describe the features of this book as a precaution to the reader:

- This is an introductory book on category theory aiming at understanding Yoneda's lemma. I would also recommend it to those who want to re-challenge category theory. I would like you to experience that the theory will look different when you are strongly aware of the "grammar" of diagram chasing and the data structure of the category.  
- All proofs of the theorems are given. You should be f铝合金 with the concepts of sets, maps, injections, surjections, Cartesian products, relations, symmetry, reflexivity, transitivity, and so on. It is assumed that you have the basic knowledge or the skill to acquire new knowledge that you have a proper understanding of equivalence relations and equivalence classes, or that you can quickly recall or supplement them by looking them up in textbooks or on the Internet.  
- In some chapters, applications to linear algebra, groups, rings, and fields are given. However, you can safely skip those examples. It just a bit narrows down the way you can enjoy it.  
- Haskell example code is everywhere. You can skip it and follow the discussion of category theory itself, but using Haskell is a major feature of this book, so I guarantee you'll enjoy reading it. See [2] for a quick or in-depth introduction to Haskell. You can find many other friendly books on Haskell on the Internet. You should be able to enjoy category theory even more if you do so. In principle, the sample code should be "one-shot," and with some exceptions, mutual references (import, export) are not employed. It means that you can pick up and read sample code independently. There is no versatility at all. However, if you read and compare them, you will find that there is a consistent design pattern.  
- Mathematics students will find this book useful as a companion to a standard introductory text.  
- I won't mention any of the beautiful libraries for category theory that are actively being developed in the Haskell community. They are for intermediate-level category theory students and above, and I do not have enough competence and experience to introduce them to the reader.

I highly recommend Awodey [3] to readers interested in logic and computer science. For the technical terms, I referred to Mac Lane's book [1], the bible on

category theory, and Leinster's masterpiece [4]. The Haskell processor used GHCi version 8.6.5.

I am grateful to all those who reviewed the manuscript.

Koganei, Japan

Shuichi Yukita

# References

1. Mac Lane S (1998) Categories for the working mathematician, Graduate texts in mathematics, vol 5, 2nd edn. Springer  
2. Lipovaca M (2011) Learn you a Haskell for great good! PDF on-line available  
3. Awodey S (2006) Category theory. Oxford University Press  
4. Leinter T (2014) Basic category theory, Cambridge studies in advanced mathematics, vol 143. Cambridge University Press

# Contents

# 1 Category, Functor, Natural Transformation 1

1.1 Sets and Functions 1  
1.2 Category, Object, Morphism 7  
1.3 Data Structures of Categories 10  
1.4 Functor and Contravariant Functor 12  
1.5 Faithful Functors and Full Functors 18  
1.6 Natural Transformations 21  
1.7 Subcategories of Hask 30

References 33

# 2 Equivalence of Categories 35

2.1 Functor Category 35  
2.2 Equivalence of Categories 39

# 3 Universality and Limits 51

3.1 Initial and Terminal Objects 51  
3.2 Products 53  
3.3 Coproducts 57  
3.4 Limits 61  
3.5 Colimits 69  
3.6 Existence of Limits 80  
3.7 Existence of Colimits 91

# 4 Functors and Limits 103

4.1 Functors Map Cones to Cones 103  
4.2 Hom Functors and Limits 105  
4.3 Hom Functors and Colimits 108  
4.4 Executable Examples 111  
4.5 Limit Functors 114

4.5.1 Limits as a Functor 115  
4.5.2 Colimits as a Functor 116

# 5 Adjoints 119

5.1Adjunctions 119  
5.2 Unit and Counit 121  
5.3 Triangle Identities 124  
5.4 Universal Arrows and Adjunctions 126  
5.5 Equivalent Formulations of Adjunction 128  
5.6 Adjunction and Category Equivalence 138  
5.7 Global Naturality of Adjunction 145  
5.8Adjunctions and Limits 147

# 6 Monads 151

6.1 Kleisli Triples 151  
6.2 Moggi' Theory 154

6.2.1 Non-determinism and the List Functor 154  
6.2.2 Computation with Output 156  
6.2.3 Continuation Passing 159  
6.2.4 Computation that May Fail and the Maybe Functor 163

6.3 Monads 165  
6.4 Monad Instances in Haskell 174

6.4.1 Computation with Output(revisited) 174  
6.4.2 Computation with Continuation(revisited) 178

6.5 Functor, Applicative, and Monad 183  
6.6 Monads and Adjoints 189

6.6.1 Adjoints to Monads 189  
6.6.2 List Monad as Adjoint 191

Reference 196

# 7 Representable Functors 197

7.1 Representation of Covariant Functors 197  
7.2 Representation of Contravariant Functors 202  
7.3 The Yoneda Lemma 204

7.3.1 Covariant Case 204  
7.3.2 Contravariant Case (Presheaves) 210

7.4 Milewski's "Understanding Yoneda" 215

7.4.1 Specification Determines Implementation 216  
7.4.2 A Function That Has the Same Signature as the Identity Function 217

7.5 Reverse Engineering by the Yoneda Lemma 218

7.5.1 A Machine That Has a Hidden Parameter 218  
7.5.2 A Machine That Hides a List Inside 220  
7.5.3 A Machine That Has a Secret Morphism 222  
7.5.4 The Design Pattern with Yoneda 223

7.6 Adjoints Preserve Limits 224

References 226

# 8 Monoidal Categories and Coherence 227

8.1 Categories with Tensor Products 227  
8.2 Coherence—Part One 238  
8.3 Monoidal Functors 245  
8.4 Coherence—Part Two 246  
References 263

# Epilogue 265

# Appendix A: Sets and Universe 267

# Appendix B: Calculations with Output 269

# Appendix C: Continuation Passing 283

# Index 295

# Category, Functor, Natural Transformation

1

Beginning with sets, functions, and relations, we will see how we are tempted to introduce category theory. After defining the data structures for categories, we will examine some examples. A functor is a function from one category to another that preserves the data structures of the source in its image. Given two categories and two functors between them, a natural transformation is used to compare how the two functors preserve data structures. We will see polymorphic functions in Haskell are natural transformations.

# 1.1 Sets and Functions

The purpose of the first half of this section is to tempt the reader to use a new device that can handle both functions and their variants such as partial functions and relations. The new device is called category. We will first introduce the category of sets and functions or simply the category of sets, then the category of sets and partial functions and the category of sets and relations.

Given two sets  $A$  and  $B$ , we can form their Cartesian product  $A \times B$ . A subset  $\mathbf{R} \subset A \times B$  is called a relation between  $A$  and  $B$ .

We often write as

$$
a R b \Leftrightarrow (a, b) \in R.
$$

Some authors like to say R is the graph of a relation.

When the relation  $R$  satisfies the following condition, it is called a function or mapping.

$$
\text {C o n d i t i o n}: \forall a \in A. \exists ! b \in B. a R b
$$

Here,  $\exists!$  means there exists exactly one thing that satisfies the condition.

Let us consider the case where  $A = B = \{1,2,3\}$  and three relations:

$$
R _ {1} = \{(1, 1), (2, 1), (3, 3) \},
$$

$$
\mathrm {R} _ {2} = \{(1, 1), (1, 2), (2, 2), (3, 3) \}, \text {a n d}
$$

$$
\mathrm {R} _ {3} = \{(1, 1), (2, 3) \}.
$$

Pictorially, we have the following.

![](images/ace3df4561c137572da8074ee4339d8bd1547a266ea8bdf9b75849b9e7891be1.jpg)

![](images/3749cd47e9ad974438694be79c7f458e92eed012716847469db42e11d839ed0e.jpg)

![](images/133a8e0583a231bd641a985f271a8f9b7236f912f9d2e430bcf14c768b941d0a.jpg)

$\mathbb{R}_1, \mathbb{R}_2,$  and  $\mathbb{R}_3$  are all relations. Which of them are functions? While  $\mathbb{R}_1$  is a function, neither  $\mathbb{R}_2$  nor  $\mathbb{R}_3$  are functions.

Roughly speaking, all the points of the source set emit exactly one arrow  $\mapsto$  in order for the relation to be a function. In other words, no two arrows  $\mapsto$  start at the same point in the case of a function. Notice that the notion of function is extremely non-symmetric between input and output.

$\mathbf{R}_3$  is not a function, but it is called a partial function that represents a computation that may fail or a computation that may not terminate forever, which are a primary object of study in computer science. Rational functions, functions that are formed by a fraction of two polynomials, are examples of a partial function. The values are undefined when a given input makes the denominator null. We can write a logic formula for the condition for a relation to be a partial function.

$$
C o n d i t i o n: \forall a \in A. (a R b \wedge a R b ^ {\prime} \Rightarrow b = b ^ {\prime})
$$

In the case of a partial function, every source point emits at most one arrow  $\mapsto$ .

Not to mention, the notion of relation is the basis of database theory, where relational algebra plays the central role.

To sum up, we have the following inclusions:

- A function is a partial function.  
- A partial function is a relation.

Relation  $\mathbf{R}_2$  is neither a function nor a partial function. However, in the theory of functions of a complex variable, we are familiar with the notion of multi-valued function that allows several, possibly infinite, values for a single input value. A typical example is a function of square root  $f(z) = \sqrt{z}$ , which allows twofold values.

The desire to make those multi-valued functions a single-valued function led mathematicians to topology. The Riemann surfaces were thus introduced.

Given two functions  $f: A \to B$  and  $g: B \to C$ , we define their composition  $g \circ f: A \to C$  as

$$
(g \circ f) (a) = g (f (a)).
$$

We know that function composition is associative. But, it is not obvious.

Proposition 1.1 Given three functions  $f: A \to B$ ,  $g: B \to C$ , and  $h: C \to D$ , we have

$$
(h \circ g) \circ f = h \circ (g \circ f).
$$

Proof To prove the statement, we have to show that

$$
((h \circ g) \circ f) (a) = (h \circ (g \circ f)) (a)
$$

holds for all  $a \in A$ .

Let us calculate the LHS (left-hand side).

$$
\begin{array}{l} ((h \circ g) \circ f) (a) \\ = (h \circ g) (f (a)) \\ = h (g (f (a))) \\ \end{array}
$$

Next, calculate the RHS (right-hand side).

$$
\begin{array}{l} (h \circ (g \circ f)) (a) \\ = h ((g \circ f) (a)) \\ = h (g (f (a))) \\ \end{array}
$$

We have established that both sides coincide.

Besides function composition, associative compositions can be found everywhere in mathematics and mathematical sciences. This makes us include associativity in the axioms of the category in what follows.

The composition of partial functions is also associative. We omit the proof. The reader might check each of the following three cases:

$f(a) = \bot$  
$f(a)$  exists, but  $g(f(a)) = \bot$ , and  
-  $g(f(a))$  exists, but  $h(g(f(a))) = \bot$ ,

where we wrote  $f(a) = \bot$  when  $f(a)$  does not exist.

Remark 1.1 We used the symbol  $\perp$  (bottom) to mean that the thing is not defined. If we add  $\perp$  as a member to every set, we can make all the partial functions into total ones. Further, if we require  $f(\perp) = \perp$  for every function, we are led to the world of denotational semantics, which is out of the scope of this exposition.

We have just established that the composition of functions and partial functions is associative. Let us consider relations. Given two relations  $F \subset A \times B$  and  $G \subset B \times C$ , we define their composition  $G \circ F \in A \times C$  as

$$
G \circ F = \{(x, z) \in A \times C \mid \exists y \in B. (x, y) \in F \text {a n d} (y, z) \in G \}.
$$

Proposition 1.2 Given three relations  $F \subset A \times B$ ,  $G \subset B \times C$ , and  $H \subset C \times D$ , we have

$$
(H \circ G) \circ F = H \circ (G \circ F).
$$

Proof We show that

$$
\begin{array}{l} (a, d) \in ((H \circ G) \circ F) \\ \Leftrightarrow (a, d) \in (H \circ (G \circ F)) \\ \end{array}
$$

holds for any  $a \in A$  and  $d \in D$ .

Let us calculate the LHS, applying the definition of  $\circ$  from the outermost (top level) to the inner part.

$$
\begin{array}{l} (a, d) \in ((H \circ G) \circ F) \\ \Leftrightarrow \exists b \in B. a F b \text {a n d} b (H \circ G) d \\ \Leftrightarrow \exists b \in B. a F b \text {a n d} \exists c \in C. b G c \text {a n d} c H d \\ \Leftrightarrow \exists b \in B. \exists c \in C. a F b \text {a n d} b G c \text {a n d} c H d \\ \end{array}
$$

Next, we calculate the RHS, applying the definition of  $\circ$  again from the outermost to the inner part.

$$
\begin{array}{l} (a, d) \in (H \circ (G \circ F)) \\ \Leftrightarrow \exists c \in C. a (G \circ F) c \text {a n d} c H d \\ \Leftrightarrow \exists c \in C. (\exists b \in B. a F b \text {a n d} b G c) \text {a n d} c H d \\ \Leftrightarrow \exists c \in C . \exists b \in B . a F b \text {a n d} b G c \text {a n d} c H d \\ \end{array}
$$

We can exchange the positions of  $\exists b \in B$  and  $\exists c \in C$ . Thus, we have proved the equality.

If we carefully reflect on the discussion above, we find that associativity of function composition comes from that of relations. We have only to show that function composition is the restriction of relation composition to the subclass (of relations) consisting of functions and that the subclass is closed under relation composition.

Note that it is a lucky situation in which a certain binary operation is associative. There are many important non-associative algebras. The most familiar ones everyone can imagine are Lie algebras, but we find an example at the elementary school level.

Example 1.1 Is subtraction associative? Does the following hold?

$$
(1 0 0 - 5 0) - 5 0 = 1 0 0 - (5 0 - 5 0)
$$

Many people carry out mathematical work under various frameworks. Common features are categories consisting of objects and morphisms.

<table><tr><td>Category</td><td>Objects</td><td>Morphisms</td></tr><tr><td>Category of sets</td><td>Sets</td><td>Functions</td></tr><tr><td>Category of sets and partial functions</td><td>Sets</td><td>Partial functions</td></tr><tr><td>Category of sets and relations</td><td>Sets</td><td>Relations</td></tr></table>

What's the good of this? Well, it is common to switch the framework of discussion saying, for example, "so far we have talked about everything in the category of sets and functions, but from now on we will talk about the category of sets and relations."

Let us see further examples that strongly motivate to introduce categories.

Sets in the wild that we encounter everyday are no more than a rabble. Usually, they have structures and structure preserving morphisms. We sometimes want to forget such structures intentionally to gain insight within the framework of adjunctions. Such activities are conducted by forgetful functors. All such emphasized key words will be defined later. Anyway, we must collect examples of such structures that are forgettable.

We first see an algebraic system group. The reader should consult with standard textbooks on algebra. We do not give the definitions here.

Example 1.2 Let  $\mathbb{R}_{\mathrm{add}}$  be a group of real numbers with the addition operation. And let  $\mathbb{R}_{\mathrm{mult}}^{>0}$  be a group of positive real numbers with the multiplication. The (natural) logarithm function

$$
\log : \mathbb {R} _ {\mathrm {m u l t}} ^ {> 0} \to \mathbb {R} _ {\mathrm {a d d}}
$$

is called a group homomorphism from  $\mathbb{R}_{\mathrm{mult}}^{>0}$  to  $\mathbb{R}_{\mathrm{add}}$ . This function observes the group structures of the two groups involved. An awkward reader should consult with one's high school textbook. There, everyone find a formula like this.

$$
\log (x \times y) = \log x + \log y
$$

In this example, we have the inverse homomorphism  $\exp : \mathbb{R}_{\mathrm{add}} \to \mathbb{R}_{\mathrm{mult}}^{>0}$  that also keeps the group structure via the formula

$$
\exp (x + y) = \exp (x) \times \exp (y).
$$

We say, in this case, the logarithm function is an isomorphism.

Homomorphisms in algebraic systems can be viewed as just a function between two sets if we ignore algebraic structures. When we introduce a new algebraic system, we should check if the composition of morphisms as a plain function yields a structure preserving morphism.

Example 1.3 Let us consider two real vector spaces  $A$  and  $B$  with linear mapping  $f: A \to B$ . We may regard linear mapping as just a homomorphism of additive groups. However,  $f$ , as a linear mapping, has the property of preservation of scalar multiplication. Namely, we require that for all  $\vec{u}, \vec{\nu} \in A$  and  $a, b \in \mathbb{R}$

$$
f (a \vec {u} + b \vec {v}) = a f (\vec {u}) + b f (\vec {v})
$$

should hold.

We may replace "real numbers" with other fields such as "complex numbers." To sum up, we have the following.

<table><tr><td>Category</td><td>Objects</td><td>Morphisms</td></tr><tr><td>Category of groups</td><td>Groups</td><td>Group homomorphisms</td></tr><tr><td>Category of real vector spaces</td><td>Real vector spaces</td><td>Real linear mappings</td></tr><tr><td>Category of complex vector spaces</td><td>Complex vector spaces</td><td>Complex linear mappings</td></tr></table>

So far, we examined various cases where sets play the central role. They have elements and structures that force elements to behave consistently under operations the particular category imposes. Anyway, we treated objects that disclose their internal structures to the world.

Information hiding is one of the key concepts in the object oriented programming paradigm. We are reluctant to accept information that we can do without it. Not knowing anything without which we can do, we can keep a certain level of security.

Now, we proceed to tackle situations where, at first, we have no clue to imagine the internal structures.

Example 1.4 Let us consider the set  $A = \{1,2,3\}$ . We can see the internal structure of  $A$ , knowing what the elements of  $A$  are. We introduce a function  $f:A\to A$ :

$$
\begin{array}{c} A \xrightarrow {f} A \\ 1 \longmapsto 2 \\ 2 \longmapsto 3 \\ 3 \longmapsto 1 \end{array}
$$

When someone does not know the internal structure of  $A$ , what kind of thing can he/she do at best? They are provided with only information about  $f$ . They only know that it yields nothing if  $f$  is iterated three times. With this observation, they might suppose  $A$  has three elements and these are circulated by  $f$ . This is exactly what physicists of elementary particles are doing in their daily life.

So far, we have seen examples without giving definitions. In the next sections, we discuss various mathematical phenomena based on a rigorous basis.

# 1.2 Category, Object, Morphism

The reader is familiar with the term "set" and with the fact that naive set theory leads to paradoxes.

Russel's paradox arises when we consider a set like this:

$$
R = \{x \mid x \notin x \}.
$$

If  $R \in R$ , then by the definition of  $R$  we can deduce that  $R \notin R$ . If  $R \notin R$ , again by the definition of  $R$  we can deduce that  $R \in R$ . Thus, we get a contradiction.

To avoid such an absurdity, we must use the term carefully. One solution is to introduce the notion of universe originally proposed by Grothendieck. We roughly follow the style of Mac Lane [1]. Some details are given in Appendix A. We assume the existence of a sufficiently large set  $U$  called universe.  $U$  has all the needed things as its elements. If a set  $x$  is an element of  $U$ , we say  $x$  is small or  $x$  is a small set. Universe  $U$  is not a small set. Subsets of  $U$  are called a class.  $U$  is a subset of itself, so  $U$  is a class.

Remark 1.2 In the rest of this exposition, we often talk about type class in Haskell. Note that this concept of class and the class we have defined above have nothing to do with each other.

Definition 1.1 A category consists of a set of objects  $A, B, C, \dots$  and a set of morphisms  $f, g, h, \dots$ . These constituents are subject to the following conditions.

1. For every morphism  $f$  we have the unique object domain  $\operatorname{dom} f$  and the unique object codomain  $\operatorname{cod} f$ . When  $\operatorname{dom} f = A$  and  $\operatorname{cod} f = B$ , we write  $f: A \to B$  or  $A \xrightarrow{f} B$ .  
2. Given two morphisms  $f$  and  $g$  with  $\operatorname{dom} g = \operatorname{cod} f$ , there exists their unique composite  $g \circ f: \operatorname{dom} f \to \operatorname{cod} g$ .  
3. The composition operation is associative, namely, given three morphisms

$$
A \xrightarrow {f} B \xrightarrow {g} C \xrightarrow {h} D,
$$

we have

$$
h \circ (g \circ f) = (h \circ g) \circ f.
$$

4. For all object  $A$ , there exists a morphism  $1_A : A \to A$  called the identity morphism that satisfies the following conditions:

for all  $f:A\to B$  and  $g:B\to A$

$$
f \circ 1 _ {A} = f \quad \text {a n d} \quad 1 _ {A} \circ g = g.
$$

We denote by  $\mathrm{Obj}(\mathcal{C})$  the set of all objects of  $\mathcal{C}$  and by  $\mathrm{Mor}(\mathcal{C})$  the set of all morphisms of  $\mathcal{C}$ . We denote by  $\mathrm{Hom}_{\mathcal{C}}(A, B)$  the set of all morphisms of  $\mathcal{C}$  that have domain  $A$  and codomain  $B$ .

Remark 1.3 The identity morphism  $1_A$  is uniquely determined for each  $A$ . Given another morphism  $1'_A$  that satisfies the same condition above, we can easily deduce that  $1_A = 1'_A$ .

There are morphisms that have a special property. When this kind of morphism exists between two objects, we can say they are essentially the same.

Definition 1.2 We say that  $f: A \to B$  is an isomorphism if there exists a morphism  $g: B \to A$  such that  $g \circ f = 1_A$  and  $f \circ g = 1_B$ . If this is the case,  $g$  is called an inverse morphism (or simply an inverse) of  $f$  and written as  $g = f^{-1}$ . The relation inverse is easily shown to be symmetric. So, we also have that  $f$  is an inverse morphism of  $g$ .

Proposition 1.3 If  $f$  has an inverse morphism, then the inverse morphism is uniquely determined.

Proof Let  $g'$  be another inverse to  $f$ , namely  $g'$  satisfies the same conditions for  $g$ . Let us begin with the condition for  $g$ .

$$
g \circ f = 1 _ {A}
$$

We can compose  $g'$  from right to both sides. Then, we have

$$
g \circ f \circ g ^ {\prime} = g ^ {\prime}
$$

Since  $f \circ g' = 1_B$ , we have  $g = g'$ .

![](images/3026d2034ebe0413384c2649622be13d42b054e52f444883c62435f6b7c6908f.jpg)

Let  $\mathcal{C}$  is a category. If  $\mathrm{Obj}(\mathcal{C})$  and  $\mathrm{Mor}(\mathcal{C})$  are both small, then  $\mathcal{C}$  is called small or a small category. A category that is not small is called large or a large category.

Let  $\mathcal{C}$  is a category. If  $\mathcal{C}(A, B)$  is small for all pairs of objects  $A$  and  $B$ , then  $\mathcal{C}$  is called locally small or a locally small category.  $\mathcal{C}$  is not necessarily small when it is locally small.

Remark 1.4 We often say "A is not a set" to mean that it is not a small set. This rough usage is seen everywhere, and we can easily notice the exact meaning of such a statement.

We will see several examples of a large category. All of them happen to be locally small.

Example 1.5 Category Set is defined as follows. The set of objects is the set of all small sets. The set of morphisms is all the functions between those small sets. For all pairs of small sets  $A$  and  $B$ , we know  $\mathbf{Set}(A, B)$  is small. Thus, Set is locally small. See Appendix A.

All of the algebraic systems we are going to see have small sets as their underlying set.

Example 1.6 Category Grp is defined as follows. The set of objects is the set of all groups. The set of morphisms is all the homomorphisms between those groups. Category Grp is locally small.

Example 1.7 Category  $\mathbf{Ab}$  is defined as follows. The set of objects is the set of all abelian groups. The set of morphisms is all the homomorphisms between those abelian groups.  $\mathbf{Ab}$  is locally small. Category  $\mathbf{Ab}$  is a subcategory of  $\mathbf{Grp}$ . We will give the definition of a subcategory shortly.

Example 1.8 Category Top is defined as follows. The set of objects is the set of all topological spaces. The set of morphisms is all the continuous functions between those topological spaces. Category Top is locally small.

Definition 1.3 We say that category  $\mathcal{A}$  is a subcategory of  $\mathcal{B}$  if the following conditions are all satisfied:

-  $\operatorname{Obj}(\mathcal{A})$  is a subset of  $\operatorname{Obj}(\mathcal{B})$ .  
-  $\mathcal{A}(X,Y)$  is a subset of  $\mathcal{B}(X,Y)$  for all pairs of  $X,Y\in \mathrm{Obj}(\mathcal{A})$  
- Equality  $g \circ_{\mathcal{A}} f = g \circ_{\mathcal{B}} f$  holds for all the pairs of composable morphisms  $f, g \in \operatorname{Mor}(\mathcal{A})$ , where  $\circ_{\mathcal{A}}$  and  $\circ_{\mathcal{B}}$  are composition of morphisms in  $\mathcal{A}$  and  $\mathcal{B}$ , respectively.

Example 1.9 Let  $k$  be a field, such as  $\mathbb{Q}, \mathbb{R}, \mathbb{C}, \mathbb{F}_p$ , or others.  $\mathrm{Vect}_k$  is a category of finite-dimensional  $k$ -vector spaces; the set of objects consists of all finite-dimensional  $k$ -vector spaces, and the set of morphisms consists of all  $k$ -linear mappings between these vector spaces.  $\mathrm{Vect}_k$  is large, but locally small.

Example 1.10 We introduce some finite categories that are frequently used in the rest of this exposition.

- 0 is a category with no objects and no morphisms.  
- 1 is a category with one object and no morphisms other than the identity morphism.

- 2 is a category with two objects  $A, B$  and one morphism  $f: A \to B$  other than the identity morphisms  $1_A, 1_B$

Example 1.11 Any partially ordered set (poset) can be seen as a category. The set of objects is the underlying set. When  $a \leq b$ , there is exactly one morphism from  $a$  to  $b$ . The reader should check morphisms so that they satisfy all the axioms of the category.

Example 1.12 Category Hask is defined as follows. Objects are Haskell types. Morphisms from object  $A$  to  $B$  are functions of type  $A \to B$ .

Remark 1.5 Many authors accuse Hask of not being even a category. See [2] for more information. The author takes the position that viewing Hask as a category helps us to understand various phenomena in computation. Let us compromise, expecting a theoretical breakthrough is coming someday. We will use Hask instead of Set when we present code for Yoneda machines.

If we reverse all the arrows in a discussion, it is very often the case that the discussion is still valid. Such phenomena are formulated as the principle of duality.

Definition 1.4 Given a category  $\mathcal{A}$ , we can construct an opposite category as follows.  $\mathcal{A}^{\mathrm{op}}$  is a category, where  $\operatorname{Obj}(\mathcal{A}^{\mathrm{op}}) = \operatorname{Obj}(\mathcal{A})$  and morphisms are all reversed.

# 1.3 Data Structures of Categories

We have seen examples of categories in the wild of mathematics. All of them are based on sets and functions. Transitivity and associativity of composition are obvious in those cases. In this section, we will examine artificial toy examples where such properties are not clear.

Example 1.13 Let us consider a category with one object  $A$  and one morphism  $f: A \to A$  other than mandatory  $1_A$  as in Fig. 1.1. We want a composition table for the composition of morphisms.  $f$  is composable with itself. The result will be either  $1_A$  or  $f$ . There are no other options.

![](images/74fb5d15a7b02fe0f7ad247811af4c5fcd4032662c572fa668b7fdabc8446917.jpg)  
Fig.1.1 One morphism other than the identity

In the case of  $f\circ f = 1_{A}$  , we have

$$
\begin{array}{c c c} & 1 _ {A} & f \\ \hline 1 _ {A} & 1 _ {A} & f \\ f & f & 1 _ {A} \end{array}
$$

In the case of  $f \circ f = f$ , we have

$$
\begin{array}{c c c} & 1 _ {A} & f \\ \hline 1 _ {A} & 1 _ {A} & f \\ f & f & f \end{array}
$$

Both cases observe associativity. Therefore, we can define two different categories out of a generator  $f$ . Equations  $f \circ f = 1_A$  and  $f \circ f = f$  are called relations.

Example 1.14 Let us consider a category with one object  $A$  and the set of morphisms

$$
\{1 _ {A}, f, f ^ {2}, f ^ {3}, \dots , f ^ {n}, \dots \}
$$

as in Fig. 1.2.

The composition table is given as follows.

$$
\begin{array}{c c c c c c} & 1 _ {A} & f & \dots & f ^ {n} & \dots \\ \hline 1 _ {A} & 1 _ {A} & f & \dots & f ^ {n} & \dots \\ f & f & f ^ {2} & \dots & f ^ {n + 1} & \dots \\ \vdots & \vdots & \vdots & \ddots & \vdots & \dots \\ f ^ {m} & f ^ {m + 1} & \dots & \dots & f ^ {m + n} & \dots \\ \vdots & \vdots & \vdots & \vdots & \vdots & \ddots . \end{array}
$$

This is a free monoid with generator  $f$  (Fig. 1.2).

![](images/8fd0f6ba9a2c4161453a754928004e5ff3b60fbf4af27a3a14f9fa5463a3b089.jpg)  
Fig.1.2 A free monoid

![](images/fbe5328b923c1c621a996f6e00e555ae291ad0121faab1568567da26e5f75e30.jpg)  
Fig.1.3 A non-symmetric relation

Example 1.15 Let us consider a category with two objects  $A$  and  $B$ , and with two morphisms  $f: A \to B$  and  $g: B \to A$  other than identity morphisms.  $f$  and  $g$  generate all the morphisms. We say that  $\{f, g\}$  is the system of generators.

We impose one relation on this category:  $g \circ f = 1_A$ . If we examine the table carefully, we see that the table is closed under the binary operation of composition. The empty slots mean that the case is not composable. To establish associativity, we must check in all the cases of triples  $(a, b, c)$ , where  $a, b, c$  are morphisms, that  $(a \circ b) \circ c = a \circ (b \circ c)$  holds.

<table><tr><td></td><td>1A</td><td>1B</td><td>f</td><td>g</td><td>f o g</td></tr><tr><td>1A</td><td>1A</td><td></td><td></td><td>g</td><td></td></tr><tr><td>1B</td><td></td><td>1B</td><td>f</td><td></td><td>f o g</td></tr><tr><td>f</td><td>f</td><td></td><td></td><td>f o g</td><td></td></tr><tr><td>g</td><td></td><td>g</td><td>1A</td><td></td><td>g</td></tr><tr><td>f o g</td><td></td><td>f o g</td><td>f</td><td></td><td>f o g</td></tr></table>

Examples 1.13-1.15 are narrowly tractable with pencil and paper. We will provide Haskell programs for checking the consistency of a table to be that of a category.

We can construct a new category out of two categories in various ways. The most important one is the product category.

Definition 1.5 Let  $\mathcal{A}$  and  $\mathcal{B}$  be categories. The product category  $\mathcal{A} \times \mathcal{B}$  is given by:

- Objects are all pairs  $(A, B)$  where  $A \in \operatorname{Obj}(\mathcal{A})$  and  $B \in \operatorname{Obj}(\mathcal{B})$ .  
- Morphisms are all pairs  $(f, g)$  where  $f: A_1 \to A_2 \in \mathcal{A}(A_1, A_2)$  and  $g: B_1 \to B_2 \in \mathcal{B}(B_1, B_2)$ .

# 1.4 Functor and Contravariant Functor

Given two linear spaces, we naturally compare their structures via linear mappings. Given two groups, we compare their group structures via group homomorphisms. Functors are homomorphisms between two categories.

Definition 1.6 The data for a category consists of objects, morphisms, table of morphism composition. A functor from category  $\mathcal{A}$  to  $\mathcal{B}$  is a collection of functions that is united to be one big function as follows:

- A function  $F_0: \mathrm{Obj}(\mathcal{A}) \to \mathrm{Obj}(\mathcal{B})$  called a function on objects,  
- A collection of functions

$$
F _ {1} \left(A _ {1}, A _ {2}\right): \mathscr {A} \left(A _ {1}, A _ {2}\right)\rightarrow \mathscr {B} \left(F _ {0} \left(A _ {1}\right), F _ {0} \left(A _ {2}\right)\right)
$$

for all the pair  $A_1, A_2 \in \mathrm{Obj}(\mathcal{A})$ . Since there are no overlapping of domains of definition, we can collectively call the collection as a function on morphisms.

From now on, we omit suffixes and parentheses in  $F_0(A)$  and write as  $FA$ . We omit suffix, object parameters, and parentheses in  $F_1(A_1, A_2)(f)$  and write as  $Ff$ .

We impose the following conditions on the function of morphisms:

- For all  $A \in \mathrm{Obj}(\mathcal{A})$ , equality  $F(1_A) = 1_{F(A)}$  holds.  
- For all pairs of morphisms  $f: A_1 \to A_2$  and  $g: A_2 \to A_3$ , equality  $F(g \circ f) = F(g) \circ F(f)$  holds.

Figure 1.4 may convey the feeling of this formality.

Example 1.16 Homology functors  $H_{n}$  from Top to Ab return a group homomorphism  $H_{n}(f):H_{n}(X)\to H_{n}(Y)$  for a given continuous function  $f:X\rightarrow Y$ .

Example 1.17 Let  $X$  and  $Y$  be posets and  $f: X \to Y$  be order-preserving function. We say  $f$  is order preserving if  $f(x_{1}) \leq f(x_{2})$  for all pairs  $x_{1} \leq x_{2}$  in  $X$ . When we regard  $X$  and  $Y$  as categories,  $f$  is a functor.

![](images/b507c68d9b9b6ab5a645e61d5af761ff34619084a7bda57ebe83fe6896c2682c.jpg)  
Fig.1.4 Morphism composition is preserved

Example 1.18 Figure 1.5 depicts a functor between posets. When we draw a graph representation of a category, we often omit obvious transitive closure and identities. The reader should check if this example satisfies all the axioms.

Example 1.19 Let us examine the List functor in Hask. Given a type A in Haskell, we can construct a type [ ] A or [A]. Both are syntactically correct and have the same meaning. [ ] is called a type constructor. Figure 1.6 shows that map plays the role of functor's function on morphisms. map satisfies the condition:

$$
\text {m a p} (\mathrm {g}. \mathrm {f}) = \text {m a p} \mathrm {g}. \text {m a p} \mathrm {f}.
$$

Example 1.20 Let us examine the Maybe functor in Hask. Given a type A in Haskell, we can construct a type Maybe A. Maybe is a type constructor as well as a List. Figure 1.7 shows that fmap plays the role of functor's function on morphisms. map satisfies the condition:

$$
f m a p (g . f) = f m a p g . f m a p f.
$$

Function fmap is shared by all the functor instances in Haskell. Programmers do not explicitly write which functor is intended. In most cases, the compiler precisely infers which one to take. If this is not the case, programmers must add an annotation to fmap.

![](images/0bbeebebd2aed276885cd4ff8c94bc3092f83b6aa3401f4748045922c1442a9f.jpg)  
Fig.1.5 A functor between posets

![](images/ba6729c357359f00c642b1a78254053b72d9f360be5a4a05dacef0302d98c179.jpg)  
Fig.1.6 List functor

![](images/9c89f1536a93b0a65f76626955c257070cd102aedb31c3d4a12db46125922dfd.jpg)  
Fig.1.7 Maybe functor

Example 1.21 Tree structures are naturally seen as an instance of functor. Let us consider binary trees.

Listing 1.1 Tree.vs  
```haskell
1 module Tree where  
2 import Data.Char  
3  
4 data Tree a = Empty | Node a (Tree a) (Tree a)  
5  
6 instance (Show a) => Show (Tree a) where  
7 show x = show1 0 x  
8  
9 show1 :: Show a => Int -> (Tree a) -> String  
10 show1 n Empty = ""  
11 show1 n (Node x t1 t2) =  
12 show1 (n+1) t2 ++  
13 indent n ++ show x ++ "\n" ++  
14 show1 (n+1) t1  
15  
16 indent :: Int -> String  
17 indent n = replicate (n*4),  
18  
19 instance Functor Tree where  
20 fmap f Empty = Empty  
21 fmap f (Node x t1 t2) =  
22 Node (f x) (fmap f t1) (fmap f t2)  
23  
24 -- test data  
25 tree2 = Node "two" (Node "three" Empty Empty)  
26 (Node "four" Empty Empty)  
27 tree3 = Node "five" (Node "six" Empty Empty)  
28 (Node "seven" Empty Empty)  
29 tree1 = Node "one" tree2 tree3  
30  
31 string2int :: String -> Int  
32 string2int "one" = 1  
33 string2int "two" = 2  
34 string2int "three" = 3  
35 string2int "four" = 4  
36 string2int "five" = 5
```

```txt
37 string2int "six" = 6  
38 string2int "seven" = 7  
39 string2int _ = 0  
40  
41 tree0 = fmap string2int tree1  
42  
43 { -suggested tests  
44 fmap (map toUpper) tree1  
45 fmap string2int tree1  
46 fmap length tree1  
47 }
```

Line 4 defines the binary tree data structures. Lines 6-17 implement an instance of the Show type class. Lines 19-22 implement a functor instance for the binary tree. Some tests are shown in Fig. 1.8.

Definition 1.7 A functor from category  $\mathcal{A}^{\mathrm{op}}$  to  $\mathcal{B}$  is often called a contravariant functor. When we want to distinguish functors that we saw so far from contravariant functors, we use the term covariant functor.

Example 1.22 Figure 1.9 illustrates a contravariant functor. If we redraw Fig. 1.9 by replacing  $\mathcal{A}^{\mathrm{op}}$  with  $\mathcal{A}$  while keeping the correspondence, we get Fig. 1.10.

```hcl
*Tree> tree1
    "seven"
    "five"
    "six"
    "one"
    "four"
    "two"
    "three"
```

Fig.1.8 Binary tree as a functor

![](images/59fdef771cdf951aefd7f069a6b1ff9b8f731c18bd9cf35968883ca24566fe08.jpg)  
Fig.1.9 Contravariant functor

![](images/641029247e5608a98ae4774d9c28c00746c85f3d8beecfb1e7cec0f062ae448b.jpg)  
Fig.1.10 Arrows are reversed

Example 1.23 Functor  $(\dashrightarrow)$  has two variables. If we fix the first argument, we obtain a covariant functor. If we fix the second, we obtain a contravariant one. These are called Hom functors. We will discuss this in detail in Chap. 7.

In the following sample code, we do not import an extra library. We use "do it ourselves" version of Contra for our purpose. Note that functor ( , ) has two arguments. A functor instance for the first variable fixing the second is already defined in Prelude. We have to add an instance for the second variable by ourselves.

Listing 1.2 homfunctors.hs  
```haskell
1 {- defined in default startup environment   
2 class Functor f where   
3 fmap :: (a -> b) -> f a -> fb   
4   
5 instance Functor ((->) r) where   
6 fmap = (.   
7   
8 instance Functor ((, ) a) where   
9 fmap f (x,y) = (x, f y)   
10 -}   
11   
12 class Contra f where   
13 pamf :: (a -> b) -> fb -> fa   
14   
15 newtype Moh ba = Moh {getHom :: a -> b}   
16   
17 instance Contra (Moh b) where   
18 pamf f (Moh g) = Moh (g . f)   
19   
20 newtype Riap ba = Riap {getPair :: (a,b)}   
21   
22 instance Functor (Riap b) where   
23 fmap f (Riap (x,y)) = Riap (f x,y)
```

Lines 1-10 are excerpts from the standard library source code in the comment block. Lines 12-13 define a type class Contra with one class method spamf that corresponds to fmap for the Functor class. Line 15 introduces a wrapping Moh for the exchange of variables. Lines 17-18 declare an instance of Contra for Moh. Tests for fmap and spamf can be done as follows.

```latex
\*Main> fmap  $\backslash \mathbf{x}\rightarrow \mathbf{x}*\mathbf{x})$ $\backslash \mathbf{x}\rightarrow \mathbf{x} + 1)$  10  $= = 121$  True   
\*Main> getHom (pamf  $\backslash \mathbf{x}\rightarrow \mathbf{x}*\mathbf{x})$  (Moh  $(\backslash x\rightarrow x + 1))$  ）10  $= = 101$  True
```

Line 20 defines another wrapping for the exchange of variables. This way we can declare a Functor instance fixing the second variable. Tests can be done as follows.

```latex
\*Main> fmap  $\text{山} - >$  x\*x）(10,10）  $= =$  (10,100) True   
\*Main> getPair（fmap  $\text{山} - >$  x\*x）(Riap(10,10)))  $= =$  (100,10) True
```

# 1.5 Faithful Functors and Full Functors

Like the concepts of injection and surjection for functions between sets, we introduce the concepts of faithful and full functors.

Definition 1.8 Let  $F:\mathcal{A}\to \mathcal{B}$  be a functor. If its function on morphisms

$$
F: \mathscr {A} (A _ {1}, A _ {2}) \rightarrow \mathscr {B} (F (A _ {1}), F (A _ {2}))
$$

is injective for all pairs  $A_1, A_2 \in \mathrm{Obj}(\mathcal{A})$ , we say  $F$  is faithful. If its function on morphisms is surjective for all pairs  $A_1, A_2 \in \mathrm{Obj}(\mathcal{A})$ , we say  $F$  is full. If its function on morphisms is bijective for all pairs  $A_1, A_2 \in \mathrm{Obj}(\mathcal{A})$ , we say  $F$  is full and faithful.

Example 1.24 Let us consider a functor  $F: \mathcal{A} \to \mathcal{B}$  as in Fig. 1.11. We write down functions on objects and on morphisms as follows.

$$
F (A _ {1}) = B _ {1}, \quad F (A _ {2}) = B _ {2}
$$

$$
F (a _ {1}) = b _ {1}, \quad F (a _ {2}) = b _ {2}
$$

![](images/2f433afb62e3719380ec1f2c593ca3d47941748ee28f7994377de9ceae7f2c33.jpg)  
Fig.1.11 Full and faithful functor

Notice that a functor can be full and faithful, even though its function on objects is not surjective.

Example 1.25 Let us consider a functor  $F: \mathcal{A} \to \mathcal{B}$  as in Fig. 1.12. We write down functions on objects and on morphisms as follows.

$$
F (A _ {1}) = B _ {1}, \quad F (A _ {2}) = B _ {2}
$$

$$
F (a _ {1}) = b _ {1}, \quad F (a _ {2}) = b _ {2}
$$

Then, we see that  $F$  is faithful but not full since its function on morphisms is not surjective.

Example 1.26 Let us consider a functor  $F: \mathcal{A} \to \mathcal{B}$  as in Fig. 1.13. We write down functions on objects and on morphisms as follows.

$$
F (A _ {1}) = B _ {1}, \quad F (A _ {2}) = B _ {2}
$$

$$
F (a _ {1}) = b _ {1}, \quad F (a _ {2}) = b _ {1}
$$

Then, we see that  $F$  is full but not faithful since its function on morphisms is not injective.

![](images/28081142f038131495f054a3f4046cdcd8016a06de8ac425a81ce4fbb629546b.jpg)  
Fig.1.12 Faithful but not full

![](images/3f08c1de3ef8a890cb65cf2288820fb5a922e90cf95639d239c56c52c36194de.jpg)  
Fig.1.13 Full but not faithful

Example 1.27 Let us consider a functor  $F: \mathcal{A} \to \mathcal{B}$  as in Fig. 1.14. We write down functions on objects and on morphisms as follows.

$$
F (A _ {1}) = F (A _ {3}) = B _ {1}, \quad F (A _ {2}) = F (A _ {4}) = B _ {2}
$$

$$
F (a _ {1}) = b _ {1}, \quad F (a _ {2}) = b _ {1}
$$

Then, we see that  $F$  is faithful even though its function on morphisms is not injective.

We will see some examples in the wild.

Example 1.28 Let us consider an embedding functor  $F: \mathbf{Ab} \to \mathbf{Grp}$ . We can easily check that  $F$  is full and faithful.

Example 1.29 Let us consider a forgetful functor  $F: \mathbf{Top} \to \mathbf{Set}$ . Its function on objects sends a topological space to its underlying set. Its function on morphisms sends a continuous function to a function between underlying spaces. This functor is faithful but not full.

Example 1.30 A complex number consists of its real part and imaginary part. Thus, an  $n$ -dimensional complex vector space can be seen as a  $2n$ -dimensional real vector space.

![](images/e9ca2ed73813b1c0b25a8a8a92aee880e9ff68d1ce30ea5d40a709f180462119.jpg)  
Fig.1.14 Faithful but non-injective function on morphisms

We consider a functor  $F: \mathrm{Vect}_{\mathbb{C}} \to \mathrm{Vect}_{\mathbb{R}}$ . Let  $V$  be an object in  $\mathrm{Vect}_{\mathbb{C}}$ , namely a complex  $n$ -dimensional vector space. Let  $FV$  be a real  $2n$ -dimensional vector space sharing the same underlying additive group. The difference is their scalar multiplication. So much for the function of objects.

As to the function of morphisms, a complex linear mapping can be considered as a linear mapping restricting scalar multiplication from complex to real.

Conversely, an arbitrary real linear mapping is not necessarily a complex linear mapping. So, we have

$$
\operatorname {V e c t} _ {\mathbb {C}} \left(V _ {1}, V _ {2}\right) \subsetneq \operatorname {V e c t} _ {\mathbb {R}} \left(F V _ {1}, F V _ {2}\right).
$$

Let us employ matrix representations with a fixed basis. Then, we can identify  $V = \mathbb{C}^n$  and  $FV = \mathbb{R}^{2n}$ . Then, morphisms in  $\mathrm{Vect}_{\mathbb{C}}$  are represented as an  $n \times n$  matrix; the corresponding morphisms in  $\mathrm{Vect}_{\mathbb{R}}$  are represented as an  $2n \times 2n$  matrix. For example,

$$
\left( \begin{array}{c c} \sqrt {- 1} & 0 \\ 0 & 1 0 \end{array} \right) \left( \begin{array}{c} x + y i \\ u + v i \end{array} \right)
$$

is rewritten as

$$
\left( \begin{array}{c c c} 0 & - 1 & \\ 1 & 0 & \\ & & 1 0 \quad 0 \\ & & 0 \quad 1 0 \end{array} \right) \left( \begin{array}{c} x \\ y \\ u \\ v \end{array} \right).
$$

The function of morphisms acts like this:

$$
\left( \begin{array}{c c} \sqrt {- 1} & 0 \\ 0 & 1 0 \end{array} \right) \mapsto \left( \begin{array}{c c c c} 0 & - 1 & & \\ 1 & 0 & & \\ & & 1 0 & 0 \\ & & 0 & 1 0 \end{array} \right),
$$

where empty slots should be filled with 0s.

We conclude that functor  $F$  is faithful but not full.

# 1.6 Natural Transformations

A natural transformation is, in a sense, a morphism between functors. We will give an exact meaning for this idea in the following chapter.

Definition 1.9 Let  $F$  and  $G$  are functors from category  $\mathcal{A}$  to  $\mathcal{B}$ . Let  $\{\alpha_A : FA \to GA\}_{A \in \mathrm{Obj}(\mathcal{A})}$  be a collection of morphisms in  $\mathcal{B}$  satisfying the following condition: for any morphism  $f : A_1 \to A_2$  in  $\mathcal{A}$ , the square to the right in Fig. 1.15 commutes. Namely,

$$
\alpha_ {A _ {2}} \circ F f = G f \circ \alpha_ {A _ {1}}.
$$

Then, we call the collection  $\{\alpha_A\}$  a natural transformation  $\alpha : F \to G$ .

![](images/094f5c3562f7409de54def9433a323e8c9a04bced3c127f5df4e8bc3d3f07585.jpg)  
Fig.1.15 Natural transformation  $\alpha : F \to G$

A functor is a kind of photograph of  $\mathcal{A}$  recorded on  $\mathcal{B}$ . When there are two functors, we have two photographs of  $\mathcal{A}$  on  $\mathcal{B}$ . So, we can compare the two images on the film or CCD (that is,  $\mathcal{B}$ ). This is just what natural transformations do.

A natural transformation  $\alpha : F \to G$  is often drawn as in the diagram:

![](images/4649bf7d32c482b50a1bdd45133a12d0781c76c44533f7170a73fcd7ec948ab6.jpg)

Example 1.31 Let us consider categories  $\mathcal{A}$  and  $\mathcal{B}$  in Fig. 1.16.  $\mathcal{A}$  has three objects and two morphisms  $p$  and  $q$  other than the identities.  $\mathcal{B}$  has nine objects and nine morphisms other than the identities and two diagonals obtained by transitivity, where we suppose the two squares are commutative.

$F, G, H$  are functors from  $\mathcal{A}$  to  $\mathcal{B}$ . There is a natural transformation  $\alpha: F \to G$ , but no natural transformation from  $F \to H$ . The reader may feel that natural transformations are kind of a homotopy. This idea is established in higher category theory, which is out of the scope of this exposition.

![](images/c0acd247a15bbfba0b25c987559f033a166567c0b5c63bf8fcb1cd1236c14bd4.jpg)  
Fig.1.16 Natural transformation and homotopy

Example 1.32 Let us consider a natural transformation concat from  $[ ] [ ]$  to  $[ ]$ . As a Haskell function, concat flattens a list of lists into a single list.

Prelude> concat [[1,2,3], [4,5], [6,7,8]]

[1,2,3,4,5,6,7,8]

Figure 1.17 illustrates the naturality of concat. The diagram in Fig. 1.17 can be tested as follows.

Listing 1.3 safehead.hs  
```txt
\*Main>:{   
\*Main| map length   
\*Main| (concat[[1,2,3]],[4,5],[],[[6],[7],[8]]])   
\*Main|:   
[3,2,0,1,1,1]   
\*Main>:{   
\*Main| concat((map.map)length   
\*Main| [[1,2,3]],[4,5],[],[[6],[7],[8]]])   
\*Main|:   
[3,2,0,1,1,1]
```

Example 1.33 We define a natural transformation safehead from the List functor to the Maybe functor as follows.

1 safehead::[]a->Maybe a  
2 safehead [] = Nothing  
3 safehead (x:xs) = Just x

![](images/066f4c7df587b224ec025afd06e728d3c97873c596ff2b7e209c8ad998c90647.jpg)  
Fig.1.17 Natural transformation concat

We can test like:

```txt
\*Main> safehead [] Nothing \*Main> safehead [1..10] Just 1
```

Figure 1.18 illustrates the naturality of safehead. We can test the naturality of safehead like this.

```txt
\*Main>:{   
\*Main| fmap length   
\*Main| (safehead ["hello", "Bon jour", "Guten Tag", "Buenos Diaz"]   
\*Main| :}   
Just 5   
\*Main>:{   
\*Main| safehead (map length   
\*Main| ["hello", "Bon jour", "Guten Tag", "Buenos Diaz"]   
\*Main| :}   
Just 5   
\*Main> fmap length (safehead []   
Nothing   
\*Main> safehead (map length[])   
Nothing
```

![](images/c028ca31207878b11c7a8a011fd6d655e2530533ed2a4c2c507d53e7c65b3cba.jpg)  
Fig.1.18 Natural transformation from List to Maybe

Definition 1.10 A functor that maps all the objects in the source to a designated object in the target, mapping all the morphisms to the identity, is called a constant functor.

At first sight, such a functor is too trivial a thing. However, we will see its great roles in various situations.

Example 1.34 The length function can be seen as a constant functor. We make it clear using a home-made length, mylength.

Listing 1.4 mylength.ms  
```haskell
import Data.FunctorConst
2
3 mylength :: [b] -> Const Int b
4 mylength [] = Const 0
5 mylength (x:xs) = Const (1 + getConst (mylength xs))
```

We can test mylength like  
```txt
\*Main> mylength [1..100]   
Const 100   
\*Main> mylength []   
Const O   
\*Main> :t mylength   
mylength :: [b] -> Const Int b
```

The Data.Functor Const module is defined like the following.

```txt
-- | The 'Const' functor.  
newtype Const a b = Const { getConst :: a }  
deriving ...  
...
```

In code listing 1.4, Const Int is a functor. It sends any Hask object, namely any type b, to Int. Note that Const itself is not a functor, but Const Int is. See Fig. 1.19 carefully. When we test Const Int f as in Fig. 1.20, we have to rewrite as fmap f in actual Haskell interaction. In Fig. 1.20, f stands for \xs -> xs ++ xs.

![](images/00c3662570ed474afecdf620b1ea79e3f85af414904d63a8d9f455dbf55bb45f.jpg)  
Fig.1.19 Natural transformation from List to Const Int

![](images/abd076b173d59cdcee24a8100c6cecc30969380b41fe55da76c8481eb14c0e43.jpg)  
Fig.1.20 Tests for const

```txt
\*Main>:{
\*Main| mylength . map (\xs -> xs ++ xs) $
\*Main| ["hello", "Bon jour", "Guten Tag", "Buenos Diaz"]
\*Main| :
Const 4
\*Main>:{
\*Main| fmap (\xs -> xs ++ xs) . mylength $
\*Main| ["hello", "Bon jour", "Guten Tag", "Buenos Diaz"]
\*Main| :
Const 4
```

Given functors  $\alpha : F \to G$  and  $\beta : G \to H$ , we can compose these functors to obtain a functor  $\gamma : F \to H$ . Let us define componentwise as follows.

$$
\gamma_ {A} = \beta_ {A} \circ \alpha_ {A}
$$

We often describe this composition with a diagram

![](images/b5637b5d88be2af723d055600db7d6ea1ce8354f807fd596b39f53c8067dd6fb.jpg)

We say  $\gamma$  is a vertical composition of  $\alpha$  and  $\beta$ . At this point, however, it is not obvious that  $\gamma$  defined componentwise as above is really a functor. To see that this is the case, we only have to check if the outer square in the following diagram commutes for arbitrary  $f: A_1 \to A_2$ .

![](images/c527d7e12f42caeae8f1a9a4fcecf398ba5cc415551678832a9b4a88c54a43e7.jpg)

The two small rectangles commute since  $F$  and  $G$  are functors. Therefore, the outer square commutes. So much for the proof, but if you want the other way of presentation, the author suggests that you elaborate on a rewriting sequence. The goal is

$$
H f \circ \beta_ {A _ {1}} \circ \alpha_ {A _ {1}} = \beta_ {A _ {2}} \circ \alpha_ {A _ {2}} \circ F f
$$

Let us begin with LHS:

$$
\begin{array}{l} H f \circ \beta_ {A _ {1}} \circ \alpha_ {A _ {1}} \\ = \beta_ {A _ {2}} \circ G f \circ \alpha_ {A _ {1}} (l o w e r s q u a r e) \\ = \beta_ {A _ {2}} \circ \alpha_ {A _ {2}} \circ F f (u p p e r s q u a r e), \\ \end{array}
$$

thus we reached the goal.

Example 1.35 Let us try a vertical composition of natural transformations in Examples 1.32 and 1.33.

![](images/a2bbde49f309025d5345a5b6631b4d0f4eff50f9adf3c96d7a17fc0615160d8a.jpg)

![](images/05105f185f3d7438a53fe69122c90f09558ea89e87410da9b6739e054d6b1969.jpg)  
Fig.1.21 Vertical composition of concat and safehead

To test this composition, let us take Hask objects String and Int and morphism length. We want to check if the outer square in Fig. 1.21 commutes. We do it as follows.

```txt
*Main>:
*Main| safehead . concat . (map.map) length $
*Main| [["hello", "Bon jour"], ["Guten Tag"], ["abc", "def", "gh"]] *Main| :
Just 5
*Main> :
*Main| fmap length . safehead . concat $
*Main| [["hello", "Bon jour"], ["Guten Tag"], ["abc", "def", "gh"]} *Main| :
Just 5
*Main> safehead . concat . (map.map) length $
Nothing
*Main> fmap length . safehead . concat $
Nothing
```

Functors are often compared to containers for some values. Natural transformations map containers to containers without seeing what's inside these containers.

Example 1.36 Let us study a program that flattens binary trees to plain lists.

# Listing 1.5 Flatten.hs

```txt
1 module Flatten where  
2 import Tree  
3 import Data.Char
```

```haskell
4
5 flatten :: Tree a -> [a]
6 flatten Empty = []
7 -- flatten (Node x t1 t2) = x: (flatten t1 ++ flatten t2)
8 flatten (Node x t1 t2) = flatten t1 ++ [x] ++ flatten t2
9
10 toupper = maptoUpperCase
11
12 { - suggested tests; compare the results below
13 flatten . fmap toupper $ tree1
14 map toupper . flatten $ tree1
15 -}
```

This program imports a module 1.1. Let us give it a try.

```txt
*Flatten> tree1
    "seven"
    "five"
    "six"
"one"
    "four"
    "two"
    "three"
*Flatten> flatten tree1
["three", "two", "four", "one", "six", "five", "seven"]
```

The flatten function is a natural transformation from the Tree functor to the List functor. The flatten function transforms the structure of container organizations, in this example, binary trees to lists. It behaves regardless of the contents in the containers. See Fig. 1.22 to get a clear understanding. The numbers in the figure are intended for tracing the container organization transform. To prove that flatten is really a natural transformation, we have to show that the square on the right in Fig. 1.23 commutes. Let us try a test by giving a and b concrete types.

```txt
*Main> flatten . fmap toupper $ tree1
[["ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX", "SEVEN"]
*Main> map toupper . flatten $ tree1
[["ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX", "SEVEN"]
```

So much for the test for the following.

```txt
flatten . fmap toupper = map toupper . flatten
```

![](images/94ec75bba83e37f535e2ddb88b12c17c3ccdeeae82d99feca01412decf1c7305.jpg)  
Fig.1.22 Natural transformation from Tree to List

![](images/76ba823be2ec0f816cf473fd90a77e106e65a5d7e16b329ca1d7a021bbfe4812.jpg)  
Fig.1.23 Naturality of flatten

# 1.7 Subcategories of Hask

Polymorphic functions in Haskell that require contexts have signatures like

somefunction :: Someclass a => T1 a -> T2 a.

If type variable a is assigned a concrete type, then it is considered as an object of Hask. The context Someclass a requires that type variable a only allows the assignment of concrete types of a certain class.

Defining a type class in Haskell amounts to defining a subcategory of Haskell. Both String and Int can be considered as objects in subcategory 0rd. Function string2int in Example 1.1 is surely a morphism in Haskell, but not a morphism in 0rd.

Example 1.37 The sort function is a natural transformation from the List functor restricted to category Ord. The objects of Ord are Haskell types that belong to the type class Ord. The morphisms of Ord are functions that preserve order. If we can formulate a subcategory in Hask in this way, Ord is a faithful but not full subcategory of Hask.

Let us take an example of insertion sort.

Listing 1.6 sort.ps  
```haskell
1 import Tree  
2 import Flatten  
3  
4 iSort :: Ord a => [a] -> [a]  
5 iSort xs =  
6 foldr ins [] xs  
7 where  
8 ins x [] = [x]  
9 ins x (y:ys)  
10 | x <= y = x:y:ys  
11 | otherwise = y:ins x ys  
12  
13 list2tree :: Ord a => [a] -> Tree a  
14 list2tree xs =  
15 foldl sni Empty xs  
16 where  
17 sni = flip ins  
18 ins x Empty = Node x Empty Empty  
19 ins x (Node y t1 t2)  
20 | x <= y = Node y (ins x t1) t2  
21 | otherwise = Node y t1 (ins x t2)  
22  
23 iSort2 :: Ord a => [a] -> [a]  
24 iSort2 = flatten . list2tree
```

Notice that iSort and list2tree have local functions ins with the same name, but they are completely different.

Look carefully at Fig. 1.24. iSort is a natural transformation from a functor  $\mathrm{Ord} \to \mathrm{Hask}$  to itself.

![](images/2fe998e1faa40ad67c9eddd5195a61f402c748dcbd1fb7614faf9e189579f986.jpg)

Naturality can be tested as follows.

```txt
*Main> map (\x -> x*2) . iSort $ [1,5,3,4,2] [2,4,6,8,10] *Main> iSort . map (\x -> x*2) $ [1,5,3,4,2] [2,4,6,8,10]
```

![](images/b0a20139f4ca68b7100dd577b6484cf48c71a5095a0f2be8a1415ac677381aee.jpg)  
Fig.1.24 Natural transformation iSort

We can bring any monotone functions in place of  $\backslash x \dashrightarrow x * 2$ .

Function list2tree is a natural transformation from a functor [] to Tree. See Fig. 1.25.

![](images/cf37f2d0819c61d9c33a537b7a5d97f1dd072610b21ebf84bb02be95ec32062a.jpg)

Naturality of list2tree can be tested in the same way.

Alternative version iSort2 is a vertical composition of list2tree and flatten.

![](images/a423313b95b94199b07d03be78f780d5dd8b3c4c8ec4ddba68caee27879eb051.jpg)  
Fig.1.25 Natural transformation list2tree

We can test this mapping monotone functions in the same way.

![](images/16b0f8a26bbf2337f1cb959b429ed121a4903bdecb5482d4d0b230532a88c724.jpg)

# References

1. Mac Lane S (1998) Categories for the working mathematician, Graduate texts in mathematics, vol 5, 2nd edn. Springer  
2. Haskell WH https://wiki.haskell.org/Hask

# Equivalence of Categories

2

We introduce the concept of a functor category to better understand natural transformations. Then we study category equivalence. Most of us notice that intrinsic linear algebra, namely linear algebra independent of basis, and matrix linear algebra are essentially the same. Both can be formulated as a category of finite-dimensional linear spaces and linear transformations over a field such as  $\mathbb{R}$ ,  $\mathbb{C}$ , and other variety of fields. Intrinsic linear algebras are far wider than matrix linear algebras. These two categories are clearly not isomorphic, yet we have a feeling that they are essentially the same. The concept of category equivalence is invented to tackle this dilemma.

# 2.1 Functor Category

We fix a small category  $\mathcal{A}$  and locally small category  $\mathcal{B}$ . Let  $[\mathcal{A},\mathcal{B}]$  be a category with:

- the set of objects consisting of all the functors from  $\mathcal{A}$  to  $\mathcal{B}$  and  
- the set of morphisms between two functors  $F: \mathcal{A} \to \mathcal{B}$  and  $G: \mathcal{A} \to \mathcal{B}$  consisting of all the natural transformations  $F \to G$ .

This category is called a functor category from  $\mathcal{A}$  to  $\mathcal{B}$ .

Morphisms in a functor category, namely natural transformations, are composed componentwise, therefore associativity is automatic. The identity for a functor  $F$  is the identity natural transformation  $1_F: F \to F$ , where  $(1_F)_A: F(A) \to F(A) = 1_{F(A)}$ .

Remark 2.1 Category  $\mathcal{A}$  is assumed to be small, and category  $\mathcal{B}$  locally small, so that functor category  $[\mathcal{A},\mathcal{B}]$  stays locally small.

Example 2.1 What we have seen in Example 1.32 can be summarized as follows. Both List List and List are objects of category [Hask, Hask]. concat is a morphism

$$
\operatorname {c o n c a t} \in [ \operatorname {H a s k}, \operatorname {H a s k} ] (\operatorname {L i s t} ^ {2}, \operatorname {L i s t}).
$$

What we have seen in Example 1.33 can be summarized as follows. List and Maybe are objects of category [Hask, Hask]. safehead is a morphism

$$
\text {s a f e h e a d} \in [ \text {H a s k}, \text {H a s k} ] (\text {L i s t}, \text {M a y b e}).
$$

What we have seen in Example 1.36 can be summarized as follows. Tree and List are objects of category [Hask, Hask]. flatten is a morphism

$$
f l a t t e n \in [ H a s k, H a s k ] (T r e e, L i s t).
$$

Definition 2.1 An isomorphism in a functor category is called a natural isomorphism.

Example 2.2 The mirror function is a natural isomorphism from Tree to Tree.

Listing 2.1 mirror.ms  
```haskell
import Tree
2
3 mirror :: Tree a -> Tree a
4 mirror Empty = Empty
5 mirror (Node x t1 t2) = Node x (mirror t2) (mirror t1)
```

If we run mirror as in Fig. 2.1, we can see mirror is an inverse to itself. We should check if the following two expressions evaluate the same result.

```txt
mirror . fmap string2int  $tree1fmap string2int. mirror$  tree1
```

![](images/3927dc883acef1a1916b561fc7de33df303bc361b1280964e8bc222eb5d3859a.jpg)  
Fig.2.1 Natural isomorphism from Tree to Tree

Let us draw a diagram that illustrates what's going on. s2i is short for string2int.

![](images/5317cc01f307020d83699f61b8919038ecf2f9a7fbd06ea1aec48862527e38af.jpg)

The square commutes, which means the naturality of mirror.

Example 2.3 We will implement a natural isomorphism from Maybe to Either(). Functor Either() is obtained by partially applying the unit type () to Either, which is in fact a functor with two arguments.

Listing 2.2 maybeEither.hs  
```haskell
1 alpha :: Maybe a -> Either () a
2 alpha Nothing = Left()
3 alpha (Just x) = Right x
4
5 beta :: Either () a -> Maybe a
6 beta (Left ()) = Nothing
7 beta (Right x) = Just x
8
9 {- suggested tests
10 beta . alpha $ Just 100
11 beta . alpha $ Nothing
12 alpha . beta $ Right 100
13 alpha . beta $ Left ()
14 }
```

Performing tests suggested in lines 10-13 are left to the reader.

Lemma 2.1 Natural transformation

![](images/27171844dc9a1397f8b17c42525dc3e9c542fd1edaaac6f6ec506f3eb3eee39d.jpg)

is a natural isomorphism if and only if  $\alpha_{A}: F(A) \to G(A)$  is an isomorphism in  $\mathcal{B}$  for all objects  $A \in \mathrm{Obj}(\mathcal{A})$ .

Remark 2.2 This lemma claims that natural isomorphism is equivalent to componentwise isomorphism. At first sight, it seems trivial, but proving it is not so trivial.

By definition,  $\alpha : F \to G$  is a natural isomorphism if and only if there exists a natural transformation  $\beta : G \to F$  such that

![](images/a5f1a03c6c5b4f42292afd945e855c5e77bf43e023566ead2f44647870d40ea4.jpg)

and

![](images/82e60f039e9b592867f2af603e70e4e2a81e64bfdc46a519b5c9dc809800c674.jpg)

Even when  $\alpha_{A}: F(A) \to G(A)$  has an inverse  $\beta_{A}: G(A) \to F(A)$  as morphisms in  $\operatorname{Mor}(\mathcal{B})$  for all  $A \in \mathrm{Obj}(\mathcal{A})$ , we still do not know if the collection  $\{\beta_{A}\}$  really forms a natural transformation.

# Proof (Lemma 2.1)

Assume  $\alpha : F \to G$  is a natural isomorphism. We will show that  $\alpha_{A}$  is an isomorphism in  $\mathcal{B}$  for all  $A \in \mathrm{Obj}(\mathcal{A})$ . Since  $\beta \circ \alpha = 1_{F}$ , we have  $\beta_{A} \circ \alpha_{A} = 1_{F(A)}$  for all  $A \in \mathrm{Obj}(\mathcal{A})$ . Also, since  $\alpha \circ \beta = 1_{G}$ , we have  $\alpha_{A} \circ \beta_{A} = 1_{G(A)}$  for all  $A \in \mathrm{Obj}(\mathcal{A})$ . Therefore, we have that  $\alpha_{A}$  is an isomorphism in  $\mathcal{B}$  for all  $A \in \mathrm{Obj}(\mathcal{A})$ .

Let us prove the other direction. Assume that a natural transformation  $\alpha : F \to G$  has componentwise inverses  $\beta_A : G(A) \to F(A)$ , namely

$$
\beta_ {A} \circ \alpha_ {A} = 1 _ {F (A)} \quad \text {a n d} \quad \alpha_ {A} \circ \beta_ {A} = 1 _ {G (A)}.
$$

We will show that collection  $\{\beta_A\}$  forms a natural transformation  $\beta : G \to F$  and that  $G \circ F = 1_F$  and  $F \circ G = 1_G$ . The goal is the naturality of  $\beta$ . Establishing naturality amounts to show the square in the following diagram commutes.

![](images/18f9771798821922f7b903af2892d5b1d5d87f7d61804665cba0463ac3082a3b.jpg)

We add information about  $\alpha$  to this diagram and get the following.

![](images/b9d808188de0b6a076f404fc86eb178adc5e478ded1e08e4240570283254da9f.jpg)

The assumption is the commutativity of the inner square. The assumption also says that anti-parallel pairs of morphisms are isomorphisms. The commutativity of the inner square is

$$
\alpha_ {A _ {2}} \circ F f = G f \circ \alpha_ {A _ {1}}.
$$

We compose  $\beta_{A_1}$  from right and  $\beta_{A_2}$  from left

$$
\beta_ {A _ {2}} \circ \alpha_ {A _ {2}} \circ F f \circ \beta_ {A _ {1}} = \beta_ {A _ {2}} \circ G f \circ \alpha_ {A _ {1}} \circ \beta_ {A _ {1}}.
$$

Cancelling the inverses, we have

$$
F f \circ \beta_ {A _ {1}} = \beta_ {A _ {2}} \circ G f.
$$

Now, we see that the outer square commutes. Thus, we established that  $\beta$  is a natural transformation.

# 2.2 Equivalence of Categories

Given a pair of functors  $F: \mathcal{A} \to \mathcal{A}'$  and  $G: \mathcal{A}' \to \mathcal{A}$  with  $GF = \operatorname{Id}_{\mathcal{A}}$  and  $FG = \operatorname{Id}_{\mathcal{A}'}$ , we say that  $\mathcal{A}$  and  $\mathcal{A}'$  are isomorphic categories. This is just what we can think of next to equality. But, unfortunately this idea yields little insight for a deeper understanding of the relations among categories. Instead, we will introduce the concept of equivalence of categories that is coarser than isomorphism. We will see that equivalence of categories is closely related to the concept of adjoint in Chap. 5.

Definition 2.2 We say categories  $\mathcal{A}$  and  $\mathcal{A}'$  are equivalent if there are functors  $F: \mathcal{A} \to \mathcal{A}'$  and  $G: \mathcal{A}' \to \mathcal{A}$ , and natural isomorphisms  $\eta: \operatorname{Id}_{\mathcal{A}} \to GF$  and  $\varepsilon: FG \to \operatorname{Id}_{\mathcal{A}'}$ .

Is so defined equivalence of categories really an equivalence relation among categories? At first sight, this relation looks non-symmetric, which is fatal to be equivalence. Further, we doubt at present that the relation is reflexive and transitive. We will show that the equivalence of categories is an equivalence relation later.

Let us first take an example of linear algebra.

Example 2.4 Let  $\operatorname{Vect}_{\mathbb{C}}$  be a category of finite-dimensional complex vector spaces. Let  $\mathbb{C}^n$  be an  $n$ -dimensional complex vector space consisting of column vectors. Let  $\operatorname{Col}_{\mathbb{C}}$  be a category with the set of objects  $\{\mathbb{C}^n\}_{n \in \mathbb{N}}$  and the set of morphisms consisting of all  $m \times n$ -complex matrices, where morphisms from  $\mathbb{C}^n \to \mathbb{C}^m$  are matrix multiplication from the left. Note that  $\mathbb{N}$  is the set of natural numbers, namely  $\{n \in \mathbb{Z} \mid n \geq 0\}$ .

We define a functor  $F:\mathrm{Vect}_{\mathbb{C}}\to \mathrm{Col}_{\mathbb{C}}$  as follows:

- We first choose a particular basis for each object  $V$  in  $\mathrm{Vect}_{\mathbb{C}}$ . If you are familiar with the axiom of choice, you may wonder if this kind of activities are possible. Yes, we adopt the axiom.  
-  $FV$  consists of column vectors that are obtained from vectors in  $V$  by taking components with respect to the designated basis of  $V$ .  
- Let  $T: V_1 \to V_2$  be a complex linear transformation.  $FT: \mathbb{C}^n \to \mathbb{C}^m$  is a  $m \times n$ -complex matrix that represents  $T$  with respect to the designated bases.

$F$  introduced in this way is clearly a functor. We skip the proof of functoriality.

Next, we consider an obvious embedding functor  $G: \mathrm{Col}_{\mathbb{C}} \to \mathrm{Vect}_{\mathbb{C}}$  and proceed to the construction of natural transformations. The composition  $G \circ F: \mathrm{Vect}_{\mathbb{C}} \to \mathrm{Vect}_{\mathbb{C}}$  is a full and faithful functor. The function on objects is not injective, but the function on morphisms is bijective for all pairs of objects in  $\mathrm{Vect}_{\mathbb{C}}$ . We construct a natural transformation  $\eta: G \circ F \to \mathrm{Id}_{\mathrm{Vect}_{\mathbb{C}}}$ , and show  $\eta$  is a natural isomorphism. We have to show that the square commutes in the following diagram.

$$
\begin{array}{c c} V _ {1} & \quad \operatorname {I d} (V _ {1}) \xrightarrow {\eta_ {V _ {1}}} G (F (V _ {1})) \\ f \Bigg \downarrow & \quad f \Bigg \downarrow \qquad \qquad \qquad \Bigg \downarrow G (F (f)) \\ V _ {1} & \quad \operatorname {I d} (V _ {2}) \xrightarrow {\eta_ {V _ {2}}} G (F (V _ {2})) \end{array}
$$

Functor  $G$  is just an embedding and does nothing significant on objects and morphisms. Therefore, commutativity depends solely on  $F$ , which is a functor that promises commutativity. Since  $\eta_{V_1}$  and  $\eta_{V_2}$  are isomorphisms,  $\eta : \mathrm{Id}_{\mathrm{Vect}_{\mathbb{C}}} \to G \circ F$  is a natural isomorphism.

Another direction is quite easy. Since  $F \circ G : \mathrm{Col}_{\mathbb{C}} \to \mathrm{Col}_{\mathbb{C}}$  is already an identity functor,  $\varepsilon : F \circ G \to \operatorname{Id}_{\mathrm{Col}_{\mathbb{C}}}$  is already there.

We got an example in which a large category is equivalent to a small category.

Theorem 2.1 The equivalence of categories is an equivalence relation.

Proof (1) We first show reflexivity:  $\mathcal{A} \simeq \mathcal{A}$ .

We set  $F = G = \operatorname{Id}_{\mathcal{A}}: \mathcal{A} \to \mathcal{A}$ , and  $\eta = GF = \varepsilon = FG: \operatorname{Id}_{\mathcal{A}} \to \operatorname{Id}_{\mathcal{A}}$ .

(2) We show symmetry:  $\mathcal{A} \simeq \mathcal{A}' \Rightarrow \mathcal{A}' \simeq \mathcal{A}$ .

Let  $\eta : \operatorname{Id}_{\mathcal{A}} \to GF$  and  $\varepsilon : FG \to \operatorname{Id}_{\mathcal{A}'}$  be natural isomorphisms between two functors  $F : \mathcal{A} \to \mathcal{A}'$  and  $G : \mathcal{A}' \to \mathcal{A}$ .

If we set  $F' = G$ ,  $G' = F$ ,  $\eta' = \varepsilon$ , and  $\varepsilon' = \eta$ , we have equivalence of categories  $\mathcal{A}' \simeq \mathcal{A}$  with functors  $F': \mathcal{A}' \to \mathcal{A}$  and  $G': \mathcal{A} \to \mathcal{A}'$ , and with natural isomorphisms  $\eta': \operatorname{Id}_{\mathcal{A}'} \to G'F'$  and  $\varepsilon': F'G' \to \operatorname{Id}_{\mathcal{A}}$ .

(3) We show transitivity:  $\mathcal{A} \simeq \mathcal{A}'$  and  $\mathcal{A}' \simeq \mathcal{A}'' \Rightarrow \mathcal{A} \simeq \mathcal{A}''$ .

Since  $\mathcal{A} \simeq \mathcal{A}'$ , we have natural isomorphisms  $\eta$  and  $\varepsilon$ :

$$
\xrightarrow {\mathcal {A} \xrightarrow {F} \mathcal {A} ^ {\prime} \xrightarrow {G} \mathcal {A}} \quad \xrightarrow [ \text {I d} _ {\mathcal {A}} ]{\text {I d} _ {\mathcal {A} ^ {\prime}}} \quad \mathcal {A} ^ {\prime} \xrightarrow [ G ]{\text {I d} _ {\varepsilon}} \mathcal {A} \xrightarrow [ F ]{\text {I d} _ {\mathcal {A} ^ {\prime}}}. \tag {2.1}
$$

Since  $\mathcal{A}' \simeq \mathcal{A}''$ , we have natural isomorphisms  $\eta'$  and  $\varepsilon'$ :

$$
\begin{array}{c} \mathcal {A} ^ {\prime} \xrightarrow {F ^ {\prime}} \mathcal {A} ^ {\prime \prime} \xrightarrow [ \Downarrow \eta^ {\prime} ]{G ^ {\prime}} \mathcal {A} ^ {\prime} \\ \mathrm {I d} _ {\mathcal {A} ^ {\prime}} \end{array} \quad \begin{array}{c} \mathrm {I d} _ {\mathcal {A} ^ {\prime \prime}} \\ \mathcal {A} ^ {\prime \prime} \xrightarrow [ G ^ {\prime} ]{\Downarrow_ {\varepsilon^ {\prime}}} \mathcal {A} \xrightarrow [ F ^ {\prime} ]{F ^ {\prime}} \mathcal {A} ^ {\prime \prime}. \end{array} \tag {2.2}
$$

All we have to do is to construct two natural isomorphisms  $\eta''$  and  $\varepsilon''$  out of diagrams (2.1) and (2.2).

$$
\begin{array}{c} \mathcal {A} \xrightarrow {F ^ {\prime} F} \mathcal {A} ^ {\prime \prime} \xrightarrow {G G ^ {\prime}} \mathcal {A} \\ \hline \mathrm {I d} _ {\mathcal {A}} \end{array} \qquad \begin{array}{c} \mathcal {A} ^ {\prime \prime} \xrightarrow {\mathrm {I d} _ {\mathcal {A} ^ {\prime \prime}}} \\ \hline \mathrm {G G} ^ {\prime} \xrightarrow {\mathrm {I d} _ {\varepsilon^ {\prime \prime}}} \mathcal {A} \xrightarrow {F ^ {\prime} F} \mathcal {A} ^ {\prime \prime} \end{array}
$$

To construct  $\eta''$ , we place vertically two diagrams for  $\eta$  and  $\eta'$  in (2.1) and  $\eta$  and (2.2).

![](images/14b243778a7f884ebb641f4143812e03146263c6ee8f783fe9cd5834d567a1d1.jpg)

Note that we can rewrite  $\eta : \mathrm{Id}_{\mathcal{A}} \to GF$  as

$$
\eta : \operatorname {I d} _ {\mathcal {A}} \to G \operatorname {I d} _ {\mathcal {A} ^ {\prime}} F.
$$

Horizontally composing  $\eta': \operatorname{Id}_{\mathcal{A}'} \to G'F'$  with  $G$  and  $F$ , we have a natural isomorphism

$$
G \eta^ {\prime} F: G \operatorname {I d} _ {\mathscr {A} ^ {\prime}} F \to G G ^ {\prime} F ^ {\prime} F.
$$

Further composing vertically, we have

$$
G \eta^ {\prime} F \circ \eta : \operatorname {I d} _ {\mathscr {A}} \to G G ^ {\prime} F ^ {\prime} F.
$$

Thus, we can define a natural isomorphism

$$
\eta^ {\prime \prime} = G \eta^ {\prime} F \circ \eta .
$$

To construct  $\varepsilon^{\prime \prime}$ , we place vertically two diagrams for  $\varepsilon$  and  $\varepsilon^{\prime}$  in (2.1) and  $\eta$  and (2.2).

![](images/f929d1944ae2bcdbc779aca06065f3d9a23bd530323c57b9ac634b96fcbb45a2.jpg)

Note that we can rewrite  $\varepsilon^{\prime}:F^{\prime}G^{\prime}\to \mathrm{Id}_{\mathcal{A}^{\prime \prime}}$  as

$$
\varepsilon^ {\prime}: F ^ {\prime} \operatorname {I d} _ {\mathscr {A} ^ {\prime \prime}} G ^ {\prime} \rightarrow \operatorname {I d} _ {\mathscr {A} ^ {\prime \prime}}.
$$

Horizontally composing  $\varepsilon: FG \to \operatorname{Id}_{\mathcal{A}'}$  with  $G'$  and  $F'$ , we have a natural isomorphism

$$
F ^ {\prime} \varepsilon G ^ {\prime}: F ^ {\prime} F G G ^ {\prime} \rightarrow F ^ {\prime} \operatorname {I d} _ {\mathscr {A} ^ {\prime}} G ^ {\prime}.
$$

Vertically composing, we have

$$
\varepsilon^ {\prime} \circ F ^ {\prime} \varepsilon G ^ {\prime}: F ^ {\prime} F G G ^ {\prime} \rightarrow \operatorname {I d} _ {\mathcal {A} ^ {\prime \prime}}.
$$

$$
\varepsilon^ {\prime \prime} = \varepsilon^ {\prime} \circ F ^ {\prime} \varepsilon G ^ {\prime}
$$

We have shown reflexivity, symmetry, and transitivity.

![](images/7b2f8d037b0facee1c3bf453cf103c139fa6309fab79a76453c10ef4f68ef34e.jpg)

Equivalence of categories can be put in other forms with which we can decide equivalence with information about either  $F$  or  $G$ , not both.

Definition 2.3 A functor  $F: \mathcal{A} \to \mathcal{B}$  is said to be essentially surjective on objects, if for all  $B \in \mathrm{Obj}(\mathcal{B})$  there exist  $A \in \mathrm{Obj}(\mathcal{A})$  such that  $F(A) \cong B$ .

If the function on objects is surjective, the functor, of course, is automatically essentially surjective on objects. There are cases in which the function on objects is not surjective but essentially surjective on objects. See the diagram below. An object  $B$  is out of the image of  $F$  but it has an isomorphism to  $B_{\infty}$  that belongs to the image of  $F$ .

![](images/93ac0087738180e23ff13de2922a5c14e5d3dc92f106782aaa372eb72a5b9b8a.jpg)

Full and faithful functors have important properties concerning isomorphisms.

Lemma 2.2 Let  $F:\mathcal{A}\to \mathcal{B}$  be a full and faithful functor. For any pair  $A,A^{\prime}\in$ $\mathrm{Obj}(\mathcal{A})$  , we have the following:

(a) A morphism  $f: A \to A'$  is isomorphic if and only if  $Ff: FA \to FA'$  is isomorphic.  
(b) For all isomorphisms  $g: FA \to FA'$ , there exists a unique isomorphism  $f: A \to A'$  with  $Ff = g$ .  
(c)  $A$  and  $A^{\prime}$  are isomorphic if and only if  $FA$  and  $FA^{\prime}$  are isomorphic.

Proof Let us show (a). Suppose  $f$  is an isomorphism. Then, there is a morphism  $f': A' \to A$  such that  $f' \circ f = 1_A$  and  $f \circ f' = 1_{A'}$ . Since  $F$  is a functor, it maps identities to identities. Function on morphisms maps like this:

$$
\begin{array}{c} \mathcal {A} \longrightarrow \mathcal {B} \\ ^ {\prime} \circ f = 1 _ {A} \longmapsto F f ^ {\prime} \circ F f = 1 _ {F A} \\ \circ f ^ {\prime} = 1 _ {A ^ {\prime}} \longmapsto F f \circ F f ^ {\prime} = 1 _ {F A ^ {\prime}} \end{array}
$$

We see that  $Ff$  is an isomorphism.

Conversely, suppose  $Ff$  is an isomorphism. There exists a morphism  $g:FA^{\prime}\to FA$  such that  $g\circ Ff = 1_{FA}$  and  $Ff\circ g = 1_{FA^{\prime}}$ . Since  $F$  is full, there exists a morphism  $f^{\prime}:A^{\prime}\to A$  such that  $Ff^{\prime} = g$ . We see that  $F$  maps morphisms as follows:

$$
\begin{array}{c} \mathcal {A} \longrightarrow \mathcal {B} \\ f ^ {\prime} \circ f \longmapsto F f ^ {\prime} \circ F f \\ 1 _ {A} \longmapsto_ {\text {a x i o m}} 1 _ {F A} \\ f \circ f ^ {\prime} \longmapsto F f \circ F f ^ {\prime} \\ 1 _ {A ^ {\prime}} \longmapsto_ {\text {a x i o m}} 1 _ {F A ^ {\prime}}. \end{array}
$$

Since  $F$  is faithful, we have  $f' \circ f = 1_A$  and  $f \circ f' = 1_{A'}$ . Thus,  $f$  is an isomorphism. Let us show (b).

Assume that  $g:FA\to FA'$  is an isomorphism. There exists a morphism  $g^{\prime}: FA^{\prime}\rightarrow FA$  such that  $g^{\prime}\circ g = 1_{FA}$  and  $g\circ g^{\prime} = 1_{FA^{\prime}}$ . Since  $F$  is full and faithful,

there exists unique morphisms such that  $g = Ff$  and  $g' = Ff'$ .  $F$  maps morphisms as follows:

![](images/e5f19b1f0b8970157ae858fee6e4bf2cc755f172e1730a7e1924d6ab55187460.jpg)

The two triangles correspond mirror symmetrically via  $F$ . By assumption, the right triangle commutes. We do not know at present about the left one. We can summarize the situation like this.

![](images/2bd54e448d9a614f116a31be19eddebeef4c65155f54a30de80dcdd52ccaf2f4.jpg)

Since  $F$  is faithful, we have  $f' \circ f = 1_A$ . This means the left triangle also commutes. Likewise, we can show that  $f \circ f' = 1_{A'}$ . To sum up, there exists a unique isomorphism  $f: A \to A'$  such that  $g = Ff$ .

Let us show (c).

Suppose that  $A \simeq A'$ , namely that there exists an isomorphism  $f: A \to A'$ . By (a), we have that  $Ff: FA \to FA'$  is an isomorphism. Therefore,  $FA \simeq FA'$ .

Conversely suppose that  $FA \simeq FA'$ , namely that there exists an isomorphism  $g: FA \to FA'$ . By (b), we see that there exists an isomorphism  $f: A \to A'$ , and thus  $A \simeq A'$ .

Proposition 2.1 For any functor  $F: \mathcal{A} \to \mathcal{B}$ , the following two conditions are equivalent.

1. There exists a functor  $G: \mathcal{B} \to \mathcal{A}$  such that the pair  $(F, G)$  gives an equivalence of categories  $\mathcal{A} \simeq \mathcal{B}$ .  
2.  $F$  is full and faithful and essentially surjective on objects.

Remark 2.3 What is great about the second statement above is that it is described by information of  $F$  only. It is often the case that the construction of functor  $G$  is cumbersome.

Note that the roles of  $F$  and  $G$  are exchangeable, therefore both of them are full and faithful and essentially surjective on objects.

Proof (1) Let us show  $1 \Rightarrow 2$ .

Natural isomorphisms  $\eta : \operatorname{Id}_{\mathcal{A}} \to GF$  and  $\varepsilon : FG \to \operatorname{Id}_{\mathcal{B}}$  are available.

- We first prove that  $F$  is essentially surjective on objects.

For any  $B \in \mathrm{Obj}(\mathcal{B})$ , we have isomorphism  $\varepsilon_B: FGB \to B$ . This shows that  $B$  is isomorphic to the image of  $G(B)$  by  $F$ , meaning that  $F$  is essentially surjective on objects.

- Next we prove that  $F$  is faithful.

The naturality of  $\eta$  claims the following diagram commutes:

![](images/af3fa5d305eeef2c4c3495696080d5bd32a3df9f3322126e66a219be2d701a2e.jpg)

Further, since  $\eta$  is an isomorphism, inverses  $\eta_A^{-1}$  and  $\eta_{A'}^{-1}$  are available. The naturality equation is written as

$$
\eta_ {A ^ {\prime}} \circ f = G F f \circ \eta_ {A}.
$$

If we apply  $\eta_{A'}^{-1} \circ -$ , from the left to both sides, we get

$$
f = \eta_ {A ^ {\prime}} ^ {- 1} \circ G F f \circ \eta_ {A}. \tag {2.3}
$$

Faithfulness means that

$$
F f _ {1} = F f _ {2} \Rightarrow f _ {1} = f _ {2}
$$

for any pair of morphisms  $f_{1}$  and  $f_{2}$  in  $\mathcal{A}$ , which is obvious by Eq. (2.3).

- Before we proceed to the fullness of  $F$ , let us examine the faithfulness of  $G$ .

The naturality of  $\varepsilon$  claims the following diagram commutes:

![](images/9d9337b8a7313a2821b1727635e64b40f8868991ad52c9b31c6c87eeab34e0b6.jpg)

Further, since  $\varepsilon$  is an isomorphism, inverses  $\varepsilon_B^{-1}$  and  $\varepsilon_{B^{\prime}}^{-1}$  are available. The naturality equation is written as

$$
g \circ \varepsilon_ {B} = \varepsilon_ {B ^ {\prime}} \circ F G g.
$$

If we apply  $-\circ \varepsilon_{B}^{-1}$  from the right to both sides, we get

$$
g = \varepsilon_ {B ^ {\prime}} \circ F G g \circ \varepsilon_ {B} ^ {- 1}. \tag {2.4}
$$

Faithfulness means that

$$
G g _ {1} = G g _ {2} \Rightarrow g _ {1} = g _ {2}
$$

for all pairs of morphisms  $g_{1}$  and  $g_{2}$  in  $\mathcal{B}$ , which is obvious by Eq. (2.4).

- We prove that  $F$  is full.

We have to show that

$$
\mathcal {A} (A, A ^ {\prime}) \rightarrow \mathcal {B} (F A, F A ^ {\prime})
$$

is surjective for all pairs of  $A, A' \in \mathrm{Obj}(\mathcal{A})$ . We show that there exists a morphism  $f: A \to A'$  such that  $h = Ff$  for all morphisms  $h: FA \to FA'$ . Since  $\eta_{A'}$  is invertible in the following diagram

![](images/d3c69aeb1a9984308fefd546fe8ddb7d865c8ab91e35591dd97fb1dab7bc8205.jpg)

we may define morphism  $f: A \to A'$  by

$$
f = \eta_ {A ^ {\prime}} ^ {- 1} \circ G h \circ \eta_ {A}.
$$

Recalling that  $\eta : \mathrm{Id}_{\mathcal{A}} \to GF$  is a natural transformation, we draw two commuting squares as follows.

![](images/b5d6d8bf3c92012a93f00c1bc06328b565cf8b36440c511d4c4c48610a2dc71a.jpg)

Since underlined morphisms  $Gh$  and  $GFf$  both equal to

$$
\eta_ {A ^ {\prime}} \circ f \circ \eta_ {A} ^ {- 1},
$$

we have  $Gh = GFf$ . We have already shown that  $G$  is faithful, therefore  $h = Ff$ . This shows the fullness of  $F$ .

(2) Let us show  $2 \Rightarrow 1$ .

We will construct a functor  $G: \mathcal{B} \to \mathcal{A}$  and two natural isomorphisms  $\eta: \operatorname{Id}_{\mathcal{A}} \to GF$  and  $\varepsilon: FG \to \operatorname{Id}_{\mathcal{B}}$  out of a given functor  $F: \mathcal{A} \to \mathcal{B}$ .

Since  $F$  is essentially surjective on objects, for all  $B \in \mathrm{Obj}(\mathcal{B})$  we can find  $A \in \mathrm{Obj}(\mathcal{A})$  and a morphism  $\varepsilon_B: FA \to B$  as in

![](images/bae8c43e878c4a63411f94e71caa602858593dd452317c3aa9cd2d87eddf4adf.jpg)

Neither  $A$  nor  $\varepsilon_B$  is unique. We choose them arbitrarily and fix for each  $B$ . We define a function on objects  $G$  as  $A = GB$ . At this point, we do not know either if the collection  $\{\varepsilon_B\}_{B \in \mathrm{Obj}(\mathcal{B})}$  forms a natural isomorphism, or if  $G$  is a functor.

$$
\begin{array}{c} \mathcal {A} \xrightarrow {F} \mathcal {B} \\ A = G B \longmapsto F G B \\ \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \searrow \end{array}
$$

Now, we want to extend  $G$  to morphisms. Given a morphism  $g: B \to B'$ , we study a diagram

$$
\begin{array}{c} \mathcal {A} \xrightarrow {F} \mathcal {B} \\ G B \longmapsto F G B \xrightarrow {\varepsilon_ {B}} B \\ \exists G g \Bigg | _ {\vee} \Bigg | _ {\vee} \Bigg | _ {\vee} ^ {- 1} \circ g \circ \varepsilon_ {B} \Bigg | _ {\vee} ^ {- 1} \forall g \\ G B ^ {\prime} \longmapsto F G B ^ {\prime} \xrightarrow {\varepsilon_ {B ^ {\prime}}} B ^ {\prime}. \end{array}
$$

Since  $\varepsilon_{B'}$  is invertible,

$$
\varepsilon_ {B ^ {\prime}} ^ {- 1} \circ g \circ \varepsilon_ {B}: F G B \to F G B ^ {\prime}
$$

makes the right square commute. Since  $F$  is full and faithful, there is a unique morphism  $Gg$  that makes the left square commute. Thus, we obtain a function on morphisms.

- Let us show that  $G$  is a functor.

Given two morphisms  $g: B \to B'$  and  $g': B' \to B''$ , we must show

$$
G \left(g ^ {\prime} \circ g\right) = G g ^ {\prime} \circ G g. \tag {2.5}
$$

Let us consider the following diagram.

$$
\begin{array}{c} \mathcal {A} \xrightarrow {F} \mathcal {B} \\ G B \longmapsto F G B \xrightarrow {\varepsilon_ {B}} B \\ \left( \begin{array}{c c c} G g & \Bigg | & \Bigg | _ {\varepsilon_ {B ^ {\prime}} ^ {- 1} \circ g \circ \varepsilon_ {B}} \\ & & \Bigg | & \Bigg | _ {\Bigg |} \\ G (g ^ {\prime} \circ g) & \Bigg | & \Bigg | _ {\varepsilon_ {B ^ {\prime}} ^ {- 1} \circ g ^ {\prime} \circ \varepsilon_ {B ^ {\prime}}} \\ & & \Bigg | & \Bigg | _ {\Bigg |} \\ & & \Bigg | & \Bigg | _ {\Bigg |} \\ & G B ^ {\prime \prime} & \longmapsto F G B ^ {\prime \prime} \xrightarrow {\varepsilon_ {B ^ {\prime \prime}}} B ^ {\prime \prime} \end{array} \right) g ^ {\prime} \circ g \\ & \end{array}
$$

If we compose two morphisms in the center column, we obtain

$$
\varepsilon_ {B ^ {\prime \prime}} ^ {- 1} \circ g ^ {\prime} \circ g \circ \varepsilon_ {B} = \varepsilon_ {B ^ {\prime \prime}} ^ {- 1} \circ (g ^ {\prime} \circ g) \circ \varepsilon_ {B}.
$$

We now see that  $Gg' \circ Gg$  and  $G(g' \circ g)$  are mapped by  $F$  to the same morphism  $\varepsilon_{B''}^{-1} \circ g' \circ g \circ \varepsilon_B$ . For better illustration, we draw morphism mapping as follows.

$$
\begin{array}{l} \mathcal {A} (G B, G B ^ {\prime \prime}) \xrightarrow {F} \mathcal {B} (F G B, F G B ^ {\prime \prime}) \\ G g ^ {\prime} \circ G g \longmapsto \varepsilon_ {B ^ {\prime \prime}} ^ {- 1} \circ g ^ {\prime} \circ g \circ \varepsilon_ {B} \\ G \left(g ^ {\prime} \circ g\right) \longmapsto \varepsilon_ {B ^ {\prime \prime}} ^ {- 1} \circ \left(g ^ {\prime} \circ g\right) \circ \varepsilon_ {B} \\ \end{array}
$$

By assumption  $F$  is faithful, so the two morphisms on the left must coincide, which proves Eq. (2.5). Now,  $G$  is a functor.

- Let us show that  $\varepsilon$  is a natural transformation.

We know that  $\varepsilon_{B}$  is an isomorphism for each  $B\in \mathrm{Obj}(\mathcal{B})$  by definition. All we have to do is to show the collection  $\{\varepsilon_B\}_{B\in \mathrm{Obj}(\mathcal{B})}$  forms a natural transformation. Let us review the definition of  $G$ .

$$
\begin{array}{c} G B \longmapsto F G B \xrightarrow {\varepsilon_ {B}} B \\ G g \Bigg | _ {\downarrow} F G g \Bigg | _ {\downarrow} \bigcirc \Bigg | _ {\downarrow} g \\ G B ^ {\prime} \longmapsto F G B ^ {\prime} \xrightarrow {\varepsilon_ {B ^ {\prime}}} B ^ {\prime} \end{array}
$$

We constructed  $\varepsilon_{B'}^{-1} \circ g \circ \varepsilon_B$  in the place of  $FGg$  so that the right square commutes. Since  $F$  is full and faithful, we can equate  $FGg = \varepsilon_{B'}^{-1} \circ g \circ \varepsilon_B$ . We proved that  $G$  is a functor. The commutative square means that  $\varepsilon$  is a natural transformation.

- Let us construct a natural isomorphism  $\eta : \operatorname{Id}_{\mathcal{A}} \to GF$ .

Since  $\varepsilon_{FA}$  is an isomorphism, we have the inverse  $\varepsilon_{FA}^{-1}: FA \to FGFA$ . Since  $F$  is full and faithful, there exists a unique  $\eta_A$  in the diagram:

$$
\begin{array}{c} \mathcal {A} \xrightarrow {F} \mathcal {B} \\ A \vdash \longrightarrow F A \\ \exists ! \eta_ {A} \vdots \\ \Downarrow \\ G F A \longmapsto F G F A \end{array}
$$

$$
\begin{array}{c} F A \\ \Bigg {\uparrow} \\ F G F A \end{array}
$$

$\eta_{A}$  is an isomorphism by lemma 2.2.

Next, we show the naturality of  $\eta$ .

![](images/7c203ea7ac96f4a1d4ae6b7a80d4c500a34421fdd23f5971fa460f26e881130d.jpg)

![](images/2315af8548ff98dcdebf91ff1032cec107df0e21a4170b78cd07907c3e6cde37.jpg)

![](images/9a83ce7529443105349ad27ce254198b85d376c9b816b75b02c98186d5675c03.jpg)

The square on the right commutes for  $\varepsilon$  is a natural isomorphism. The function  $F$  on morphisms show

$$
\begin{array}{l} \mathcal {A} (A, G F A ^ {\prime}) \xrightarrow {F} \mathcal {B} (F A, F G F A ^ {\prime}) \\ G F f \circ \eta_ {A} \longmapsto F G F f \circ \varepsilon_ {F A} ^ {- 1} \\ \eta_ {A ^ {\prime}} \circ f \longmapsto \varepsilon_ {F A} ^ {- 1} \circ F f. \\ \end{array}
$$

By the faithfulness of  $F$ , we have

$$
G F f \circ \eta_ {A} = \eta_ {A ^ {\prime}} \circ f.
$$

Thus, we have that the square on the left commutes, which means that  $\eta$  is a natural isomorphism.

![](images/8ccefe1bedc7a96dc4d1221e3e067d4818f60cb6830f0d2c45d58045a723ace3.jpg)

# Universality and Limits

3

We will see universality and limits. We do not define the term universal property, but the whole discussion is about universality.

Emphasis is placed on the actual calculation of limit cones, and many examples of calculations with pencil and paper are given accompanied by sample code. In the colimit examples, we often calculate quotient structures, that is, division by equivalence relations, which requires iterative and recursive thinking. Sample code uses the fold function, which embodies a design pattern of functional programming. That gives a consistent style, but the algorithm is not so obvious at a glance. So, we include demonstrations of tracing recursive calls.

# 3.1 Initial and Terminal Objects

Definition 3.1 An initial object of  $\mathcal{A}$  is an object  $A$  such that for all  $X\in \mathrm{Obj}(\mathcal{A})$  there exists a unique morphism  $A\to X$

A terminal object of  $\mathcal{A}$  is an object  $A$  such that for all  $X \in \mathrm{Obj}(\mathcal{A})$  there exists a unique morphism  $X \to A$ .

Example 3.1 The empty set  $\varnothing$  is an initial object of Set. A singleton set, namely a set with only one element, is a terminal object of Set. In set theory, a function  $f:X\to Y$  is defined as a subset of  $X\times Y$ , a graph of  $f$ ,  $\{(x,f(x))\mid x\in X\}$ . See Fig. 3.1.

Not all subsets of  $X \times Y$  are functions (graphs of a function). A necessary and sufficient condition for a subset  $G \subset X \times Y$  to be a function (graph of a function) is

$$
\forall x. (x \in X \Rightarrow \exists ! y. y \in Y \text {a n d} (x, y) \in G).
$$

![](images/931d86a95121bb33f4dab1cb2f434cd5fd03717e24b2a8db15457777bda2c594.jpg)  
Fig.3.1 A function is a subset of  $X\times Y$

![](images/2ec73b672675a93ecc4b5207398945be1f8826b8c43343027d9e6b4b79c514e1.jpg)

$\exists !$  means there exists a unique so-and-so.

Think of a function  $f: \emptyset \to Y$ . We can identify  $f$  with a subset of  $\emptyset \times Y$ , which must be  $\emptyset$ . The empty set qualifies to be a graph of a function since  $p \Rightarrow q$  is true when  $p$  is false. In Set, there is a unique initial object  $\emptyset$  and infinitely many terminal objects.

Proposition 3.1 If  $A_{1}$  and  $A_{2}$  are two initial objects of  $\mathcal{A}$ , then they are isomorphic.

Proof Since  $A_{1}$  is initial, there exists a unique morphism  $f: A_{1} \to A_{2}$ . Since  $A_{2}$  is also initial, there exists a unique morphism  $g: A_{2} \to A_{1}$ . The composite  $g \circ f: A_{1} \to A_{1}$  is a morphism from  $A_{1}$  to  $A_{1}$ , which must be unique due to the initiality of  $A_{1}$ , therefore the composite equals to  $1_{A_{1}}$ . Likewise, we have  $f \circ g = 1_{A_{2}}$ . This completes the proof.

Proposition 3.2 If  $A_1$  and  $A_2$  are two terminal objects of  $\mathcal{A}$ , then they are isomorphic.

Proof Since  $A_{2}$  is terminal, there exists a unique morphism  $f: A_{1} \to A_{2}$ . Since  $A_{1}$  is also terminal, there exists a unique morphism  $g: A_{2} \to A_{1}$ . The composite  $g \circ f: A_{1} \to A_{1}$  is a morphism from  $A_{1}$  to  $A_{1}$ , which must be unique due to the terminality of  $A_{1}$ , therefore the composite equals to  $1_{A_{1}}$ . Likewise, we have  $f \circ g = 1_{A_{2}}$ . This completes the proof.

Example 3.2 Given a set  $X = \{1, 2, 3\}$ , its power set is:

$$
2 ^ {X} = \{\emptyset , \{1 \}, \{2 \}, \{3 \}, \{1, 2 \}, \{2, 3 \}, \{1, 3 \}, X \}.
$$

We define a category  $\mathcal{P}(X)$ , the category of power sets of  $X$ , as follows.

$\operatorname {Obj}(\mathcal{P}(X)) = 2^X$

- for any objects  $A$  and  $B$ , if  $A \subset B$  there exists a unique morphism from  $A$  to  $B$ . Otherwise, there is no morphism from  $A$  to  $B$ .

If we draw the set of generators omitting the identity morphisms, we have the following:

![](images/0bda0516f49e7fdce85ae4b3d51b69110d2a44b54441c40abd2444de887c13a9.jpg)

$\varnothing$  is a unique initial object, and  $X$  is a unique terminal object.

We can construct a faithful functor from  $\mathcal{P}(X)$  to Set as follows:

- function on objects is obvious.  
- function on morphisms maps  $f: A \to B$  to the inclusion map. For example, a morphism  $\{2, 3\} \to \{1, 2, 3\}$  of  $\mathcal{P}(X)$  is mapped as

$$
\begin{array}{l} f: \{2, 3 \} \to \{1, 2, 3 \} \\ 2 \mapsto 2, \quad 3 \mapsto 3 \\ \end{array}
$$

Notice that this functor is not full.

# 3.2 Products

We first observe how Cartesian products interact with functions.

Example 3.3 Let  $A = \{7,8,9\}$ ,  $B = \{a,b,c\}$ ,  $X = \{1,2,3,4\}$ , and consider functions  $x_{1}:X\to A$ ,  $x_{2}:X\to B$ :

$$
\begin{array}{l} x _ {1}: 1 \mapsto 7, \quad 2 \mapsto 8, \quad 3 \mapsto 9, \quad 4 \mapsto 7, \\ x _ {2}: 1 \mapsto a, \quad 2 \mapsto b, \quad 3 \mapsto c, \quad 4 \mapsto c. \\ \end{array}
$$

The pair of these functions can uniquely be combined as

$$
f: 1 \mapsto (7, a), \quad 2 \mapsto (8, b), \quad 3 \mapsto (9, c), \quad 4 \mapsto (7, c)
$$

that makes the following diagram commute:

![](images/91718a7490beef9fce0200bd91f20279873f3ee366203be0ca307af2ac7566ae.jpg)

where  $p_1$  and  $p_2$  are projections. We fix  $A$  and  $B$ . For each triple  $(X, x_1, x_2)$  we get a unique  $f: X \to A \times B$  that makes the diagram above commute.

Based on this observation, we try to define products without referring to elements of sets involved.

We fix two objects  $A_{1}$  and  $A_{2}$  of  $\mathcal{A}$ . Take any object  $X\in \mathrm{Obj}(\mathcal{A})$  and consider a pair of morphisms  $x_{1}:X\to A_{1}$  and  $x_{2}:X\to A_{2}$ .

$$
A _ {1} \xleftarrow {x _ {1}} X \xrightarrow {x _ {2}} A _ {2}
$$

This triple  $(X, x_{1}, x_{2})$  is called a span from apex  $X$  to  $\{A_{1}, A_{2}\}$ .

We consider a category  $\operatorname{Span}(A_1, A_2)$  of spans to  $\{A_1, A_2\}$ :

-  $\operatorname{Obj}(\operatorname{Span}(A_1, A_2))$  consists of all the spans  $A_1 \xleftarrow{x_1} X \xrightarrow{x_2} A_2$ .  
- a morphism from  $A_1 \xleftarrow{x_1} X \xrightarrow{x_2} A_2$  to  $A_1 \xleftarrow{y_1} Y \xrightarrow{y_2} A_2$  is a morphism  $f: X \to Y$  in  $\mathcal{A}$  that makes the two triangles in the following diagram commute:

![](images/6654acc73ab90c2772bd0f9e9be15d3a66b96482a2a14da7f0d9f97a877488c5.jpg)

We can easily check associativity and other properties required.

We will study initial objects and terminal objects in  $\operatorname{Span}(A_1, A_2)$ . But before stepping into the main discussion, we consider the influence of the initial and terminal objects in  $\mathcal{A}$  on those in  $\operatorname{Span}(A_1, A_2)$ .

Suppose there is an initial object  $0$  in  $\mathcal{A}$ . Then, the two triangles in a diagram

![](images/d52227c0ceca74e514e47061400a7a9a1374a785ddd9a86fb808e43b29f154a5.jpg)

automatically commute with a unique morphism  $f$ , and thus we get a unique morphism in  $\operatorname{Span}(A_1, A_2)$ . In fact, both  $x_1$  and  $y_1 \circ f$  are morphisms from 0 to  $A_1$ , and we know such a morphism exists at most one. Thus, we have  $x_1 = y_1 \circ f$ . Likewise, we have  $x_2 = y_2 \circ f$ . If this is the case, we get no meaningful results in seeking for initial objects in  $\operatorname{Span}(A_1, A_2)$ . And this is often the case with examples we encounter. So, it is not a good idea to think about initial objects in  $\operatorname{Span}(A_1, A_2)$ .

# 3.2 Products

Then, how about thinking of terminals? Suppose there is a terminal object 1 in  $\mathcal{A}$ . Then, the two triangles in a diagram

![](images/ba26fe6b08ad3ed2cdd83b19329cd4334d58afd675ed8726b5fdf3ac05fb9a0d.jpg)

do not automatically commute, even though we have a unique morphism  $f$ . We have no hope to get a unique morphism in  $\operatorname{Span}(A_1, A_2)$ . Therefore, we expect meaningful results in seeking terminal objects in  $\operatorname{Span}(A_1, A_2)$ , despite the possible existence of terminals in  $\mathcal{A}$ . So, it is a good idea to study terminal objects in  $\operatorname{Span}(A_1, A_2)$ .

A terminal span  $A_1 \xleftarrow{z_1} Z \xrightarrow{z_2} A_2$  ensures that for any span  $A_1 \xleftarrow{x_1} X \xrightarrow{x_2} A_2$  there exists a unique morphism  $f: X \to Z$  that makes the two triangles in the following diagram commute:

![](images/f12ec038df2408ae3867f6ecc99c1a5dbcd022a84533be68c09e9c32158a0e85.jpg)

Definition 3.2 A terminal object  $A_{1} \xleftarrow{z_{1}} Z \xrightarrow{z_{2}} A_{2}$  in  $\operatorname{Span}(A_{1}, A_{2})$  is called a product of  $A_{1}$  and  $A_{2}$  and written as  $A_{1} \xleftarrow{p_{1}} A_{1} \times A_{2} \xrightarrow{p_{2}} A_{2}$  or simply  $A_{1} \times A_{2}$  with implicit projections.

Not all pairs have a product in general. If all the pairs in  $\mathcal{A}$  have products, we say that  $\mathcal{A}$  has products, or  $\mathcal{A}$  is a category with products.

Example 3.4 Let us consider Example 3.2 again. Let  $X = \{1, 2, 3\}$ . We study products in category  $\mathcal{P}(X)$ .

If a product of  $\{1,2\}$  and  $\{2,3\}$  exists in  $\mathcal{P}(X)$ , we put  $z = \{1,2\} \times \{2,3\}$ , and write as

$$
\{1, 2 \} \leftarrow z \rightarrow \{2, 3 \}.
$$

Candidates for  $z$  are only  $\{2\}$  and  $\varnothing$  since morphisms are very limited in this category. In other words, we can write as

$$
\begin{array}{l} \operatorname {O b j} (\operatorname {S p a n} (\{1, 2 \}, \{2, 3 \})) \\ = \{\{1, 2 \} \leftarrow \{2 \} \rightarrow \{2, 3 \}, \quad \{1, 2 \} \leftarrow \emptyset \rightarrow \{2, 3 \} \}. \\ \end{array}
$$

$\{1,2\} \leftarrow \{2\} \rightarrow \{2,3\}$  is clearly a terminal object in  $\operatorname{Span}(\{1,2\}, \{2,3\})$ . So, we may write as  $\{2\} = \{1,2\} \times \{2,3\}$ . Notice that  $\{2\}$  is the greatest lower bound of  $\{1,2\}$  and  $\{2,3\}$ .

Proposition 3.3 A product, if it exists, is unique up to isomorphisms.

This comes directly from the uniqueness of terminal objects in general. But, let us repeat the proof in a new context.

Proof Suppose there are two products  $(X, x_{1}, x_{2})$  and  $(Y, y_{1}, y_{2})$  of  $A_{1}$  and  $A_{2}$ . All the triangles, including large ones, in the left diagram

![](images/8da931450c145f49e38c76757eeda1065c89251bdb4fc1dc805837c59daf3867.jpg)

![](images/10572607d6ba424f75c777bbaf910dfc12cc2e8ddae12e0e5d4e0138886f8c35.jpg)

commute with uniquely determined  $f$  and  $g$ . The right one is a trivial commuting diagram. Morphism from  $(X, x_1, x_2)$  to itself must be unique, namely,  $1_X$ . Thus, we have  $g \circ f = 1_X$ .

The same argument goes with  $X$  and  $Y$  exchanged. So, we have  $f \circ g = 1_Y$ .

Example 3.5 We visit Example 3.3 again. In the diagram

![](images/04463b75f197d61864c4268a6a7e5d87858e880aaf57770a725f66875c176dee.jpg)

we fix  $A$  and  $B$ . We consider various spans  $(X, x_1, x_2)$ . For each span  $(X, x_1, x_2)$ , there exists a unique  $f: X \to A \times B$  that makes the two triangles commute. We simulate this situation with a program, where products are implemented with the type constructor  $(, )$ .

Listing 3.1 product.hs  
```haskell
1 data SetA = A7 | A8 | A9 deriving (Enum,Show)  
2  
3 data SetB = Ba | Bb | Bc deriving (Enum,Show)  
4  
5 data SetX = X1 | X2 | X3 | X4 deriving (Enum,Show)  
6  
7 x1 :: SetX -> SetA  
8 x1 X1 = A7  
9 x1 X2 = A8  
10 x1 X3 = A9  
11 x1 X4 = A7  
12  
13 x2 :: SetX -> SetB  
14 x2 X1 = Ba  
15 x2 X2 = Bb  
16 x2 X3 = Bc  
17 x2 X4 = Bc
```

```txt
18   
19 factor :: (x -> a) -> (x -> b) -> (x -> (a,b))   
20 factor p1 p2 x = (p1 x, p2 x)
```

We can check the signature of the factor function as follows:

```txt
\*Main> :t factor x1 x2 factor x1 x2 :: SetX -> (SetA, SetB)
```

We can see that the function factor  $x1 \times 2$  returns a value of type  $X \to A \times B$ . Tests can be done as follows:

```txt
\*Main> [(x，factor x1 x2 x）|x<-[X1..X4]] [(X1,(A7,Ba)),(X2,(A8,Bb)),(X3,(A9,Bc)),(X4,(A7,Bc)))]
```

# 3.3 Coproducts

We first observe how disjoint unions or direct sums interact with functions. The disjoint union of  $A$  and  $B$  is denoted by  $A \sqcup B$  or  $A + B$ . When we want a disjoint union of  $A$  and  $B$  with  $A \cup B \neq \emptyset$ , we adopt a brute force method: we attach different tags to elements of both sets. For example,

$$
\{1, 2, 3 \} \sqcup \{3, 4 \} = \{(L, 1), (L, 2), (L, 3), (R, 3), (R, 4) \}.
$$

This is just Haskell type constructor Either does, which we will see sample code later.

Example 3.6 Let  $A = \{7, 8, 9\}$ ,  $B = \{a, b\}$ ,  $X = \{1, 2, 3, 4, 5, 6\}$ , and consider functions  $x_1: A \to X$ ,  $x_2: B \to X$ :

$$
x _ {1}: 7 \mapsto 1, \quad 8 \mapsto 2, \quad 9 \mapsto 3
$$

$$
x _ {2}: a \mapsto 3, \quad b \mapsto 4.
$$

The pair of these functions can uniquely be combined as

$$
f: 7 \mapsto 1, \quad 8 \mapsto 2, \quad 9 \mapsto 3, \quad a \mapsto 3, \quad b \mapsto 4
$$

that makes the following diagram commute:

![](images/2cf615bc57b944c23696c5d88b1dc403d4b5590a7b79df05a9e881897f3b45f3.jpg)

where  $i_1$  and  $i_2$  are coprojections. We fix  $A$  and  $B$ . For each triple  $(x_1, x_2, X)$  we get a unique  $f: A \sqcup B \to X$  that makes the diagram above commute.

Based on this observation, we try to define coproducts without referring to elements of sets involved.

We fix two objects  $A_{1}$  and  $A_{2}$  of  $\mathcal{A}$ . Take any object  $X \in \mathrm{Obj}(\mathcal{A})$  and consider a pair of morphisms  $x_{1}: A_{1} \to X$  and  $x_{2}: A_{2} \to X$ .

$$
A _ {1} \xrightarrow {x _ {1}} X \xleftarrow {x _ {2}} A _ {2}
$$

This triple  $(x_{1}, x_{2}, X)$  is called a cospan from  $\{A_{1}, A_{2}\}$  to  $X$ . We consider a category  $\operatorname{Cospan}(A_{1}, A_{2})$  of cospans from  $\{A_{1}, A_{2}\}$ :

- Obj(Cospan(A1,A2)) consists of all the cospans  $A_{1}\xrightarrow{x_{1}}X\xleftarrow{x_{2}}A_{2}$  
- a morphism from  $A_1 \xrightarrow{x_1} X \xleftarrow{x_2} A_2$  to  $A_1 \xrightarrow{y_1} Y \xleftarrow{y_2} A_2$  is a morphism  $f: X \to Y$  in  $\mathcal{A}$  that makes the two triangles in the following diagram commute:

![](images/1e36e5cc39f3d26550d0f8c604b72be8f18521d7f51bfa9ee22fea5ad9a482b8.jpg)

We can easily check associativity and other properties required.

In this way, the category of cospans is obtained by fixing  $A_{1}$  and  $A_{2}$ . In this category of cospans, we consider initial and terminal objects.

Suppose the category  $\mathcal{A}$  itself has a terminal object 1. In diagram

![](images/a64c84ed117bfef3e4892bdf09db694efc4651e96f9cd7faa7cfc9a9f5122afa.jpg)

$i_1, i_2$ , and  $f$  are all uniquely determined.  $f \circ x_1$  is a morphism from  $A_1$  to  $1$ . Since only one such morphism is allowed, it matches  $i_1$ . So the left triangle is automatically commutative. Similarly, the triangle on the right is automatically commutative. From this observation, we can see that thinking about terminal objects in the category of cospans is too trivial to give us any new information.

When category  $\mathcal{A}$  itself has initial object 0, only  $f$  is known to be unique in the following diagram.

![](images/3bfc4d5833c9d184f5df7a6ab17bf8ab2700cae53b1cd445092ba963ba93f69d.jpg)

The commutativity of the two triangles is not guaranteed. Therefore, it makes sense to consider the initial object in the category of cospans.

Definition 3.3 Let  $A_{1}$  and  $A_{2}$  be objects in  $\mathcal{A}$ . The coproduct of  $A_{1}$  and  $A_{2}$  is an initial object in the category Cospan  $(A_{1}, A_{2})$ , written as

$$
A _ {1} \sqcup A _ {2} = A _ {1} \xrightarrow {i _ {1}} Z \xleftarrow {i _ {2}} A _ {2},
$$

which is unique up to isomorphisms if it exists. We often (almost always) identify  $A_1 \sqcup A_2$  with its copex  $Z$  by abuse of terminology. If a coproduct exists for any pair of objects in  $\mathcal{A}$ , the category  $\mathcal{A}$  is said to have coproducts or said to be a category with coproducts.

Example 3.7 Let us search for coproducts in the category  $\mathcal{P}(X)$  of the power set of Example 3.2. Consider  $\{1\} \sqcup \{1,2\}$ . Does it exist in the first place? Let  $z$  be a coproduct if it exists. For a cospan

$$
\{1 \} \to z \leftarrow \{1, 2 \}
$$

candidates for  $z$  are  $\{1, 2\}$  and  $\{1, 2, 3\}$ . The category of cospans consists of only two objects and obvious morphisms. The initial object is  $\{1, 2\}$ , which is the least upper bound of  $\{1\}$  and  $\{1, 2\}$ . We have

$$
\{1 \} \sqcup \{1, 2 \} = \{1, 2 \}.
$$

Proposition 3.4 Given two objects in a category, their coproduct is unique up to isomorphisms, if it exists.

This comes directly from the uniqueness of initial objects in general. But, let us repeat the proof in a new context.

Proof Let  $(x_{1}, x_{2}, X)$  and  $(y_{1}, y_{2}, Y)$  be two coproducts of  $A_{1}$  and  $A_{2}$ . Observe the following two diagrams.

![](images/3493273c8ddb52c7b45c64d7443d0058a4ef7e20da3b400604f1a20a54d33a99.jpg)

![](images/c6ae507248a3bd4cfd8f92ed6301d24da18e623106af4601689ddb9962cf7e62.jpg)

All triangles, small or large, in the left diagram commute where  $f$  and  $g$  are uniquely determined. The diagram on the right is a trivial commuting diagram. Since  $(x_{1}, x_{2}, X)$  is initial in the category of cospans, we have  $g \circ f = 1_{X}$ . Exchanging  $X$  and  $Y$ , we also have  $f \circ g = 1_{Y}$ . This means that  $X$  and  $Y$  are isomorphic, and that  $(x_{1}, x_{2}, X)$  and  $(y_{1}, y_{2}, Y)$  are isomorphic.

Example 3.8 We reexamine Example 3.6. Given a diagram

![](images/ea037793db62862d9a84f41b1ca340db51d1a30c60ce3852f665cb911abe2ff3.jpg)

we fix  $A$  and  $B$  and let data  $(x_{1}, x_{2}, X)$  vary arbitrarily. For any  $(x_{1}, x_{2}, X)$ , we get a unique  $f: A + B \to X$  such that all the triangles commute in the above diagram. Let us simulate the situation with Haskell. Coproduct is realized by type constructor Either with two type parameters.

Listing 3.2 coproduct.hs  
```txt
1 data SetA = A7 | A8 | A9 deriving (Enum,Show)  
2  
3 data SetB = Ba | Bb deriving (Enum,Show)  
4  
5 data SetX = X1 | X2 | X3 | X4 | X5 | X6 deriving (Enum,Show)  
6  
7 x1 :: SetA -> SetX  
8 x1 A7 = X1  
9 x1 A8 = X2  
10 x1 A9 = X3  
11  
12 x2 :: SetB -> SetX  
13 x2 Ba = X3  
14 x2 Bb = X4  
15  
16 factor :: (a -> x) -> (b -> x) -> (Either a b -> x)  
17 factor i1 i2 (Left a) = i1 a  
18 factor i1 i2 (Right b) = i2 b
```

The signature of factor is confirmed as follows.

```rust
\*Main> :t factor x1 x2 factor x1 x2 :: Either SetA SetB -> SetX
```

factor x1 x2 is a function that takes a parameter from Either SetA SetB and returns a value in SetX.

\*Main> [Left x, factor x1 x2 (Left x) | x<- [A7 .. A9] ]

[(Left A7,X1),(Left A8,X2),(Left A9,X3)]

\*Main> [(Right x, factor x1 x2 (Right x)) | x<- [Ba,Bb] ]

[(Right Ba,X3),(Right Bb,X4)]

# 3.4 Limits

What we did with products and coproducts can be extended to the notions of limit and colimit. In this section, we generalize the concept of product to that of limit.

Definition 3.4 Let  $J$  be a small category and  $\mathcal{A}$  a category. A diagram in  $\mathcal{A}$  of shape  $J$  is a functor  $F: J \to \mathcal{A}$ .  $J$  is called an index category.  $F$  is often called a  $J$ -shaped diagram in  $\mathcal{A}$ .

Let  $A$  be an object of  $\mathcal{A}$ . A cone from  $A$  to  $F$  is a set of data:

- For each object  $j$  of  $J$ , there is a morphism  $p_j : A \to F(j)$  called projection.  $A$  is called the apex of a cone.  
- For all morphisms  $f: j_1 \to j_2$  of  $J$ , the diagram

![](images/55c45ae9ff658f39ce4b6c53c98a0f4690ebd89940cc79f412ad5d68a9b3d8f6.jpg)

commutes.

A cone is presented as a triple  $(A, \{p_j\}, F)$ , or a pair  $(A, \{p_j\})$ , or simply  $\{p_j\}$ , all of which contain the same amount of information.

Definition 3.5 Let  $J$  be a small category and  $\mathcal{A}$  a category. We fix a  $J$ -shaped diagram  $F: J \to \mathcal{A}$ . We consider a category  $(\mathcal{A}, F)$  defined as follows.

- Objects are cones  $(A, \{p_j\})$ .  
- A morphism from  $(A, \{p_j\})$  to  $(A', \{q_j\})$  is a morphism  $u: A \to A'$  of  $\mathcal{A}$  such that all the triangles below commute for all morphisms  $f$  of  $J$ .

![](images/c0a7a9299fd415f98d333d07c913f732d562052dc07953de664c52e01c54e3d6.jpg)

If category  $(\mathcal{A}, J, F)$  has a terminal object  $(L, \{r_j\})$ , we call it a limit of the diagram  $F$ . We often call its apex  $L$  a limit of  $F$  with implicit  $\{r_j\}$ . Cone  $(L, \{r_j\})$  is also called a universal cone or limiting cone. From the general argument over terminal objects,  $L$  is unique up to isomorphism. It is often written as  $L = \varprojlim F$ . Given an arbitrary cone, a unique morphism from it to the limiting cone is called a mediating morphism.

Remark 3.1 The set of all cones from  $A$  to  $F$  is written as  $\operatorname{Cones}(A, F)$ . We have the following isomorphism.

$$
\mathscr {A} (A, \varprojlim F) \simeq \operatorname {C o n e s} (A, F)
$$

When  $\mathcal{A}$  is locally small, using the language of Chap. 7, the above isomorphism means that  $\lim F$  is an object that represents the contravariant functor  $\operatorname{Cones}(-,F):\mathcal{A}^{\mathrm{op}}\to \mathbf{Set}$ . See also Chap. 5.

Example 3.9 Let the index category  $J$  be the category with only two objects 1 and 2 and the identity morphisms. Determining a functor  $F$  from  $J$  to the category  $\mathcal{A}$  is the same as choosing two objects in the category  $\mathcal{A}$ . Given  $F(1) = A_{1}$  and  $F(2) = A_{2}$ , the span from any object  $X$  in the category  $\mathcal{A}$

$$
A _ {1} \xleftarrow {x _ {1}} X \xrightarrow {x _ {2}} A _ {2}
$$

is the same as considering the cone from  $X$  to a  $J$ -shaped diagram  $F$ . Considering the category of spans  $\operatorname{Span}(A_1, A_2)$ , and the category of cones  $(\mathcal{A}, F)$  is the same. So it turns out that the limit is a generalization of the product.

Example 3.10 We consider an index category  $J$  with natural numbers  $1, 2, 3, \dots$  as objects and

$$
1 \leftarrow 2 \leftarrow 3 \leftarrow \dots
$$

as generators of morphisms. Let  $F: J \to \mathbf{Set}$  be a functor where

- function on objects is given by  $F(n) = \mathbb{R}^n$ ,  
- function on morphisms is given by  $F(n \leftarrow n + 1) = p_n$ , where  $p_n$  is a projection

$$
p _ {n}: \mathbb {R} ^ {n + 1} \rightarrow \mathbb {R} ^ {n}
$$

$$
(x _ {1}, x _ {2}, \dots , x _ {n}, x _ {n + 1}) \mapsto (x _ {1}, x _ {2}, \dots , x _ {n}).
$$

Let  $Y$  be an arbitrary set. A cone from  $Y$  to a  $J$ -shaped diagram  $F$  is given by a family of morphisms  $\{y_n\}$  that makes all the triangles with edges  $y_n$  and  $p_n$  commute:

![](images/9e2ebb158bf76df370864864f7563aca8898060f04982a0bc7b9dc177acaf80a.jpg)

We have  $\varprojlim F = \mathbb{R}^{\infty}$ . In fact, we use the data  $\{y_{n}\}$  to uniquely define  $f:Y\to \mathbb{R}^{\infty}$  as

$$
f (z) = \left(f _ {1} (z), f _ {2} (z), \dots , f _ {n} (z), \dots\right),
$$

where  $y_{n}(z)\in \mathbb{R}^{n}$  and  $f_{n}(z)$  is its  $n$  -th component.

Definition 3.6 We consider an index category  $J$  with objects 0, 1, and 2. The following two morphisms

$$
1 \rightarrow 0 \leftarrow 2
$$

generate the whole morphisms. A limit of a  $J$ -shaped diagram is called a pullback or fiber product. Let  $F: J \to \mathcal{A}$  be a functor given by:

-  $F(0) = A_0$ ,  $F(1) = A_1$ ,  $F(2) = A_2$ , and  
-  $F(1 \to 0) = a_{1}$ ,  $F(2 \to 0) = a_{2}$ .

We consider a cone  $(X, \{x_0, x_1, x_2\}, F)$ , which is depicted as the left diagram in Eq. (3.1).

$$
A _ {1} \xrightarrow [ a _ {1} ]{X} A _ {0} \xleftarrow [ a _ {2} ]{X _ {2}} A _ {2} \quad A _ {1} \xleftarrow [ a _ {1} ]{X _ {1}} A _ {0} \xleftarrow [ a _ {2} ]{X _ {2}} A _ {2} \tag {3.1}
$$

The qualification test for being a cone is

$$
x _ {0} = a _ {1} \circ x _ {1} \quad \text {a n d} \quad x _ {0} = a _ {2} \circ x _ {2},
$$

which is reduced to a single equation  $a_1 \circ x_1 = a_2 \circ x_2$ . We can confirm this fact as follows. Omitting  $x_0$  gives the diagram on the right. If this diamond is commutative,

we can regain morphism  $x_0$  by  $x_0 = a_1 \circ x_1 = a_2 \circ x_2$ . Thus, both commutative diagrams contain the same information.

Let us suppose there is a universal cone  $(L, \{p_0, p_1, p_2\}, F)$ . Taking the above argument into account, all we have to do is to check the commutativity of all the triangles and squares in the following diagram.

![](images/4a34cc054cf9f8d6cd11b73b7ada43d72c2a7dce966f5227bf0e2c279e23c52d.jpg)

By universality, morphism  $f$  is uniquely determined. Note that morphism  $p_0$  is omitted but easily regained by setting  $p_0 = a_1 \circ p_1 = a_2 \circ p_2$ .

A pullback  $\varprojlim F$  is often written as

$$
L = A _ {1} \times_ {A _ {0}} A _ {2}.
$$

Example 3.11 Let  $A_0 = \{a, b\}$ ,  $A_1 = \{1, 2, 3, 4\}$ , and  $A_2 = \{5, 6, 7, 8\}$ . We consider functions  $a_1: A_1 \to A_0$  and  $a_2: A_2 \to A_0$  as follows.

![](images/038b78bfc97a5ee49e9c83a062d69170751f389ffa61d08345a63a5b8accca85.jpg)

A pullback or fiber product is given by

$$
A _ {1} \times_ {A _ {0}} A _ {2} = (\{1, 2 \} \times \{5, 7 \}) \sqcup (\{3, 4 \} \times \{6, 8 \}). \tag {3.2}
$$

$\{1,2\}$  and  $\{5,7\}$  are fibers over  $a$  of  $a_1$  and  $a_2$ , respectively.  $\{3,4\}$  and  $\{8,9\}$  are fibers over  $b$  of  $a_1$  and  $a_2$ , respectively. The RHS of (3.2) is a disjoint union of the pointwise direct products of fibers over a single point.

Haskell code is given below.

Listing 3.3 fiberproduct.hs  

<table><tr><td>1</td><td>data A0 = Va | Vb deriving (Eq, Show)</td></tr><tr><td>2</td><td></td></tr><tr><td>3</td><td>data A1 = V1 | V2 | V3 | V4 deriving (Eq, Enum, Show)</td></tr><tr><td>4</td><td></td></tr><tr><td>5</td><td>data A2 = V5 | V6 | V7 | V8 deriving (Eq, Enum, Show)</td></tr></table>

```haskell
fiberProduct :: (Eq a, Eq b, Eq c) =>  
(b -> a) -> (c -> a) -> [b] -> [c] -> [(a,b,c)]  
fiberProduct p q xs ys =  
[(p x,x,y) | x<- xs, y<- ys, px==q y]  
11  
getFiber :: Eq a => a -> [(a,b,c)] -> [(b,c)]  
getFiber bp zxys = [(x,y) | (z,x,y)<- zxys, z == bp]  
14  
-- testdata  
16 a1s = [V1 .. V4]  
17 a2s = [V5 .. V8]  
18  
a1 :: A1 -> A0  
a1 V1 = Va  
a1 V2 = Va  
a1 V3 = Vb  
a1 V4 = Vb  
24  
a2 :: A2 -> A0  
a2 V5 = Va  
a2 V6 = Vb  
a2 V7 = Va  
a2 V8 = Vb  
30  
{-- suggested tests  
fiberProduct a1 a2 a1s a2s  
getFiber Va $ fiberProduct a1 a2 a1s a2s  
getFiber Vb $ fiberProduct a1 a2 a1s a2s  
}
```

Lines 1-5 define data types for  $A_0$ ,  $A_1$ , and  $A_2$  in Example 3.11.

Lines 7-10 define a function that realizes the fiber product.

Lines 12-13 define agetter function for fibers.

Lines 15-29 give data structures for all players, namely objects and morphisms. A test goes like this.

```txt
\*Main> getFiber Va  $\$$  fiberProduct a1 a2 a1s a2s
[(V1,V5),(V1,V7),(V2,V5),(V2,V7)]
\*Main> getFiber Vb  $\$$  fiberProduct a1 a2 a1s a2s
[(V3,V6),(V3,V8),(V4,V6),(V4,V8)]
```

The results are fibers over a and b.

Definition 3.7 We consider a category  $J$  with objects 0 and 1. Generators of morphisms are

```txt
$0\xrightarrow[b]{a}1.$
```

A limit of a  $J$ -shaped diagram in category  $\mathcal{A}$  is called an equalizer. Let us look closer into the situation. Let a functor  $F: J \to \mathcal{A}$  be defined by the following:

- function on objects is given by  $F(0) = A_{1}$  and  $F(1) = A_{2}$ .  
- function on morphisms is given by  $F(a) = f$  and  $F(b) = g$ .

We consider a cone from  $X$  to  $F$ .

![](images/f427e0a057b291c638ec848dad3b0067d5dc4fc3e47f7b687f342a24a6b84a4e.jpg)

Any cone must pass a qualification test for being really a cone:

$$
* = f \circ h \quad \text {a n d} \quad * = g \circ h
$$

Thus, we have

$$
f \circ h = g \circ h.
$$

To sum up, getting a limit of a  $J$ -shaped diagram is completely the same as finding a universal object  $L$  giving a unique  $h'$  that makes the following diagram commute.

![](images/8a8335e512da5c096599d8d6831fc9b330cb54c9d60dcae302badb1e86596bbf.jpg)

Example 3.12 Let  $A_{1} = \{1,2,3,4\}$  and  $A_{2} = \{a,b,c\}$ . We consider the following two functions  $f,g:A_1\to A_2$ :

$\{2,3\} \xrightarrow{e} A_1\xrightarrow[g]{f}A_2$

![](images/a9d70d965ed79703d16050304039ab03aaa40e2115b9cf4ec010956af67864f5.jpg)

$g$  is depicted with dotted lines. Function  $e:\{2,3\} \to A_1$  is an equalizer.

The Haskell code for this example is given below.

Listing 3.4 equalizer.hs  
```haskell
1 data A1 = V1 | V2 | V3 | V4  
2 deriving (Eq, Enum, Show)  
3  
4 data A2 = Va | Vb | Vc deriving (Eq, Enum, Show)  
5  
6 -- We will be content with  
7 -- finding a subobject(subset) of A1  
8 equalizer :: (Eq a, Enum a, Eq b) =>  
9 (a -> b) -> (a -> b) -> [a] -> [a]  
10 equalizer fg xs  
11 = [x | x <- xs, f x == g x]  
12  
13 f :: A1 -> A2  
14 f V1 = Va  
15 f V2 = Vb  
16 f V3 = Vc  
17 f V4 = Vc  
18  
19 g :: A1 -> A2  
20 g V1 = Vb  
21 g V2 = Vb  
22 g V3 = Vc  
23 g V4 = Va  
24  
25 {-- suggested test  
26 equalizer fg [V1..V4]  
27 -}
```

Lines 1-4 define  $A_{1}$  and  $A_{2}$ . Lines 10-11 define equalizer. It would be better to give this function a signature like (a -> b) -> (a -> b) -> [a], but we compromise for ease of implementation.

Let us give it a try.

```txt
\*Main> equalizer f g [V1 .. V4] [V2,V3]
```

Definition 3.8 A category with no morphisms other than identities is called a discrete category. Let  $J$  be a small discrete category, namely a set. If a  $J$ -shaped diagram  $F: J \to \mathcal{A}$  has a limit, we call this limit in particular a product or direct product. The apex of a limit cone is often written as  $\prod_{J} F(j)$ . Note that  $J$  is not limited to a finite set.

Given a cone from  $X$  to  $F$ , namely a set of morphisms  $\{f_j : X \to F(j)\}_{j \in \mathrm{Obj}(J)}$ , the mediating morphism  $u$  in the following diagram

![](images/e86ef4b084ff5b46dc0032d11dd82de082f5947178db1689b4e14d92dbb047e2.jpg)

is often written as

$$
u = \prod_ {j \in \operatorname {O b j} (J)} f _ {j}.
$$

A product of morphisms accompanies with the universality of product.

Proposition 3.5 We use the same notation in Definition 3.8. Consider an arbitrary morphism  $g: Y \to X$ . We have the following.

$$
\left(\prod_ {j \in \operatorname {O b j} (J)} f _ {j}\right) \circ g = \prod_ {j \in \operatorname {O b j} (J)} \left(f _ {j} \circ g\right).
$$

The operation of composing  $g$  from right and the operation of taking a limit commute.

Proof First, observe that all the triangles in the diagram

![](images/64abc678b7fcbe389b671c14a144764e5b7e43245623c3a89dfc86dfc950b981.jpg)

commute. Large triangles obtained by taking the union of the adjacent small triangles also commute. Consider a cone  $(Y, \{f_j \circ g\})$ . The mediating morphism from  $Y$  to the universal cone is given by

$$
\prod_ {j \in \operatorname {O b j} (J)} \left(f _ {j} \circ g\right). \tag {3.3}
$$

While morphism

$$
\left(\prod_ {j \in \operatorname {O b j} (J)} f _ {j}\right) \circ g \tag {3.4}
$$

makes all the large triangles

$$
\begin{array}{c}\underset {f _ {j} \circ g} {\overset {f _ {j} \circ g} {\rightleftarrows}} \underset {\downarrow} {\overset {Y} {\rightleftarrows}} (\prod_ {j} f _ {j}) \circ g\\F (j) \xleftarrow [ p _ {j} ]{\underset {p _ {j}} {\rightleftarrows}} \prod_ {j} F (j)\end{array}
$$

commute. Therefore, it is a mediating morphism from  $Y$  to the universal cone. Since the mediating morphism is uniquely determined, we see that (3.3) and (3.4) coincide.

# 3.5 Colimits

In this section, we generalize the concept of coproduct to that of colimit. The arguments are almost parallel to those in the previous section.

We introduce the dual concept of cone.

Definition 3.9 Let  $J$  be a small category and  $\mathcal{A}$  a category. Let  $F: J \to \mathcal{A}$  be a  $J$ -shaped diagram and  $A$  an object of  $\mathcal{A}$ . A cocone from  $F$  to  $A$  is a set of data:

- For each object  $j$  of  $J$ , there is a morphism  $p_j : F(j) \to A$  called coprojection.  $A$  is called the apex of a cocone.  
- For all morphisms  $f: j_1 \to j_2$  of  $J$ , the diagram

$$
F (j _ {1}) \xrightarrow [ p _ {j _ {1}} ]{F (f)} F (j _ {2})
$$

commutes.

A cone is presented as a triple  $(F, \{p_j\}, A)$ , or a pair  $(\{p_j\}, A)$ , or simply  $\{p_j\}$ , all of which contain the same amount of information.

Definition 3.10 Let  $J$  be a small category and  $\mathcal{A}$  a category. We fix a  $J$ -shaped diagram  $F: J \to \mathcal{A}$ . We consider a category  $(F, \mathcal{A})$  defined as follows.

- Objects are cocones  $(\{p_j\}, A)$ .

- A morphism from  $(\{p_j\}, A)$  to  $(\{q_j\}, A')$  is a morphism  $u: A \to A'$  of  $\mathcal{A}$  such that all the triangles below commute for all morphisms  $f$  of  $J$ .

![](images/963b3c77c33c412ca10fe1b3f460e6d9bc09a7fdb60da225d9006352537204df.jpg)

![](images/a96bb8a8dd6e4ac42a39ba6c166e08ed8d427d24cdaa176bfbc7d1eceaf09345.jpg)

If category  $(F, \mathcal{A})$  has an initial object  $(\{r_j\}, L)$ , we call it a colimit of the diagram  $F$ . We often call its apex  $L$  a colimit of  $F$  with implicit  $\{r_j\}$ . Cone  $(L, \{r_j\})$  is also called a universal cocone or limiting cocone. From the general argument over initial objects,  $L$  is unique up to isomorphism. It is often written as  $L = \varinjlim F$ . Given an arbitrary cocone, a unique morphism to it from the limiting cone is called a mediating morphism.

Remark 3.2 The set of all cocones from  $F$  to  $A$  is written as  $\operatorname{Cones}(F, A)$ . We have the following isomorphism.

$$
\mathscr {A} (\varinjlim F, A) \simeq \operatorname {C o n e s} (F, A)
$$

When  $\mathcal{A}$  is locally small, using the language of Chap. 7, the above isomorphism means that  $\lim F$  is an object that represents the covariant functor  $\operatorname{Cones}(F, -): \mathcal{A} \to \mathbf{Set}$ . See also Chap. 5.

Example 3.13 Let the index category  $J$  be the category with only two objects 1 and 2 and the identity morphisms. Determining a functor  $F$  from  $J$  to the category  $\mathcal{A}$  is the same as choosing two objects in the category  $\mathcal{A}$ . Given  $F(1) = A_{1}$  and  $F(2) = A_{2}$ , the cospan to any object  $X$  in the category  $\mathcal{A}$

$$
A _ {1} \stackrel {x _ {1}} {\longrightarrow} X \stackrel {x _ {2}} {\leftarrow} A _ {2}
$$

is the same as considering the cocone from  $J$ -shaped diagram  $F$  to an object of  $\mathcal{A}$ . Considering the category of cospans  $\operatorname{Cospan}(A_1, A_2)$ , and the category of cocones  $(F, \mathcal{A})$  is the same. So it turns out that colimit is a generalization of coproduct.

Example 3.14 We consider an index category  $J$  with natural numbers  $1, 2, 3, \dots$  as objects and

$$
1 \rightarrow 2 \rightarrow 3 \rightarrow \dots
$$

as generators of morphisms. Let  $F: J \to \mathbf{Set}$  be a functor where

- function on objects is given by  $F(n) = \mathbb{R}^n$ ,  
- function on morphisms is given by  $F(n \to n + 1) = i_n$ , where  $i_n$  is an embedding

$$
i _ {n}: \mathbb {R} ^ {n} \to \mathbb {R} ^ {n + 1}
$$

$$
(x _ {1}, x _ {2}, \dots , x _ {n}) \mapsto (x _ {1}, x _ {2}, \dots , x _ {n}, 0).
$$

Let  $Y$  be an arbitrary set. A cocone from a  $J$ -shaped diagram  $F$  to  $Y$  is given by a family of morphisms  $\{y_n\}$  that makes all the triangles with edges  $y_n$  and  $i_n$  commute:

![](images/406e2855c7fa19d536b229a274093caf61074ee18397f379b4dacc756ea6aef4.jpg)

A colimit of the  $J$ -shaped diagram is  $\mathbb{R}_{\infty}$ , namely an infinite dimensional space consisting of vectors with a finite number of nonzero components. Note that  $\mathbb{R}_{\infty} \neq \mathbb{R}^{\infty}$ . We write  $\varinjlim F = \mathbb{R}_{\infty}$  or

$$
\bigcup_ {n} \mathbb {R} ^ {n}.
$$

Using cocone data  $\{y_{n}\}$ , we can construct the unique mediating morphism  $f:\mathbb{R}_{\infty}\to Y$ . For any  $z\in \mathbb{R}_{\infty}$  there is a natural number  $n$  such that we can regard  $z\in \mathbb{R}^n$ . With this  $n$  we define as

$$
f (z) = y _ {n} (z).
$$

We may choose a greater  $n$ , which gives the same result due to the commutativity of the triangles.

Definition 3.11 We consider an index category  $J$  with objects 0, 1, and 2. The following two morphisms

$$
1 \leftarrow 0 \rightarrow 2
$$

generate the whole morphisms. A colimit of a  $J$ -shaped diagram is called a pushout or fibered coproduct, the dual of pullback. Let  $F: J \to \mathcal{A}$  be a functor given by:

-  $F(0) = A_0$ ,  $F(1) = A_1$ ,  $F(2) = A_2$ , and  
-  $F(0 \to 1) = a_{1}$ ,  $F(0 \to 2) = a_{2}$ .

We consider a cocone  $(F, \{x_0, x_1, x_2\}, X)$ , which is depicted as the left diagram in Eq. (3.5).

$$
A _ {1} \xleftarrow {\begin{array}{c} a _ {1} \\ x _ {1} \end{array}} A _ {0} \xrightarrow {\begin{array}{c} a _ {2} \\ x _ {0} \end{array}} A _ {2} \quad A _ {1} \xleftarrow {\begin{array}{c} a _ {1} \\ x _ {1} \end{array}} A _ {0} \xrightarrow {\begin{array}{c} a _ {2} \\ x _ {2} \end{array}} A _ {2} \tag {3.5}
$$

The qualification test for being a cocone is

$$
x _ {0} = x _ {1} \circ a _ {1} \quad \text {a n d} \quad x _ {0} = x _ {2} \circ a _ {2},
$$

which is reduced to a single equation  $x_{1} \circ a_{1} = x_{2} \circ a_{2}$ . We can confirm this fact as follows. Omitting  $x_{0}$  gives the diagram on the right. If this diamond is commutative, we can regain morphism  $x_{0}$  by  $x_{0} = x_{1} \circ a_{1}$ . Thus, both commutative diagrams contain the same information.

Let us suppose there is a universal cocone  $(F, \{i_0, i_1, i_2\}, L)$ . Taking the above argument into account, all we have to do is to check the commutativity of all the triangles and squares in the following diagram.

![](images/27b86e7d9d17cac601cfefba9d4c0706248cca3e0267d2396388d8ddaa717c99.jpg)

By universality, morphism  $f$  is uniquely determined. Note that morphism  $i_0$  is omitted but easily regained by setting  $i_0 = i_1 \circ a_1 = i_2 \circ a_2$ .

Remark 3.3 Pushouts can be given an alternative definition as follows. We fixed a diagram at the left. Consider a category such that objects are triples  $(x_{1}, x_{2}, X)$  that makes the diagram at right commute.

$$
\begin{array}{c c} A _ {0} \xrightarrow {a _ {2}} A _ {2} & A _ {0} \xrightarrow {a _ {2}} A _ {2} \\ a _ {1} \Bigg \downarrow & a _ {1} \Bigg \downarrow \\ A _ {1} & A _ {1} \xrightarrow [ x _ {1} ]{} X \end{array}
$$

A morphism from  $(x_{1}, x_{2}, X)$  to  $(y_{1}, y_{2}, Y)$  must make all the triangles and squares in the following diagram commute.

![](images/a0490050924379e085b4ae42ac489baed1f6264a7d08b27107514e1a2c3c7f1b.jpg)

The pushout  $(i_1, i_2, L)$  is an initial object of the category so obtained.

Example 3.15 Let  $A_0 = \{a, b, c, d\}$ ,  $A_1 = \{1, 2, 3, 4\}$ , and  $A_2 = \{5, 6, 7, 8\}$ . We consider functions  $a_1: A_0 \to A_1$  and  $a_2: A_0 \to A_2$  as follows.

![](images/8da05bbf3112cf73eba8a22def4295969f238782e150063b9c5b792182b76f2b.jpg)

A pushout or fibered coproduct is given by

$$
A _ {1} \bigcup_ {A _ {0}} A _ {2} = \{L 2, G [ 1, 4 ] [ 5, 6 ], G [ 3 ] [ 7 ], R 8 \},
$$

where notation needs explanation.  $L2$  and  $R8$  are points that escape from being glued.  $L2$  is an element that comes from the set at left.  $R8$  comes from the set at right.  $G[1,4][5,6]$  is an element formed by gluing 1 and 4 from the set at left, 5 and 6 from the set at right.  $G[3][7]$  is an element obtained by gluing 3 and 7.

The above construction went as follows. We first simply take the disjoint union of  $A_{1}$  and  $A_{2}$ . Then, the gluing is carried out by identifying points  $x_{1} \in A_{1}$  and  $x_{2} \in A_{2}$  when there is  $x_{0}$  such that  $x_{1} = a_{1}(x_{0})$  and  $x_{2} = a_{2}(x_{0})$ . Such identification must be extended transitively. This construction is called a disjoint union with gluing.

Haskell code may help you understand what is going on.

Listing 3.5 fibercoproduct.hs  

<table><tr><td>1</td><td>data A0 = Va | Vb | Vc | Vd deriving (Ord, Eq, Enum, Show)</td></tr><tr><td>2</td><td>data A1 = V1 | V2 | V3 | V4 deriving (Ord, Eq, Enum, Show)</td></tr><tr><td>3</td><td>data A2 = V5 | V6 | V7 | V8 deriving (Ord, Eq, Enum, Show)</td></tr><tr><td>4</td><td></td></tr><tr><td>5</td><td>-- Disjoint Union with Gluing</td></tr><tr><td>6</td><td>data DUnG a b c =</td></tr></table>

```haskell
7 L b | R c | G [b] [c] deriving (Ord, Eq, Show)  
8  
9 fibercoproduct :: (Ord a, Ord b, Ord c) =>  
10 (a -> b) -> (a -> c) -> [a] -> [b] -> [c] -> [DUwG a b c]  
11 fibercoproduct p q as xs ys =  
12 [L x | x <- xs, not (x 'elem' (fmap p as)) ] ++  
13 glue p q as xs ys ++  
14 [R y | y <- ys, not (y 'elem' (fmap q as)) ]  
15  
16 glue :: (Ord a, Ord b, Ord c) =>  
17 (a -> b) -> (a -> c) -> [a] -> [b] -> [c] -> [DUwG a b c]  
18 glue p q as xs ys =  
19 let  
20 oneStepGlues = [(p a], [q a]) | a<-as]  
21 classes = collect oneStepGlues  
22 in  
23 map (\xys -> G (fst xys) (snd xys)) classes  
24  
25 collect :: (Ord b, Ord c) => [(b], [c]) -> [(b], [c])  
26 collect [] =  
27 collect [x] = [x]  
28 collect (x:xs) =  
29 fst folded :snd folded  
30 where  
31 folded = foldl f (x,[]) (collect xs)  
32 f (z,zs) y  
33 | equivQ z y = (merge z y, zs)  
34 | otherwise = (z, y:zs)  
35  
36 equivQ :: (Ord b, Ord c) => ([b], [c]) -> ([b], [c]) -> Bool  
37 equivQ (bs1,cs1) (bs2,cs2) =  
38 [x | x <- bs1, y <- bs2, x == y] /= []  
39 [u | u <- cs1, v <- cs2, u == v] /= []  
40  
41 merge :: (Ord b, Ord c) => ([b], [c]) -> ([b], [c]) -> ([b], [c])  
42 merge (bs1,cs1) (bs2,cs2) =  
43 (uniq (bs1++bs2),uniq (cs1++cs2))  
44  
45 -- unique sort  
46uniq :: Ord a => [a] -> [a]  
47uniq xs =  
48 foldr ins [] xs  
49 where  
50 ins y [] = [y]  
51 ins y (z:zs)  
52 | y<z = y:z:zs  
53 | y==z = z:zs  
54 | otherwise = z:ins y zs  
55  
56 ____________  
57 -- testdata  
58 -- Both a1 and a2 are injective.  
59  
60 a0s = [Va .. Vd]  
61 a1s = [V1 .. V4]
```

```haskell
62 a2s = [V5 .. V8]  
63  
64 a1 :: A0 -> A1  
65 a1 Va = V1  
66 a1 Vb = V2  
67 a1 Vc = V3  
68 a1 Vd = V4  
69  
70 a2 :: A0 -> A2  
71 a2 Va = V5  
72 a2 Vb = V6  
73 a2 Vc = V7  
74 a2 Vd = V8  
75  
76 {-- suggested tests  
77 fibercoproduct a1 a2 a0s a1s a2s  
78 => [G [V1] [V5], G [V3] [V7], G [V4] [V8], G [V2] [V6]]  
79 -}  
80  
81  
82 -- b2 is injective while b1 is not.  
83  
84 b1 :: A0 -> A1  
85 b1 Va = V1  
86 b1 Vb = V1  
87 b1 Vc = V3  
88 b1 Vd = V3  
89  
90 b2 :: A0 -> A2  
91 b2 Va = V5  
92 b2 Vb = V6  
93 b2 Vc = V7  
94 b2 Vd = V8  
95  
96 {-- suggested test  
97 fibercoproduct b1 b2 a0s a1s a2s  
98 => [L V2, L V4, G [V1] [V5, V6], G [V3] [V7, V8]]  
99 -}  
100  
101  
102 -- c1 and c2 are non-injective.  
103  
104 c1 :: A0 -> A1  
105 c1 Va = V1  
106 c1 Vb = V1  
107 c1 Vc = V3  
108 c1 Vd = V3  
109  
110 c2 :: A0 -> A2  
111 c2 Va = V6  
112 c2 Vb = V6  
113 c2 Vc = V8  
114 c2 Vd = V8  
115  
116 {-- suggested test
```

```txt
117 fibercoproduct c1 c2 a0s a1s a2s  
118 => [L V2,L V4,G [V1] [V6],G [V3] [V8],R V5,R V7]  
119 -}  
120  
121  
122 -- non trivial transition  
123 d1 :: A0 -> A1  
124 d1 Va = V1  
125 d1 Vb = V1  
126 d1 Vc = V3  
127 d1 Vd = V4  
128  
129 d2 :: A0 -> A2  
130 d2 Va = V5  
131 d2 Vb = V6  
132 d2 Vc = V7  
133 d2 Vd = V6  
134  
135 {- suggested test  
136 fibercoproduct d1 d2 a0s a1s a2s  
137 => [L V2,G [V1,V4] [V5,V6],G [V3] [V7],R V8]  
138 -}
```

Lines 1-3 define data types for  $A_0$ ,  $A_1$ , and  $A_2$  in Example 3.15.

Lines 6-7 define a data type for disjoint union with gluing. Value constructors  $L$  and  $R$  are for points that escape from being glued. Value constructor  $G$  takes two parameters. The first parameter is the list of elements in  $A_{1}$ , and the second is the list of elements in  $A_{2}$ , which are glued into a single point.

Lines 9-14 define a function that constructs a fibered coproduct. The return value is the concatenation of three lists. The first one is the list of points coming from the left (object) that escape from the gluing. The third one is the list of points coming from the right that escape from the gluing. The second one is the list of points that are glued in some way.

The gluing strategy, implemented by the function glue in lines 16-23, is as follows:

- the list oneStepGlues consists of pairs. We first seek for a pair (p a, q a) for each  $a \in A_0$ . Then, we box p a and p q in the singleton lists [p a] and [q a], which will be used as seeds for the following transitive closure operation.  
- the equivalence classes are recursively calculated by the collect function in lines 25-34, which is equivalent to taking the transitive closure.

The suggested test is commented on at the bottom of the sample code runs like this, which is derived from Example 3.15.

```txt
\*Main>fibercoproduct d1 d2 a0s a1s a2s [L V2,G [V1,V4] [V5,V6],G [V3] [V7],R V8]
```

Definition 3.12 We consider a category  $J$  with objects 0 and 1. Generators of morphisms are

$$
0 \xrightarrow [ b ]{a} 1.
$$

A colimit of a  $J$ -shaped diagram in category  $\mathcal{A}$  is called a coequalizer. Let us have a closer look at the situation. Let a functor  $F: J \to \mathcal{A}$  be defined by the following:

- function on objects is given by  $F(0) = A_{1}$  and  $F(1) = A_{2}$ .  
- function on morphisms is given by  $F(a) = f$  and  $F(b) = g$ .

We consider a cocone from  $F$  to  $X$ .

![](images/32fd3c1f53f112785d0f25f3b88b8e8166495faca74cea7510a9b65dc90af1e0.jpg)

Any cocone must pass a qualification test for being really a cocone:

$$
h \circ f = * \quad \text {a n d} \quad h \circ g = *
$$

Notice that we can ignore morphism  $^*$  without losing any information, considering the following single equation.

$$
h \circ f = h \circ g
$$

To sum up, getting a colimit of a  $J$ -shaped diagram is completely the same as finding a universal object  $L$  giving a unique  $h'$  that makes the following diagram commute.

$$
A _ {1} \xrightarrow [ g ]{f} A _ {2} \xrightarrow [ h ]{c} L
$$

Example 3.16 Let  $A_{1} = \{1,2,3,4,5\}$  and  $A_{2} = \{a,b,c,d,e\}$ . We consider the following two functions  $f,g:A_1\to A_2$ :

![](images/02d8fdd0e371a9838bd1adba8db39d89c6b5cd2a4aecaa2b3aab30d666c07a82.jpg)

$g$  is depicted with dotted lines. Function  $t:A_2\to \{\{a,b\} ,\{c,d\} ,\{e\} \}$  is a coequalizer. If the images of  $f$  and  $g$  of the same point differ, we bundle these points in  $L$ . This eliminates the differences

$$
f (1) \neq g (1), \quad f (4) \neq g (4).
$$

The Haskell code for this example is given below.

Listing 3.6 product.hs  
```haskell
1 data SetA = A7 | A8 | A9 deriving (Enum,Show)  
2  
3 data SetB = Ba | Bb | Bc deriving (Enum,Show)  
4  
5 data SetX = X1 | X2 | X3 | X4 deriving (Enum,Show)  
6  
7 x1 :: SetX -> SetA  
8 x1 X1 = A7  
9 x1 X2 = A8  
10 x1 X3 = A9  
11 x1 X4 = A7  
12  
13 x2 :: SetX -> SetB  
14 x2 X1 = Ba  
15 x2 X2 = Bb  
16 x2 X3 = Bc  
17 x2 X4 = Bc  
18  
19 factor :: (x -> a) -> (x -> b) -> (x -> (a,b))  
20 factor p1 p2 x = (p1 x, p2 x)
```

Lines 1-9 define a function coalesce that takes two functions  $p, q: A \to B$  and lists of elements of  $A$  and  $B$  as parameters and returns a list of glued points in  $B$ .

Let us visualize how coalesce works with concrete data, namely two functions  $f: A_1 \to A_2$  and  $h: A_1 \to A_2$  defined in lines 51-56 and 65-70, respectively.

![](images/711ece9cf8f0ca621f1ed238f86c8f2354e9b24b8ba1c9d65b14811347984701.jpg)

The three small arcs appearing on the right show the relation returned by coequate. The minimal information is given as follows.

$$
a \sim^ {0} b, c \sim^ {0} d, d \sim^ {0} e
$$

Lacking transitivity, we cannot claim  $c \sim^0 e$ . Try suggested tests.

Definition 3.13 Let  $J$  be a discrete category, namely a set. If a  $J$ -shaped diagram  $F: J \to \mathcal{A}$  has a colimit, it is called a coproduct or direct sum. Notice that  $J$  may be infinite.

Given a cocone from  $F$  to  $X$ , in other words, a set of morphisms  $\{f_j : F(j) \to X\}_{j \in \mathrm{Obj}(J)}$ , the diagram

![](images/bdf1224c9512ab587ee4a7959fbbde74f4ec234e5755d04af811571c52b5d06b.jpg)

has a mediating morphism  $u$ , which we especially denote by

$$
u = \coprod_ {j \in \operatorname {O b j} (J)} f _ {j}.
$$

Proposition 3.6 We use the notation in Definition 3.13. Given a morphism  $g: X \to Y$ , we have the following:

$$
g \circ \left(\prod_ {j \in \operatorname {O b j} (J)} x _ {j}\right) = \prod_ {j \in \operatorname {O b j} (J)} (g \circ x _ {j}),
$$

which means that operating  $g$  from left is commutative with the coproduct operation.

Proof In diagram

![](images/bbf841be1cabd6a48efffa1547a8fd9f4daeab2cfe1a044b7505a32a457e1d13.jpg)

the triangles are all commutative. Larger triangles made by composition are also commutative. Let us consider a cocone  $(\{g \circ x_j\}, Y)$ . A mediating morphism from a universal cocone to  $Y$  is

$$
\coprod_ {j \in \operatorname {O b j} (J)} \left(g \circ x _ {j}\right). \tag {3.6}
$$

The morphism

$$
g \circ \left(\coprod_ {j \in \operatorname {O b j} (J)} x _ {j}\right) \tag {3.7}
$$

makes all the triangles

$$
F (j) \xrightarrow [ g \circ x _ {j} ]{\rho_ {j}} \coprod_ {j} F (j) \begin{array}{c} \Bigg \downarrow \\ Y \end{array} \Bigg \downarrow g \circ (\coprod_ {j} x _ {j})
$$

commute. Therefore it is a mediating morphism, which should be unique. Thus, morphisms (3.6) and (3.7) coincide

# 3.6 Existence of Limits

Not all  $J$ -shaped diagrams  $F: J \to \mathcal{A}$  have limits or colimits.

# Definition 3.14

- For a fixed index category  $J$ , if all  $J$ -shaped diagrams in  $\mathcal{A}$  have limits[colimits], category  $\mathcal{A}$  is said to have limits[colimits] of shape  $J$ .  
- If a category  $\mathcal{A}$  have limits [colimits] of shape  $J$  for all small and discrete categories  $J$ , then  $\mathcal{A}$  is said to have products [have coproducts].

- If all  $\bullet \Longrightarrow \bullet$ -shaped diagrams in  $\mathcal{A}$  have limits[colimits], category  $\mathcal{A}$  is said to have equalizers[have coequalizers].  
- If all  $\bullet \geqts \bullet \rightarrow \bullet$ -shaped diagrams have limits, category  $\mathcal{A}$  is said to have pullbacks.  
- If all  $\bullet \to \bullet \geqts \bullet$ -shaped diagrams have colimits, category  $\mathcal{A}$  is said to have pushouts.  
- If a category  $\mathcal{A}$  has limits[colimits] of shape  $J$  for all small categories  $J$ , category  $\mathcal{A}$  is said to be complete[cocomplete].

An often used sufficient condition for a category to have limits is presented below. A little preparation is required for this.

Let  $\mathcal{A}$  be a category that has equalizers, and  $J$  be an index category. We regard  $\mathrm{Obj}(J)$  and  $\mathrm{Mor}(J)$  are both discrete categories. Suppose category  $\mathcal{A}$  has products. There is a universal cone

$$
\begin{array}{c c c} \prod_ {f \in \operatorname {M o r} (J)} F (\operatorname {c o d} (f)) & \\ \pi_ {f} & \pi_ {f ^ {\prime}} \\ F (\operatorname {c o d} (f)) & \dots & F (\operatorname {c o d} (f ^ {\prime})) \end{array} \tag {3.8}
$$

to a diagram  $F \circ \operatorname{cod}$  of shape  $\operatorname{Mor}(J)$ , namely a product indexed by  $f \in \operatorname{Mor}(J)$ . The data structure is presented as follows.

$$
\left(\prod_ {f \in \operatorname {M o r} (J)} F (\operatorname {c o d} (f)), \quad \{\pi_ {f} \} _ {f \in \operatorname {M o r} (J)}, \quad F \circ \operatorname {c o d}\right)
$$

Let us consider another cone to  $F \circ \mathrm{cod}$

$$
\begin{array}{ccc}\prod_{j\in \mathrm{Obj}(J)}F(j) & \\ \hline p_{\mathrm{dom}(f)} & \searrow \\ F(\mathrm{dom}(f)) & F(\mathrm{dom}(f'))\\ F(f)\Big{\downarrow} & \Big{\downarrow}F(f')\\ F(\mathrm{cod}(f)) & \dots \\ & F(\mathrm{cod}(f')) \end{array}
$$

with data structure

$$
\left(\prod_ {j \in \operatorname {O b j} (J)} F (j), \quad \{F (f) \circ p _ {\operatorname {d o m} (f)} \} _ {f \in \operatorname {M o r} (J)}, \quad F \circ \operatorname {c o d}\right),
$$

where  $p_j$ 's are projections accompanying the product  $\prod_{j \in \mathrm{Obj}(J)} F(j)$ . These projections appear in the form of  $p_{\mathrm{dom}(f)}$  in the diagram. It often happens that  $\mathrm{dom}(f_1) = \mathrm{dom}(f_2)$  for a pair  $f_1 \neq f_2$ . So, the same  $p_{\mathrm{dom}(f)}$  may appear repeatedly in the upper half of the diagram. However, this does not cause any inconvenience since the base of the cone is indexed by  $f$ . The universal cone (3.8) gives a unique mediating morphism  $s$  that makes all the squares in the diagram commute.

![](images/60f2fdf00f421f3663f269bf7a9088a97b08afb50a366abfe36040356dbb0608.jpg)

Universality of products allows us to consider the products of morphisms. We often write as

$$
s = \prod_ {f \in \operatorname {M o r} (J)} F (f) \circ p _ {\operatorname {d o m} (f)}.
$$

We consider yet another cone from  $\prod_{j\in \mathrm{Obj}(J)}F(j)$  to  $F\circ$  cod, the base of which is indexed by  $f\in \operatorname {Mor}(J)$

![](images/c9d38481b9b683d41f03c99076190a2772e199caf37548fd098b915ba0059bfe.jpg)

The data structure for this is given as

$$
\left(\prod_ {j \in \operatorname {O b j} (J)} F (j), \quad \{p _ {\operatorname {c o d} (f)} \} _ {f \in \operatorname {M o r} (J)}, \quad F \circ \operatorname {c o d}\right)
$$

It is sometimes the case that  $\operatorname{cod}(f_1) = \operatorname{cod}(f_2)$  for a pair  $f_1 \neq f_2$ , which means that some objects repeatedly appear in the base of the cone. Notice that no trouble is caused since the base is indexed by  $f$ .

There is a unique morphism  $t$  to the universal cone (3.8)

![](images/6ca2bb164cc3a41a5e04740e8c1a9ffe759b2ceea53ef51b084cddee8b0b6894.jpg)

Universality of products allows us to consider the products of morphisms. We often write as

$$
t = \prod_ {f \in \operatorname {M o r} (J)} p _ {\operatorname {c o d} (f)}.
$$

We got two morphisms  $s$  and  $t$

$$
\prod_ {j \in \operatorname {O b j} (J)} F (j) \xrightarrow [ t ]{s} \prod_ {f \in \operatorname {M o r} (J)} F (\operatorname {c o d} (f)). \tag {3.9}
$$

Now, we can formulate the theorem for the existence of limits.

Theorem 3.1 Let  $\mathcal{A}$  be a category with equalizers and products, and  $J$  be an index category. We regard  $\mathrm{Obj}(J)$  and  $\mathrm{Mor}(J)$  as discrete categories, over which we may form products. Under these assumptions, we have an equalizer  $e:K\to \prod_{j\in \mathrm{Obj}(J)}F(j)$  for two morphisms  $s$  and  $t$  in (3.9). The cone from  $K$  to  $F$  obtained by composing  $e$  with projections  $p_j$  's gives a limit for  $F$ . We may write as  $K = \varprojlim F$ . The data structure for the limiting cone is presented as

![](images/248b3d1dfc94d2a76d832ef6b45643d9239856e1c1dc73f8a89393d227434215.jpg)

$$
\left(K, \left\{p _ {j} \circ e \right\} _ {j \in \operatorname {O b j} (J)}, F\right).
$$

Proof Let  $(X, x = \{x_{j}\}_{j \in \mathrm{Obj}(J)}, F)$  be any cone to  $F$ . This cone automatically is a cone to  $F|_{\mathrm{Obj}(J)}$ , where the discrete category  $\mathrm{Obj}(J)$  is considered as a subcategory of  $J$ . Universality of products gives a unique morphism  $x$  in the commutative diagram below.

![](images/e622e5c179bee98bdb83fa6fa3a195457b74bc754e34595380c88ba81629ac21.jpg)

Composing with parallel morphisms  $s$  and  $t$ , we get

$$
X \xrightarrow {x} \prod_ {j \in \operatorname {O b j} (J)} F (j) \xrightarrow [ t ]{s} \prod_ {f \in \operatorname {M o r} (J)} F (\operatorname {c o d} (j)) ,
$$

where  $x = \prod_{j\in \mathrm{Obj}(J)}x_j$

We now show that  $s \circ x = t \circ x$ . Rewriting the LHS, we have

$$
\begin{array}{l} s \circ x = \left(\prod_ {f \in \operatorname {M o r} (J)} F (f) \circ p _ {\operatorname {d o m} (f)}\right) \circ x \\ = \prod_ {f \in \operatorname {M o r} (J)} \left(F (f) \circ p _ {\operatorname {d o m} (f)} \circ x\right) \\ = \prod_ {f \in \operatorname {M o r} (J)} \left(F (f) \circ x _ {\operatorname {d o m} (f)}\right). \\ \end{array}
$$

Line 2 is derived by Proposition 3.5 which claims that limits and composition of a morphism commute. Line 3 is obtained directly from the definition of  $x$ , namely  $p_j \circ x = x_j$  with  $j$  replaced by  $\operatorname{dom}(f)$ .

Rewriting the RHS, we have

$$
\begin{array}{l} t \circ x = \left(\prod_ {f \in \operatorname {M o r} (J)} p _ {\operatorname {c o d} (f)}\right) \circ x \\ = \prod_ {f \in \operatorname {M o r} (J)} \left(p _ {\operatorname {c o d} (f)} \circ x\right) \\ = \prod_ {f \in \operatorname {M o r} (J)} x _ {\operatorname {c o d} (f)}. \\ \end{array}
$$

Line 2 is derived from the fact that limits and composition of a morphism commute. Line 3 is obtained directly from the definition of  $x$ , namely  $p_j \circ x = x_j$  with  $j$  replaced by  $\operatorname{cod}(f)$ .

Note that  $\{x_{j}\}$  is a cone to  $F$ . Then, we see that all the triangles

![](images/688a5f7974d75f61a1ec763f11907ea6545f982f8eec1cd3bd1c36e8588248e1.jpg)

commute. In other words, for all  $f$  we have

$$
F (f) \circ x _ {\operatorname {d o m} (f)} = x _ {\operatorname {c o d} (f)},
$$

which means  $s \circ x = t \circ x$ .

Universality of equalizer  $e$  gives a unique mediating morphism  $u: X \to K$  that makes the diagram

![](images/418998702fa98fd3f0f7124ad09b1572a93ebf8661867fd9f1fd0328329016a2.jpg)

commute. The data  $\{p_j\circ e\}$  gives a universal cone to  $J$  -shaped diagram  $F$  .We have

$$
K = \varprojlim F.
$$

![](images/e9b83e9aa43b0c727b1806a82239b4b58acae39fbcf91db3aaad41189d86684b.jpg)

So much for a formal discussion. Let us do it concretely.

Example 3.17 Let  $J$  be a category given below.

$$
J = (1 \stackrel {f} {\to} 2).
$$

The following two sets

$$
\operatorname {O b j} (J) = \{1, 2 \}
$$

$$
\operatorname {M o r} (J) = \{1 _ {1}, 1 _ {2}, f \}
$$

are considered as discrete categories. We assume existence of products. We have the limiting cone below.

![](images/8bbb99a7b1cc113b9fe5de6cbf70ea53cf619574809ade35e695fa7790ac6595.jpg)

We reindex the base with  $\operatorname{Mor}(J)$ .

$$
\operatorname {c o d} \left(1 _ {1}\right) = 1, \quad \operatorname {c o d} \left(1 _ {2}\right) = \operatorname {c o d} (f) = 2
$$

Projections indexed by  $\operatorname{Mor}(J)$  are  $\mu$ 's below.

$$
\mu_ {1 _ {1}} = p _ {1}, \quad \mu_ {1 _ {2}} = p _ {2}, \quad \mu_ {f} = p _ {2}
$$

We get a cone from  $\prod_{j\in \mathrm{Obj}(J)}F(j) = F(1)\times F(2)$  to  $\operatorname {Mor}(J)$ -shaped diagram  $F\circ \operatorname {cod}$

$$
\begin{array}{c} F (1) \times F (2) \\ \mu_ {1 _ {1}} \\ F (\operatorname {c o d} (1 _ {1})) \end{array} \qquad \begin{array}{c} \mu_ {1 _ {2}} = \mu_ {f} \\ F (\operatorname {c o d} (1 _ {2})) = F (\operatorname {c o d} (f)) \end{array}
$$

We assume a universal cone to  $\operatorname{Mor}(J)$ -shaped diagram  $F \circ \operatorname{cod}$ , which in this case a product:

$$
\prod_ {f \in \operatorname {M o r} (J)} F (\operatorname {c o d} (f)) = F (1) \times F (2) \times F (2).
$$

We have the following.

$$
\begin{array}{c} F (1) \times F (2) \times F (2) \\ \pi_ {1} \\ F (\operatorname {c o d} (1 _ {1})) \end{array} \xrightarrow {\pi_ {f}} \begin{array}{c} F (\operatorname {c o d} (1 _ {2})) = F (\operatorname {c o d} (f)) \end{array}
$$

The mediating morphism  $t$  makes all the triangles in the following diagram commute.

$$
\begin{array}{c} F (1) \times F (2) \\ \mu_ {1 _ {1}} \\ F (1) \times F (2) \times F (2) \\ \pi_ {1} \\ F (\operatorname {c o d} (1 _ {1})) \end{array} \qquad \qquad \begin{array}{c} \mu_ {1 _ {2}} = \mu_ {f} \\ \pi_ {f} \\ \pi_ {2} \\ F (\operatorname {c o d} (1 _ {2})) = F (\operatorname {c o d} (f)) \end{array}
$$

Next, we consider another cone to  $\operatorname{Mor}(J)$ -shaped diagram  $F \circ \operatorname{cod}$

$$
\begin{array}{c} F (1) \times F (2) \\ \downarrow \quad v _ {1 _ {1}} = v _ {f} \\ F (\operatorname {d o m} (1 _ {1})) = F (\operatorname {d o m} (f)) \\ F (1 _ {1}) \Bigg \downarrow \quad F (f) \\ F (\operatorname {c o d} (1 _ {1})) \end{array} \qquad \begin{array}{c} F (1) \times F (2) \\ \downarrow \quad v _ {1 _ {2}} \\ F (\operatorname {d o m} (1 _ {2})) \\ \Bigg \downarrow \quad F (1 _ {2}) \\ F (\operatorname {c o d} (f)) = F (\operatorname {c o d} (1 _ {2})) \end{array}
$$

where  $\nu$ 's are projections accompanying the cone from  $F(1) \times F(2)$  to  $F \circ \operatorname{dom}$  that satisfy

$$
v _ {1 _ {1}} = v _ {f} = p _ {1}, \quad v _ {1 _ {2}} = p _ {2}.
$$

The whole diagram amounts to considering the cone

$$
(F (1) \times F (2), \{F (1 _ {1}) \circ v _ {1 _ {1}}, F (1 _ {2}) \circ v _ {1 _ {2}}, F (f) \circ v _ {f} \}, F \circ \operatorname {c o d}).
$$

The mediating morphism from this cone to the universal cone is obtained as

$$
s: F (1) \times F (2) \to F (1) \times F (2) \times F (2).
$$

Let us revisit a previous Example 3.17. This time we take  $\mathcal{C} = \mathbf{Set}$ . We will realize that limits in  $\mathbf{Set}$  are subsets of a product.

Example 3.18 Let  $J$  be a category

$$
J = (1 \stackrel {f} {\to} 2).
$$

We have

$$
\operatorname {O b j} (J) = \{1, 2 \}
$$

$$
\operatorname {M o r} (J) = \{1 _ {1}, 1 _ {2}, f \}.
$$

We consider a diagram  $F: J \to \mathbf{Set}$  as follows. Its function on objects is given by

$$
F (1) = \{3, 4, 5 \}, \quad F (2) = \{6, 7 \}.
$$

Since  $J$  has only one morphism other than the identities,  $F$ 's function on morphisms is determined by the image of  $f$ . We set

$$
F (f): F (1) \rightarrow F (2)
$$

![](images/c470e85496003501853dd98bdfe011fc9b12d6113ac7c94095a2aab47ffbc3bf.jpg)

We follow the construction in Example 3.17. First, we have

$$
F (\operatorname {c o d} (1 _ {1})) = F (1) = \{3, 4, 5 \}
$$

$$
F (\operatorname {c o d} (1 _ {2})) = F (2) = \{6, 7 \}
$$

$$
F (\operatorname {c o d} (f)) = F (2) = \{6, 7 \}
$$

$$
\prod_ {h \in \operatorname {M o r} (J)} F (\operatorname {c o d} (h)) = \{3, 4, 5 \} \times \{6, 7 \} \times \{6, 7 \}
$$

We construct a mapping  $t$  in the diagram

![](images/af633f390dfa2a38e55c9837e0bedaace10815a063efd793a3934592a5ebe7b9.jpg)

as follows. Notice that the component  $F(2)$  is diagonally duplicated in the codomain.

$$
t: F (1) \times F (2) \longrightarrow F (1) \times F (2) \times F (2)
$$

indexed by 1 and 2 indexed by  $1_{1},1_{2}$  ,and  $f$  
(3,6)  $\longrightarrow$  (3,6,6)  
(3,7)  $\longmapsto (3,7,7)$  
$(4,6)\vdash \rightarrow (4,6,6)$  
$(4,7)\vdash$ $\rightarrow (4,7,7)$  
$(5,6)\vdash$ $\rightarrow (5,6,6)$  
$(5,7)\vdash$ $\rightarrow (5,7,7)$

The correspondence is found in the following way.

- On the left side, list out all the pair from  $F(1) \times F(2)$ . Note that  $F(1)$  and  $F(2)$  are indexed by 1 and 2.  
- On the right side, prepare three columns that are indexed by  $1_{1}, 1_{2}$ , and  $f$ . Now, we have totally five columns indexed by  $1, 2, 1_{1}, 1_{2}, f$  from left.  
- Copy column  $1 = \operatorname{cod}\left( {1}_{1}\right)$  (the first column from left) to column  ${1}_{1}$  (the third column from left).  
- Copy column  $2 = \operatorname{cod}\left( {1}_{2}\right)$  (the second column from left) to column  ${1}_{2}$  (the forth column from left).  
- Copy column  $2 = \operatorname{cod}(f)$  (the second column from left) to column  $f$  (the right-most column).

Construction of  $s$  needs some detour.

![](images/d3f3a64eb6df541e76b2e87af155dc4e12471b6053dddeda1e0922eb1f31c0fc.jpg)

The mapping  $s$  is determined as follows.

indexed by 1 and 2 indexed by  $1_{1},1_{2}$  ,and  $f$

$$
s: F (1) \times F (2) \longrightarrow F (1) \times F (2) \times F (2)
$$

(3,6)  $\rightarrow$  (3,6,6)  
(3,7)  $\longrightarrow$  (3,7,6)  
$(4,6)\vdash$ $\rightarrow (4,6,6)$  
$(4,7)\vdash$ $\succ (4,7,6)$  
$(5,6)\vdash$ $\rightarrow (5,6,7)$  
$(5,7)\vdash \rightarrow (5,7,7)$

This correspondence is found in the following way. Pairs and triplets are vertically lined up. As a whole they may be viewed as five columns lined up from left to right, being indexed by  $1, 2, 1_1, 1_2$ , and  $f$ .

- Columns 1 and 2 (two columns from the left part) list out all elements of  $F(1) \times F(2)$  as pairs.  
- Columns  $1_{1}, 1_{2}$ , and  $f$  (three columns from the right part) are reserved for storing triplets.  
- Column  $1_{1}$  is filled with images of  $F(1_{1}) = 1_{F(1)}$  of the corresponding element in column  $1 = \operatorname{dom}(1_{1})$ . In this case, obtained by simply copying the whole column 1.  
- Column  $1_{2}$  is filled with images of  $F(1_{2}) = 1_{F(2)}$  of the corresponding element in column  $2 = \mathrm{dom}(1_{2})$ . In this case, obtained by simply copying the whole column 2.  
- Column  $f$  is filled with images of  $F(f)$  of the corresponding element in column  $1 = \operatorname{dom}(f)$ . This time, we have to trace exact correspondence by  $F(f)$ .

This completes the construction of  $s$ .

To equalize  $s$  and  $t$ , we line up the images side by side.

by  $t$

by  $s$

(3,6)  $\longmapsto$  (3,6,6)

(3,6,6)

(3,7)  $\longmapsto$  (3,7,7)

(3,7,6)

(4,6)  $\longmapsto$  (4,6,6)

(4,6,6)

(4,7)  $\longmapsto$  (4,7,7)

(4,7,6)

(5,6)  $\longmapsto$  (5,6,6)

(5,6,7)

(5,7)  $\longmapsto$  (5,7,7)

(5,7,7)

Having observed this data, we find that  $e$  is a mapping that embeds

$$
\{(3, 6), (4, 6), (5, 7) \}
$$

to  $\{3,4,5\} \times \{6,7\}$

Haskell code for Example 3.18 is given below.

Listing 3.7 toylimit.hs  
```txt
1 -- Category J  
2 ---- Obj(J) = {1, 2}  
3 data ObjJ = 01 | 02 deriving (Eq, Enum, Show)  
4  
5 ---- Mor(J) = {1_1, 1_2, f}  
6 data MorJ = I1 | I2 | Mf deriving (Eq, Enum, Show)  
7  
8 ---- dom : Mor(J) -> Obj(J)  
9 domJ :: MorJ -> ObjJ  
10 domJ I1 = 01  
11 domJ I2 = 02  
12 domJ Mf = 01  
13  
14 ---- cod : Mor(J) -> Obj(J)  
15 codJ :: MorJ -> ObjJ  
16 codJ I1 = 01  
17 codJ I2 = 02  
18 codJ Mf = 02  
19  
20 -- toy sets  
21 ---- F(1) = {3,4,5}  
22 data F1 = V3 | V4 | V5 deriving (Eq, Show)  
23  
24 ---- F(2) = {6,7}  
25 data F2 = V6 | V7 deriving (Eq, Show)  
26  
27 ---- F(1_1)  
28 fmapI1 :: F1 -> F1  
29 fmapI1 x = x  
30  
31 ---- F(1_2)  
32 fmapI2 :: F2 -> F2  
33 fmapI2 x = x  
34  
35 ---- F(f)  
36 fmapMf :: F1 -> F2  
37 fmapMf V3 = V6  
38 fmapMf V4 = V6  
39 fmapMf V5 = V7  
40  
41 -- t  
42 t :: (F1,F2) -> (F1,F2,F2)  
43 t (x,y) = (x,y,y)  
44  
45 -- s  
46 s :: (F1,F2) -> (F1,F2,F2)  
47 s (x,y) = (fmapI1 x, fmapI2 y, fmapMf x)  
48  
49 -- equalizer  
50 objK = [(x,y) | x <- [V3,V4,V5], y <- [V6,V7], s (x,y) == t (x,y)]
```

Lines 3 and 6 define types for objects and morphisms of  $J$ .

Lines 8-18 define the dom and cod functions.

Lines 20-25 define  $F(1)$  and  $F(2)$  as types.

Lines 27-39 define the function on morphisms of functor  $F$ .

Lines 41-47 define morphisms  $s$  and  $t$ .

Lines 49-51 define an object  $K$  for the equalizer  $e:K\to F(1)\times F(2)$

A test can be done as follows.

\*Main>objK [(V3,V6),(V4,V6),(V5,V7)]

Let us reflect on what cones are in category Set before we proceed to the next example. Given a  $J$ -shaped diagram  $F: J \to \mathbf{Set}$ , all  $F(j)$ 's are sets. So, we can talk about their elements. Consider a cone from  $A$  to  $F$ . We require the following diagram to commute.

![](images/9054ff24f4e469cb2864145766ae3c8990011938e9752449682045e32a9a6415.jpg)

This means that  $(F(f))(p_{j}(a)) = p_{k}(a)$  for all  $a\in A$  and  $f:j\to k$

Example 3.19 Category Set has products, which are Cartesian products. Category Set also has equalizers. An equalizer of two mappings  $f, g: A \to B$  can be defined by a subset  $K \subset A$  such that

$$
K = \{x \in A \mid f (x) = g (x) \}
$$

and its embedding  $e:K\to A$

Since Set has products and equalizers, we can claim, by Theorem 3.1, that Set has limits.

Limits in Set appear in the following manner. Let  $F: J \to \mathbf{Set}$  be a  $J$ -shaped diagram. We present an element of the Cartesian product  $\prod_{j \in \mathrm{Obj}(J)} F(j)$  as  $(a_j)_{j \in \mathrm{Obj}(J)}$ . A subset defined as the solution set of the system of equations

$$
(F (f)) (a _ {j}) = a _ {k} \quad (f \in \operatorname {M o r} (J)),
$$

where unknowns are indexed by  $\mathrm{Obj}(J)$  and equations are indexed by  $\mathrm{Mor}(J)$ .

# 3.7 Existence of Colimits

An often used sufficient condition for a category to have colimits is presented below. The dual of Theorem 3.1 will be given. It is often said that the dual of some theorem

can be simply proved by reversing the arrows. When it comes to calculate examples in category Set, unfortunately, this is not the case. This is because there is a significant asymmetry in Set. Just think about the condition for a correspondence to be a function. There are many things to take care.

We repeat the same preparation as for the limit.

Let  $\mathcal{A}$  be a category that has coequalizers, and  $J$  be an index category. We regard  $\operatorname{Obj}(J)$  and  $\operatorname{Mor}(J)$  are both discrete categories. Suppose category  $\mathcal{A}$  has coproducts. There is a universal cocone

![](images/7d12e551a2629e4d297c51336f03e395782ee4e2264f11c965a38f912e18b53c.jpg)

from a diagram  $F \circ \operatorname{dom} : \operatorname{Mor}(J) \to \mathcal{A}$  of shape  $\operatorname{Mor}(J)$ , namely a coproduct indexed by  $f \in \operatorname{Mor}(J)$ . The data structure is presented as follows.

$$
\left(F \circ \operatorname {d o m}, \quad \{\pi_ {f} \} _ {f \in \operatorname {M o r} (J)}, \coprod_ {f \in \operatorname {M o r} (J)} F (\operatorname {d o m} (f))\right),
$$

where  $\pi_f$  's are coprojections.

Let us consider another cocone from  $F \circ \mathrm{dom}$

![](images/852c2bac1bf14ee3de7e060d95c15fab0223c14c97f9fb1ccbeb444c8fee7210.jpg)

with data structure

$$
\left(F \circ \operatorname {d o m}, \quad \{p _ {\operatorname {c o d} (f)} \circ F (f) \} _ {f \in \operatorname {M o r} (J)}, \coprod_ {j \in \operatorname {O b j} (J)} F (j)\right),
$$

where  $p_j$ 's are coprojections accompanying the coproduct  $\coprod_{j \in \mathrm{Obj}(J)} F(j)$ . These coprojections appear in the form of  $p_{\mathrm{cod}(f)}$  in the diagram. It often happens that  $\operatorname{cod}(f_1) = \operatorname{cod}(f_2)$  for a pair  $f_1 \neq f_2$ . So, the same  $p_{\mathrm{cod}(f)}$  may appear repeatedly in the lower half of the diagram. However, this does not cause any inconvenience since the base of the cocone is indexed by  $f$ . Therefore, there is a unique mediating morphism  $s$

![](images/7eac54d1aa493451c3fac91bbf30e7b28db2d118e18ff5ff6beb6905fdcd4213.jpg)

We may write

$$
s = \coprod_ {f \in \operatorname {M o r} (J)} p _ {\operatorname {c o d} (f)} \circ F (f).
$$

We consider yet another cocone from  $\operatorname{Mor}(J)$ -shaped diagram  $F \circ$  dom to  $\coprod_{j \operatorname{Obj}(J)} F(j)$ :

![](images/98c1a3a569a4fc161948becf498b7768b1a5be5a7ad351fa1599a14c0dcf7deb.jpg)

The data structure is given by

$$
\left(F \circ \operatorname {d o m}, \quad \{p _ {\operatorname {d o m} (f)} \} _ {f \in \operatorname {M o r} (J)}, \coprod_ {j \in \operatorname {O b j} (J)} F (j)\right).
$$

This cocone has a base indexed by  $f \in \operatorname{Mor}(J)$ . Therefore, there is a unique mediating morphism  $t$ :

![](images/ad13f36eac14161a7e9ffa8423a9e1c85365ace311dc5566ab029534ad3ffba0.jpg)

We may write

$$
t = \coprod_ {f \in \operatorname {M o r} (J)} p _ {\operatorname {d o m} (f)}.
$$

So much for the construction of the parallel morphisms  $s$  and  $t$ :

$$
\coprod_ {f \in \operatorname {M o r} (J)} F (\operatorname {d o m} (f)) \xrightarrow [ t ]{s} \coprod_ {j \in \operatorname {O b j} (J)} F (j) \tag {3.10}
$$

Now, it is time to state the theorem.

Theorem 3.2 Let  $\mathcal{A}$  be a category with coequalizers and coproducts, and  $J$  be an index category. We regard  $\mathrm{Obj}(J)$  and  $\mathrm{Mor}(J)$  as discrete categories, over which we may form coproducts. Under these assumptions, we have a coequalizer  $e: \coprod_{j \in \mathrm{Obj}(J)} F(j) \to K$  for two morphisms  $s$  and  $t$  in (3.10). Then, gives a cocone

![](images/ad89e1cf476d8a00af945fe9fc6e01fcc7dbe478e2cb631483754b5e6967e7ec.jpg)  
$(F,\{e\circ p_j\}_{j\in \mathrm{Ob}(J)},K)$

that is a limiting cocone of the  $J$ -shaped diagram  $F: J \to \mathcal{A}$ . We may write  $K = \varinjlim F$ .

Proof Let  $(F, \{x_j\}, X)$  be a cocone from  $F$  to  $X$ . Universality of coproducts gives a unique morphism  $x = \coprod_{j \in \mathrm{Obj}(J)} x_j$  that makes the following diagram commute.

![](images/2f49b3c63ec0b0d6776ccc796b45b7faa11e7a7620bdd05d5e79e82b9cfb4178.jpg)

Composing with  $s$  and  $t$ , we have the following diagram.

$$
\coprod_ {f \in \operatorname {M o r} (J)} F (\operatorname {d o m} (f)) \xrightarrow [ t ]{s} \coprod_ {j \in \operatorname {O b j} (J)} F (j) \xrightarrow {x} X
$$

We want to show that  $x \circ s = x \circ t$ . First, we rewrite the LHS.

$$
\begin{array}{l} x \circ s = x \circ \left(\coprod_ {f \in \operatorname {M o r} (J)} p _ {\operatorname {c o d} (f)} \circ F (f)\right) \\ = \coprod_ {f \in \operatorname {M o r} (J)} \left(x \circ p _ {\operatorname {c o d} (f)} \circ F (f)\right) \\ = \coprod_ {f \in \operatorname {M o r} (J)} \left(x _ {\operatorname {c o d} (f)} \circ F (f)\right) \\ \end{array}
$$

Line 2 is obtained by the exchange of colimit and composition by a morphism. This exchange is not trivial (Proposition 3.6). Line 3 is obtained by the definition of  $x$ , namely  $x \circ p_j = x_j$ , where  $j$  is replaced by  $\operatorname{cod}(f)$ .

Next, we rewrite the RHS.

$$
\begin{array}{l} x \circ t = x \circ \left(\coprod_ {f \in \operatorname {M o r} (J)} p _ {\operatorname {d o m} (f)}\right) \\ = \coprod_ {f \in \operatorname {M o r} (J)} \left(x \circ p _ {\operatorname {d o m} (f)}\right) \\ = \coprod_ {f \in \operatorname {M o r} (J)} x _ {\operatorname {d o m} (f)} \\ \end{array}
$$

Line 2 is obtained by the exchange of colimit and composition by a morphism. Line 3 is obtained by the definition of  $x$ . Since  $x_{j}$ 's constitute a cocone from  $F$ ,

$$
F (\operatorname {d o m} (f)) \xrightarrow [ X ]{F (f)} F (\operatorname {c o d} (f))
$$

commutes for all  $f$ 's. Thus, we have

$$
x _ {\operatorname {c o d} (f)} \circ F (f) = x _ {\operatorname {d o m} (f)}
$$

for all  $f \in \operatorname{Mor}(J)$ . We can conclude that  $x \circ s = x \circ t$ . Universality of coequalizer  $e$  gives us a unique mediating morphism  $u: K \to X$  as in the following diagram.

$$
\coprod_ {f \in \operatorname {M o r} (J)} F (\operatorname {d o m} (f)) \xrightarrow [ t ]{s} \coprod_ {j \in \operatorname {O b j} (J)} F (j) \xrightarrow {e} K
$$

This means that  $\{e\circ p_j\}$  is a universal cocone. We may write  $K = \varinjlim F$

Cocones in category Set can be discussed in a similar way to cones. Given a  $J$ -shaped diagram  $F: J \to \mathbf{Set}$ , we can talk about elements of  $F(j)$ . A cocone to  $A$  requires the following triangles to commute.

$$
F (j) \xrightarrow [ p _ {j} \searrow ]{F (f)} F (k)
$$

This amounts to taking the union of a family of sets  $\{F(j)\}$  pasting  $x_{j} \in F(j)$  and  $x_{k} = F(f)(x_{j}) \in F(k)$ . With this in mind, we proceed to a discussion below.

Example 3.20 Let  $J$  be a category

$$
J = (1 \stackrel {f} {\to} 2).
$$

We have

$$
\operatorname {O b j} (J) = \{1, 2 \}
$$

$$
\operatorname {M o r} (J) = \{1 _ {1}, 1 _ {2}, f \}.
$$

We consider a diagram  $F: J \to \mathbf{Set}$  as follows. Its function on objects is given by

$$
F (1) = \{3, 4, 5, 6 \}, \quad F (2) = \{7, 8, 9 \}.
$$

Since  $J$  has only one morphism other than the identities,  $F$ 's function on morphisms is determined by the image of  $f$ . We set

$$
F (f): F (1) \rightarrow F (2)
$$

$$
\begin{array}{c} 3 \longmapsto 7 \\ 4 \longmapsto 8 \end{array}
$$

$$
\begin{array}{c} 5 \longmapsto 9 \\ 6 \longmapsto \end{array}
$$

We have the following.

$$
F (\operatorname {d o m} (1 _ {1})) = F (1) = \{3, 4, 5, 6 \}
$$

$$
F (\operatorname {d o m} (1 _ {2})) = F (2) = \{7, 8, 9 \}
$$

$$
F (\operatorname {d o m} (f)) = F (1) = \{3, 4, 5, 6 \}
$$

$$
\coprod_ {f \in \operatorname {M o r} (J)} F (\operatorname {d o m} (f)) = \{3, 4, 5, 6 \} \sqcup \{7, 8, 9 \} \sqcup \{\mathbf {3}, \mathbf {4}, \mathbf {5}, \mathbf {6} \}
$$

Operator  $\sqcup$  denotes a disjoint union. To avoid overlapping, we use bold face figures in the last operand.

Morphism  $t$  is a mapping. We write down the whole correspondence below.

![](images/2f2e7c9b7706c5c47f01bfb47408d43433062cd4768fe4451ab09dcc4c85698f.jpg)

Likewise, morphism  $s$  is described as follows.

![](images/fd3124d26b4a6969d7d3d6470409e20de53835e8979bd9d25e407e16e99d9072.jpg)

To get a coequalizer for  $s$  and  $t$ , we have to calculate the quotient  $(F(1) \sqcup F(2)) / \sim$ , where  $\sim$  is an equivalence relation in  $F(1) \sqcup F(2)$ , which is the reflexive, symmetric, transitive closure of a relation  $\sim^0$  defined as follows.

Let  $b, b' \in F(1) \sqcup F(2)$ .

$$
b \sim^ {0} b ^ {\prime} \stackrel {\text {d e f}} {\Longleftrightarrow} \exists a \in F (1) \sqcup F (2) \sqcup F (1); \quad b = s (a) \text {a n d} b ^ {\prime} = t (a)
$$

Refer to the sample code below for an algorithm to collect equivalence classes of  $\sim$ . The result of calculation is

$$
\{\{3, 4, 7 \}, \{5, 6, 9 \}, \{8 \} \}.
$$

The coequalizer  $e$  is a projection of the quotient.

Listing 3.8 toycolimit.hs  
```haskell
1 import Coequalizer  
2  
3 -- Category J  
4 ---- Obj(J) = {1, 2}  
5 data ObjJ = 01 | 02 deriving (Eq, Enum, Show)  
6  
7 --- Mor(J) = {1_1, 1_2, f}  
8 data MorJ = I1 | I2 | Mf deriving (Eq, Enum, Show)  
9  
10 --- dom : Mor(J) -> Obj(J)  
11 domJ :: MorJ -> ObjJ  
12 domJ I1 = 01  
13 domJ I2 = 02  
14 domJ Mf = 01  
15  
16 --- cod : Mor(J) -> Obj(J)  
17 codJ :: MorJ -> ObjJ  
18 codJ I1 = 01  
19 codJ I2 = 02  
20 codJ Mf = 02  
21  
22 --- toy sets  
23 --- F(1) = {3,4,5,6}  
24 data F1 = V3 | V4 | V5 | V6 deriving (Eq, Show)  
25  
26 --- F(2) = {7,8,9}  
27 data F2 = V7 | V8 | V9 deriving (Eq, Show)  
28  
29 --- F(1_1)  
30 fmapI1 :: F1 -> F1  
31 fmapI1 x = x  
32  
33 --- F(1_2)  
34 fmapI2 :: F2 -> F2  
35 fmapI2 x = x  
36
```

```haskell
37 ---- F(f)   
38 fmapMf :: F1 -> F2   
39 fmapMf V3 = V7   
40 fmapMf V4 = V7   
41 fmapMf V5 = V9   
42 fmapMf V6 = V9   
43   
44 -- F(1) + F(2) + F(1) -- disjoint union   
45 data F121 = P3 | P4 | P5 | P6   
46 | Q7 | Q8 | Q9   
47 | R3 | R4 | R5 | R6   
48 deriving (Eq, Enum, Show)   
49   
50 -- coprojections to F(1)+F(2)+F(1)   
51 sigma1 :: F1 -> F121   
52 sigma1 V3 = P3   
53 sigma1 V4 = P4   
54 sigma1 V5 = P5   
55 sigma1 V6 = P6   
56   
57 sigma2 :: F2 -> F121   
58 sigma2 V7 = Q7   
59 sigma2 V8 = Q8   
60 sigma2 V9 = Q9   
61   
62 sigma'f :: F1 -> F121   
63 sigma'f V3 = R3   
64 sigma'f V4 = R4   
65 sigma'f V5 = R5   
66 sigma'f V6 = R6   
67   
68 -- partial inverses to coprojections   
69 sigmai :: F121 -> F1   
70 sigmai P3 = V3   
71 sigmai P4 = V4   
72 sigmai P5 = V5   
73 sigmai P6 = V6   
74   
75 sigma2i :: F121 -> F2   
76 sigma2i Q7 = V7   
77 sigma2i Q8 = V8   
78 sigma2i Q9 = V9   
79   
80 sigma'fi :: F121 -> F1   
81 sigma'fi R3 = V3   
82 sigma'fi R4 = V4   
83 sigma'fi R5 = V5   
84 sigma'fi R6 = V6   
85   
86 -- F(1) + F(2) -- disjoint union   
87 data F12 = S3 | S4 | S5 | S6 | T7 | T8 | T9   
88 deriving (Eq, Enum, Show)   
89   
90 -- coprojections to F(1)+F(2)   
91 rho0:: F1 -> F12
```

```txt
92 rho1 V3 = S3  
93 rho1 V4 = S4  
94 rho1 V5 = S5  
95 rho1 V6 = S6  
96  
97 rho2 :: F2 -> F12  
98 rho2 V7 = T7  
99 rho2 V8 = T8  
100 rho2 V9 = T9  
101  
102 -- t: F(1) + F(2) + F(1) -> F(1) + F(2)  
103 t :: F121 -> F12  
104 t x  
105 | x 'elem' [P3 .. P6] = rho1 (sigma1i x)  
106 | x 'elem' [Q7 .. Q9] = rho2 (sigma2i x)  
107 | x 'elem' [R3 .. R6] = rho1 (sigma'fi x)  
108  
109 {- suggested test for t  
110 map t [P3 .. R6]  
111 -}  
112  
113 -- s: F(1) + F(2) + F(1) -> F(1) + F(2)  
114 s :: F121 -> F12  
115 s x  
116 | x 'elem' [P3 .. P6] = rho1 (fmapI1 (sigma1i x))  
117 | x 'elem' [Q7 .. Q9] = rho2 (fmapI2 (sigma2i x))  
118 | x 'elem' [R3 .. R6] = rho2 (fmapMf (sigma'fi x))  
119  
120 {- suggested test for s  
121 map s [P3 .. R6]  
122 -}  
123  
124 {- do it  
125 rel = coequate s t [P3 .. R6]  
126  
127 partition rel [S3 .. T9]  
128 -}
```

Line 1 imports a helper module Listing 3.6.

All the lines to Line 20 define an index category  $J$ .

Lines 22-42 define a diagram  $F: J \to \mathbf{Set}$ .

Lines 44-84 define

$$
\coprod_ {f \in \operatorname {M o r} (J)} F (\operatorname {d o m} (f)) = F (1 _ {1}) \sqcup F (1 _ {2}) \sqcup F (f)
$$

Especially, lines 50-66 define the coprojections

$$
\sigma_ {1 _ {1}}, \quad \sigma_ {1 _ {2}}, \quad \sigma_ {f}.
$$

Lines 68-84 define inverse partial functions of coprojections:

$$
\sigma_ {1 _ {1}} ^ {- 1}, \quad \sigma_ {1 _ {2}} ^ {- 1}, \quad \sigma_ {f} ^ {- 1}.
$$

Lines 86-100 define

$$
\coprod_ {j \in \mathrm {O b j} (J)} F (j) = F (1) \sqcup F (1).
$$

Especially lines 90-100 define coprojections

$$
\begin{array}{c c} \rho_ {1}, & \rho_ {2}. \end{array}
$$

Lines 102-107 define

$$
t: \coprod_ {f \in \operatorname {M o r} (J)} F (\operatorname {d o m} (f)) \to \coprod_ {j \in J} F (j).
$$

Lines 113-118 define  $s$  in a similar manner.

The tests for  $t$  and  $s$  can be done as follows.

```javascript
\*Main>map t[P3..R6] [S3,S4,S5,S6,T7,T8,T9,S3,S4,S5,S6] \*Main>map s[P3..R6] [S3,S4,S5,S6,T7,T8,T9,T7,T7,T9,T9]
```

Using the imported function coequate, we can calculate the quotient to coequate  $s$  and  $t$  as follows.

```txt
\*Main>rel  $=$  coequate s t[P3..R6] \*Main> partition rel [S3..T9] [[T8],[S6,T9,S5],[S4,T7,S3]]
```

We sum up the previous examples.

Example 3.21 Category Set has coproducts and coequalizers. A coproduct is a disjoint union, where elements of those sets that are to be joined are tagged so that tags indicate from which set it comes from. That's why it is called a tagged union.

Having coproducts and coequalizers, category Set has colimits. See Theorem 3.2.

Colimits can be constructed as follows. Given a  $J$ -shaped diagram  $F: J \to \mathbf{Set}$ , we first form a disjoint union  $\coprod_{j \in \mathrm{Obj}(J)} F(j)$ . Then, take the quotient by an equivalence relation  $\sim$  and get

$$
L = \coprod_ {j \in \mathrm {O b j} (J)} F (j) / \sim
$$

that is an apex of a cocone. Let  $\pi$  be the projection to the quotient. The relation  $\sim$  is the equivalence closure of  $\sim^0$  defined as follows. For  $b, b' \in \coprod_{j \in \mathrm{Obj}(J)} F(j)$

$$
b \sim^ {0} b ^ {\prime} \stackrel {\mathrm {d e f}} {\Longleftrightarrow} \exists (f: j \rightarrow k) \in \operatorname {M o r} (J); \exists a \in F (j); b = F (f) (\rho_ {j} (a)) \text {a n d} b ^ {\prime} = \rho_ {j} (a)
$$

A universal cocone if given as

$$
\left(F, \quad \{\pi \circ \rho_ {j} \} _ {j \in \operatorname {O b j} (J)}, \coprod_ {j \in \operatorname {O b j} (J)} F (j) / \sim\right).
$$

# Functors and Limits

4

Functors map diagrams to diagrams and cones to cones. We are naturally tempted to ask if the image of a limiting cone is also a limiting cone in the target category. We first study some very small examples in which the answers to this question are either yes or no depending on the functor in question. Then, we will study the Hom functors that guarantee the positive answers for all limiting cones.

Suppose a category  $\mathcal{A}$  has both products and coproducts. A natural question to pose is whether the following isomorphism exists:

$$
\mathscr {A} (A, B \times C) \simeq \mathscr {A} (A, B) \times \mathscr {A} (A, C).
$$

If the answer is yes, we may say that the functor  $\mathcal{A}(A, -)$  preserves products. More specifically, functor  $\mathcal{A}(A, -)$  maps products to products.

We pose another question: if

$$
\mathcal {A} (A \sqcup B, C) \simeq \mathcal {A} (A, C) \times \mathcal {A} (B, C)
$$

holds. If the answer is positive, we may say that functor  $\mathcal{A}(-,C)$  preserves coproducts. But, note that the functor maps coproducts to products due to its variance, namely the functor is contravariant.

We study some sufficient conditions for the preservation of limits in general.

# 4.1 Functors Map Cones to Cones

We fix an index category  $J$  and a  $J$ -shaped diagram  $D: J \to \mathcal{A}$ . Given a functor  $F: \mathcal{A} \to \mathcal{B}$  and its composite with  $D$ , and get another  $J$ -shaped diagram  $F \circ D: J \to \mathcal{B}$ .

Further, we see that cones from  $A$  to  $D$  are mapped to cones from  $F(A)$  to  $F\circ D$

![](images/e8c4510e9fad2f649b7fcf5297db5e271120b7d8d5bc163ef23992cf9b784ee7.jpg)

In the same way, we see that cones from  $D$  to  $A$  are mapped to cones from  $F \circ D$  to  $F(A)$ .

![](images/a60788d2985d92346210e19def598cb7f96c983a6e5f47dff2b27ec6771d43ba.jpg)

Definition 4.1 A functor  $F: \mathcal{A} \to \mathcal{B}$  is said to preserve limits of  $J$ -shaped diagrams if, for all  $J$ -shaped diagrams  $D: J \to \mathcal{A}$  that have a limit  $\varprojlim D$ , there exists  $\varprojlim (F \circ D)$  and an isomorphism

$$
F (\varprojlim D) \simeq \varprojlim (F \circ D).
$$

A functor  $F: \mathcal{A} \to \mathcal{B}$  is said to preserve colimits of  $J$ -shaped diagrams if, for all  $J$ -shaped diagrams  $D: J \to \mathcal{A}$  that have a colimit  $\varinjlim D$ , there exists  $\varinjlim (F \circ D)$  and an isomorphism

$$
F (\varinjlim D) \simeq \varinjlim (F \circ D).
$$

Example 4.1 There are cases in which  $\varprojlim(F\circ D)$  does not exist even though  $\varprojlim D$  exists. Let  $J$  be a discrete category with two objects.

![](images/010a62b27b147da624d9493c6b515430f4b5b8222802198e9dcf8578e58e8366.jpg)

Arrows  $\Rightarrow$  constitute a limiting cone in  $\mathcal{A}$ , but the diagram  $F \circ D$  has no limits in  $\mathcal{B}$ .

Example 4.2 There are cases in which

$$
F (\varprojlim D) \simeq \varprojlim (F \circ D)
$$

does not hold even though both  $\varprojlim D$  and  $\varprojlim (F\circ D)$  exist. Let  $J$  be a discrete category with two objects.

![](images/0ac58e021ebac493b4e07bcb6edb9af4dcd2807076652a54f2292fc76179348d.jpg)

Arrows  $\Rightarrow$  in category  $\mathcal{A}$  constitute a limiting cone. Arrows  $\Rightarrow$  in category  $\mathcal{B}$  also constitute a limiting cone. However, the latter is not isomorphic to the functor image of the former. Note that we assumed, in the drawing above, the functor maps objects and morphisms in the left part to those at the same locations on the right.

Example 4.3 If we reverse all the arrows in the previous Examples 4.1 and 4.2, we get examples of colimits that may fail to be preserved.

# 4.2 Hom Functors and Limits

In this section, we fix a locally small category  $\mathcal{A}$ . The Hom functor is a functor in two variables.

$$
\mathcal {A} (-, -): \mathcal {A} ^ {\mathrm {o p}} \times \mathcal {A} \rightarrow \mathbf {S e t}.
$$

We fix the first argument and get a covariant functor

$$
\mathcal {A} (A, -): \mathcal {A} \rightarrow \mathbf {S e t},
$$

which turns out to preserve limits.

Theorem 4.1 Let  $J$  be an index category and  $\mathcal{A}$  a locally small category. If a  $J$ -shaped diagram  $D: J \to \mathcal{A}$  has a limit, then  $J$ -shaped diagram  $\mathcal{A}(A, -) \circ D$  also has a limit. Further, we have a natural isomorphism:

$$
\mathscr {A} (A, \varprojlim D) \simeq \varprojlim (\mathscr {A} (A, -) \circ D). \tag {4.1}
$$

Remark 4.1 Equation (4.1) is often written as

$$
\mathcal {A} (A, \varprojlim_ {j} D (j)) \simeq \varprojlim_ {j} \mathcal {A} (A, D (j)),
$$

making the indexing process explicitly. In the literature, we often encounter presentations such as

$$
\operatorname {H o m} _ {\mathcal {A}} (A, \varprojlim_ {j} D (j)) \simeq \varprojlim_ {j} \operatorname {H o m} _ {\mathcal {A}} (A, D (j)).
$$

Before undertaking the proof, we examine the situation in depth. The  $J$ -shaped diagram  $D: J \to \mathcal{A}$  and its composite with the functor  $\mathcal{A}(A, -): \mathcal{A} \to \mathbf{Set}$  yields another  $J$ -shaped diagram:

$$
J \xrightarrow {D} \mathscr {A} \xrightarrow {\mathscr {A} (A , -)} \mathbf {S e t}
$$

$$
\begin{array}{c} j \longmapsto D (j) \longmapsto \mathcal {A} (A, D (j)) \\ f \Big {\downarrow} \qquad \qquad \qquad \Big {\downarrow} D (f) \qquad \qquad \Big {\downarrow} D (f) \circ - \\ k \longmapsto D (k) \longmapsto \mathcal {A} (A, D (k)). \end{array}
$$

This way, we get a functor  $\mathcal{A}(A, -) \circ D: J \to \mathbf{Set}$ . We consider the following two cones:

![](images/4c0cf7c9572f5558208d71344748d9c26c045382f7280be868fe14f5085a6d4d.jpg)

![](images/11bd65533a10829e6803e5d68937b857870ab163e35dbceab6a72811bb2644b6.jpg)

Let the left diagram be a limiting cone. We will show the right diagram is also a limiting cone.

If we want to claim the naturality of the correspondence, the following formulation is convenient. However, note that the discussion will be slightly restricted to the situation where all the  $J$ -shaped diagrams in  $\mathcal{A}$  have limits.

- We define limits  $\varprojlim$  as a functor. We know that limits are unique up to isomorphisms. This means they are not unique. We choose a representative from each isomorphism class, using the axiom of choice. We can extend the so-obtained function on objects to function on morphisms. See Sect. 4.5 for details.  
- We define a functor  $\mathcal{A}^{\mathrm{op}} \times [J, \mathcal{A}] \to \mathbf{Set}$  that takes a limit first and then applies Hom as follows:

$$
\mathcal {A} ^ {\mathrm {o p}} \times [ J, \mathcal {A} ] \xrightarrow {\text {I d} \times \varprojlim} \mathcal {A} ^ {\mathrm {o p}} \times \mathcal {A} \xrightarrow {\text {H o m}} \mathbf {S e t}
$$

$$
(A, D) \longmapsto (A, \varprojlim D) \longmapsto \mathcal {A} (A, \varprojlim D).
$$

- We define a functor  $\mathcal{A}^{\mathrm{op}} \times [J, \mathcal{A}] \to \mathbf{Set}$  that creates a  $J$ -shaped diagram first, and then applies the limit functor as follows:

$$
\mathcal {A} ^ {\mathrm {o p}} \times [ J, \mathcal {A} ] \xrightarrow {\lim  _ {\leftarrow}} [ J, \mathbf {S e t} ] \xrightarrow {\underset {\leftarrow} {\lim  }} \mathbf {S e t}
$$

$$
(A, D) \longmapsto \mathcal {A} (A, -) \circ D \longmapsto \varprojlim (\mathcal {A} (A, -) \circ D).
$$

- We define a natural isomorphism between the two functors above. To be more specific, we examine how the outputs change under the influence of morphisms  $f \in \mathcal{A}(A, A')$  and  $\alpha \in [J, \mathcal{A}](D, D')$ . For example, the latter functor needs calculation with the following morphisms at its first step.

$$
\begin{array}{c c c c} A & \mathcal {A} (A, -) \circ D & D & \mathcal {A} (A, -) \circ D \\ f \Bigg {\downarrow} & \Bigg {\uparrow} \mathcal {A} (f, -) \circ D & \alpha \Bigg {\downarrow} & \Bigg {\downarrow} \mathcal {A} (A, \alpha) \\ A ^ {\prime} & \mathcal {A} (A ^ {\prime}, -) \circ D & D ^ {\prime} & \mathcal {A} (A, -) \circ D \end{array}
$$

In the above diagrams, we adopt the convention of drawing for contravariant functors. See Remark 4.1.

# Proof (Theorem 4.1)

We leave the naturality proof to the reader. Arguments similar to those in Chap. 7 will do.

Universality of limits gives

$$
\mathcal {A} (A, \varprojlim D) \simeq \operatorname {C o n e s} (A, D). \tag {4.2}
$$

This is the definition of limits itself. See Remark 3.1.

Since  $\varprojlim (\mathcal{A}(A, -) \circ D)$  is a limit in  $\mathbf{Set}$ , its existence is guaranteed by Theorem 3.1 and an argument in Example 3.19. All the objects involved can be studied using their elements. Let  $x$  be an element of  $\varprojlim (\mathcal{A}(A, -) \circ D)$ . A limiting cone in  $\mathbf{Set}$  can be seen as a set of cones from a point to the base:

$$
x = \quad p _ {j} \xrightarrow {\begin{array}{c} \operatorname {c o n s t} _ {p _ {j}} \\ D (f) \circ - \end{array} } p _ {k}
$$

$$
\mathscr {A} (A, D (j)) \xrightarrow [ \mathscr {A} (A , D (f)) ]{} \mathscr {A} (A, D (k)),
$$

where  $\mathrm{const}_{p_j}$  is a function from a singleton set  $\{*\}$  to  $\mathcal{A}(A, D(j))$  that has a single value  $p_j$ . The data representation of this cone is

$$
\left(\{\ast \}, \left\{\operatorname {c o n s t} _ {p _ {j}} \right\} _ {j \in \operatorname {O b j} (J)}, \mathcal {A} (A, -) \circ D\right).
$$

Such a cone is in one-to-one correspondence with  $(\{p_j\}, D)$ , an element of Cones  $(A, D)$ . Thus, we have

$$
\operatorname {C o n e s} (A, D) = \varprojlim (\mathscr {A} (A, -) \circ D).
$$

Combining this equation and (4.2), we get the conclusion.

# 4.3 Hom Functors and Colimits

We fix a locally small category  $\mathcal{A}$ . The Hom functor is a functor in two variables.

$$
\mathcal {A} (-, -): \mathcal {A} ^ {\mathrm {o p}} \times \mathcal {A} \rightarrow \mathbf {S e t}
$$

We fix the second argument to get a contravariant functor

$$
\mathscr {A} (-, A): \mathscr {A} ^ {\mathrm {o p}} \rightarrow \mathbf {S e t},
$$

which turns out to preserve limits, but due to contravariance both limits and colimits play the roles.

Theorem 4.2 Let  $J$  be an index category and  $\mathcal{A}$  a locally small category. If a  $J$ -shaped diagram  $D: J \to \mathcal{A}$  has a colimit, then  $J$ -shaped diagram  $\mathcal{A}(-, A) \circ D$  also has a limit. Further, we have a natural isomorphism:

$$
\mathscr {A} (\varinjlim D, A) \simeq \varprojlim (\mathscr {A} (-, A) \circ D). \tag {4.3}
$$

Remark 4.2 We cannot compose  $\mathcal{A}(-, A): \mathcal{A}^{\mathrm{op}} \to \mathbf{Set}$  and  $D: J \to \mathcal{A}$  as they are. Taking the opposites  $D: J^{\mathrm{op}} \to \mathcal{A}^{\mathrm{op}}$  solves the problem. We can compose two functors as follows:

$$
J ^ {\mathrm {o p}} \xrightarrow {D} \mathcal {A} ^ {\mathrm {o p}} \xrightarrow {\mathcal {A} (- , A)} \mathbf {S e t}.
$$

We get a diagram that appears in the RHS of Eq. (4.3).

Before undertaking the proof, we examine the situation in depth. The  $J$ -shaped diagram  $D: J^{\mathrm{op}} \to \mathcal{A}^{\mathrm{op}}$  and its composite with the functor  $\mathcal{A}(-, A): \mathcal{A}^{\mathrm{op}} \to \mathbf{Set}$  yields another  $J$ -shaped diagram:

$$
J ^ {\mathrm {o p}} \xrightarrow {D} \mathscr {A} ^ {\mathrm {o p}} \xrightarrow {\mathscr {A} (- , A)} \mathbf {S e t}
$$

$$
\begin{array}{c} j \longmapsto D (j) \longmapsto \mathcal {A} (D (j), A) \\ f \Big {\downarrow} \qquad \qquad \qquad \Big {\downarrow} D (f) \qquad \qquad \uparrow - \circ D (f) \\ k \longmapsto D (k) \longmapsto \mathcal {A} (D (k), A). \end{array}
$$

This way, we get a functor  $\mathcal{A}(-, A) \circ D: J^{\mathrm{op}} \to \mathbf{Set}$ , or We consider the following cocone and cone:

$$
\begin{array}{c c} D (j) \xrightarrow {D (f)} D (k) & \mathcal {A} (D (j), A) \xleftarrow {- \circ D (f)} \mathcal {A} (D (k), A) \\ \downarrow p _ {j} & \mathcal {A} (p _ {j}, A) \xleftarrow {\mathcal {A} (p _ {k}, A)} \\ L & \mathcal {A} (L, A) \end{array}
$$

Let the left diagram be a limiting cocone. We will show the right diagram is a limiting cone. Notice that arrows are reversed in the right diagram due to contravariance.

If we want to claim the naturality of the correspondence, the following formulation is convenient. However, note that the discussion will be slightly restricted to the situation where all the  $J$ -shaped diagrams in  $\mathcal{A}$  have colimits.

- We define colimits lim as a functor. We know that colimits are unique up to isomorphisms. This means they are not unique. We choose a representative from each isomorphism class, using the axiom of choice. We can extend the so-obtained function on objects to function on morphisms. See Sect. 4.5 for details.  
- We define a functor  $[J, \mathcal{A}]^{\mathrm{op}} \times \mathcal{A} \to \mathbf{Set}$  that takes a colimit first and then applies Hom as follows:

$$
\begin{array}{l} [ J, \mathcal {A} ] ^ {\mathrm {o p}} \times \mathcal {A} \xrightarrow {\lim  _ {\to} ^ {\mathrm {o p}} \times \operatorname {I d}} \mathcal {A} ^ {\mathrm {o p}} \times \mathcal {A} \xrightarrow {\operatorname {H o m}} \mathbf {S e t} \\ (D, A) \longmapsto (\varinjlim D, A) \longmapsto \mathcal {A} (\varinjlim D, A) \\ \end{array}
$$

- We define a functor  $[J, \mathcal{A}]^{\mathrm{op}} \times \mathcal{A} \to \mathbf{Set}$  that creates a  $J$ -shaped diagram first, and then applies the limit functor as follows:

$$
\begin{array}{l} [ J, \mathscr {A} ] ^ {\mathrm {o p}} \times \mathscr {A} \xrightarrow {} [ J, \mathbf {S e t} ] \xrightarrow [ ]{\lim } \mathbf {S e t} \\ (D, A) \longmapsto \mathcal {A} (-, A) \circ D \longmapsto \varprojlim (\mathcal {A} (-, A) \circ D) \\ \end{array}
$$

- We define a natural isomorphism between the two functors above.

Colimits and limits play their roles in the same theater.

# Proof (Theorem 4.2)

We leave the naturality proof to the reader. Arguments similar to those in Chap. 7 will do.

Universality of colimits gives

$$
\mathscr {A} (\varinjlim D, A) \simeq \operatorname {C o n e s} (D, A).
$$

This is the definition of colimits itself. See Remark 3.1.

Given a cocone  $(D, \{x_j\}, X)$  we have a mediating morphism  $t: \varinjlim D \to X$  as in the following diagram:

![](images/a53d93507a369c22d149d3aceac8e88b5d8ca304165bdc0821c6e2eed99344ff.jpg)

where all the triangles commute and  $f: j \to k$  is an arbitrary morphism in  $J$ . We hand it to the contravariant functor  $\mathcal{A}(-, A)$  and get the following.

![](images/9280136a2f291316f8d211217a5c9d247ad3c4d5576e821ce7f85e976b2303ed.jpg)

Due to functoriality, all the triangles commute. We want to know whether  $\mathcal{A}(\lim D, A)$  is a limit or not. In any case Set guarantees the existence of limits. Let  $L$  be a limit and  $u$  a mediating morphism as follows.

![](images/a8edaf8b6c32c06874478738320ddd654c939e0efc1b0d8bf05fac149ee2af5c.jpg)

We use the same notation for projections. All the objects involved can be studied using their elements. Let  $x$  be an element of  $L$ . A limiting cone in Set can be seen as a set of cones from a point * to the base:

$$
\mathscr {A} (D (j), A) \xleftarrow {\mathscr {A} (D (f) , A)} \mathscr {A} (D (k), A)
$$

$$
x = \qquad p _ {j} \underset {\text {c o n s t} _ {p _ {j}} \text {c o n s t} _ {p _ {k}}} {\underset {\text {c o n s t} _ {p _ {k}}} {\leftarrow}} p _ {k},
$$

where  $\mathrm{const}_{p_j}$  is a function from a singleton set  $\{*\}$  to  $\mathcal{A}(D(j), A)$  that has a single value  $p_j$ . The data representation of this  $J^{\mathrm{op}}$ -shaped cone is

$$
\left(\{\ast \}, \left. \operatorname {c o n s t} _ {p _ {j}} \right\} _ {j \in \mathrm {O b j} (J)}, \mathcal {A} (-, A) \circ D\right).
$$

Such a cone is in one-to-one correspondence with  $(D, \{p_j\})$ , an element of Cones  $(D, A)$ . Thus, we have

$$
\varprojlim (\mathcal {A} (-, A) \circ D) \simeq \operatorname {C o n e s} (D, A)
$$

and get to the conclusion.

# 4.4 Executable Examples

We will see interactions between Hask, Hom functors,  $(\dashv)$ ,  $(\cdot ,\cdot)$ , and Either.

Listing 4.1 homlimit.vs  
```haskell
1 dataXA = A1 | A2 | A3  
2 deriving (Show, Eq, Enum)  
3  
4 dataXB = B1 | B2  
5 deriving (Show, Eq, Enum)  
6  
7 dataXC = C1 | C2 | C3 | C4 | C5 | C6  
8 deriving (Show, Eq, Enum)  
9  
10 -- Hom(XC, (XA times XB)) ~= Hom(XC, XA) times Hom(XC, XB)  
11 alpha1::(c -> (a,b)) -> (c -> a, c -> b)  
12 alpha1 f  
13 = (fst . f, snd . f)  
14  
15 alpha2::(c -> a, c -> b) -> (c -> (a,b))  
16 alpha2 (f,g)  
17 = \c -> (f c, g c)  
18  
19 -- Hom(XA + XB, XC) ~= Hom(XA, XC) times Hom(XB, XC)  
20 beta1::(Either a b -> c) -> (a -> c, b -> c)  
21 beta1 f  
22 = (f . Left, f . Right)  
23  
24 beta2::(a -> c, b -> c) -> (Either a b -> c)  
25 beta2 (f,g)  
26 = h  
27 where  
28 h (Left a) = f a  
29 h (Right b) = g b  
30  
31 -- test data for  
32 -- alpha1 . alpha2 = id and  
33 -- alpha2 . alpha1 = id  
34  
35 f1::XC -> (XA,XB)  
36 f1 C1 = (A1,B1)  
37 f1 C2 = (A1,B2)  
38 f1 C3 = (A2,B1)  
39 f1 C4 = (A2,B2)  
40 f1 C5 = (A3,B1)  
41 f1 C6 = (A3,B2)  
42
```

```haskell
43 f2 :: XC -> XA  
44 f2 C1 = A1  
45 f2 C2 = A1  
46 f2 C3 = A2  
47 f2 C4 = A2  
48 f2 C5 = A3  
49 f2 C6 = A3  
50  
51 g2 :: XC -> XB  
52 g2 C1 = B1  
53 g2 C2 = B1  
54 g2 C3 = B1  
55 g2 C4 = B2  
56 g2 C5 = B2  
57 g2 C6 = B2  
58  
59 {- executable tests  
60 map ((alpha2 . alpha1) f1) [C1 .. C6]  
61 map f1 [C1 .. C6]  
62  
63 map (fst ((alpha1 . alpha2) (f2, g2)) ) [C1 .. C6]  
64 map f2 [C1 .. C6]  
65 map (snd ((alpha1 . alpha2) (f2, g2)) ) [C1 .. C6]  
66 map g2 [C1 .. C6]  
67 -}  
68  
69 -- test data for  
70 -- beta1 . beta2 = id and  
71 -- beta2 . beta1 = id  
72  
73 f3 :: Either XA XB -> XC  
74 f3 (Left A1) = C1  
75 f3 (Left A2) = C2  
76 f3 (Left A3) = C3  
77 f3 (Right B1) = C4  
78 f3 (Right B2) = C5  
79  
80 d1 :: [Either XA XB]  
81 d1 = (map Left [A1 ..]) ++ (map Right [B1 ..])  
82  
83 f4 :: XA -> XC  
84 f4 A1 = C1  
85 f4 A2 = C2  
86 f4 A3 = C3  
87  
88 g4 :: XB -> XC  
89 g4 B1 = C4  
90 g4 B2 = C5  
91  
92 {- executable tests  
93 map ((beta2 . beta1) f3) d1  
94 map f3 d1  
95  
96 map (fst ((beta1 . beta2) (f4, g4))) [A1 ..]  
97 map f4 [A1 ..]  
98  
99 map (snd ((beta1 . beta2) (f4, g4))) [B1 ..]  
100 map g4 [B1 ..]  
101 -}
```

Lines 1-8 define three finite sets. All the type names begin with "X." We will drop this letter when we talk about objects in the context of category theory.

Lines 11-17 define a pair of functions that establish the isomorphism:

$$
\operatorname {H o m} (C, A \times B) \xrightarrow [ \ll_ {\alpha_ {2}} ]{\alpha_ {1}} \operatorname {H o m} (C, A) \times \operatorname {H o m} (C, B).
$$

Lines 20-29 define a pair of functions that establish the isomorphism:

$$
\operatorname {H o m} (A \sqcup B, C) \xrightarrow [ \beta_ {2} ]{\beta_ {1}} \operatorname {H o m} (A, C) \times \operatorname {H o m} (B, C).
$$

Notice that the contravariant functor exchanges the sorts of limits.

Lines 35-57 provide test data for checking if  $\alpha_{1}$  and  $\alpha_{2}$  are mutual inverses. We run the test code described in the commented-out area lines 60-66. For example, to test

$$
\alpha_ {2} \circ \alpha_ {1} = 1 _ {\operatorname {H o m} (C, A \times B)}
$$

run the test code as follows.

```txt
\*Main> :t alpha2 . alpha1   
alpha2 . alpha1 :: (c -> (a, b)) -> c -> (a, b)   
\*Main> map ((alpha2 . alpha1) f1) [C1 .. C6]   
[(A1,B1),(A1,B2),(A2,B1),(A2,B2),(A3,B1),(A3,B2)]   
\*Main> map f1 [C1 .. C6]   
[(A1,B1),(A1,B2),(A2,B1),(A2,B2),(A3,B1),(A3,B2)]
```

To test

$$
\alpha_ {1} \circ \alpha_ {2} = 1 _ {\operatorname {H o m} (C, A) \times \operatorname {H o m} (C, B)}
$$

run the test code as follows.

```lisp
\*Main> :t alpha1 . alpha2   
alpha1 . alpha2 :: (c -> a, c -> b) -> (c -> a, c -> b)   
\*Main> map (fst ((alpha1 . alpha2) (f2,g2)) ) [C1 .. C6]   
[A1,A1,A2,A2,A3,A3]   
\*Main> map f2 [C1 .. C6]   
[A1,A1,A2,A2,A3,A3]   
\*Main> map (snd ((alpha1 . alpha2) (f2,g2)) ) [C1 .. C6]   
[B1,B1,B1,B2,B2,B2]   
\*Main> map g2 [C1 .. C6]   
[B1,B1,B1,B2,B2,B2]
```

Lines 73-90 provide test data for checking if  $\beta_{1}$  and  $\beta_{2}$  are mutual inverses. We run the test code described in the commented-out area lines 93-100. For example, to test

$$
\beta_ {2} \circ \beta_ {1} = 1 _ {\operatorname {H o m} (A \sqcup B, C)}
$$

run the test code as follows.

```txt
\*Main> :t beta2 . beta1   
beta2 . beta1 :: (Either a b -> c) -> Either a b -> c   
\*Main> map ((beta2 . beta1) f3) d1   
[C1,C2,C3,C4,C5]   
\*Main> map f3 d1   
[C1,C2,C3,C4,C5]
```

To test

$$
\beta_ {1} \circ \beta_ {2} = 1 _ {\operatorname {H o m} (A, C) \times \operatorname {H o m} (B, C)}
$$

run the test code as follows.

```lisp
\*Main> :t beta1 . beta2   
beta1 . beta2 :: (a -> c, b -> c) -> (a -> c, b -> c)   
\*Main> map (fst ((beta1 . beta2) (f4,g4))) [A1 ..]   
[C1,C2,C3]   
\*Main> map f4 [A1 ..]   
[C1,C2,C3]   
\*Main> map (snd ((beta1 . beta2) (f4,g4))) [B1 ..]   
[C4,C5]   
\*Main> map g4 [B1 ..]
```

# 4.5 Limit Functors

In this section, we define limits and colimits as functors from category  $[J, \mathcal{A}]$  to  $\mathcal{A}$ . We assume that  $J$  is as small as before and  $\mathcal{A}$  is locally small. We also assume that all  $J$ -shaped diagrams have limits.

Remark 4.3 This is a continued comment of Remark 4.3. We always assume that  $J$ , an index category, is small and  $\mathcal{A}$  locally small. This makes the functor category  $[J, \mathcal{A}]$  locally small. We briefly see why.

Let  $D$  and  $D'$  be any pair of objects in  $[J, \mathcal{A}]$ . We have to show that  $[J, \mathcal{A}]$  is small. Since  $\mathcal{A}$  is locally small,  $\mathcal{A}(D(j), D'(j))$  is small for all  $j \in \mathrm{Obj}(J)$ . Therefore,

their product  $\prod_{j\in \mathrm{Obj}(J)}\mathcal{A}(D(j),D'(j))$  is also small. A natural transformation from  $D$  to  $D^{\prime}$  can be seen as an element of this set. Thus, we conclude that  $[J,\mathcal{A}](D,D^{\prime})$  is small.

# 4.5.1 Limits as a Functor

We assume that all  $J$ -shaped diagrams in  $\mathcal{A}$  have a limit. For each diagram  $F: J \to \mathcal{A}$ , we choose a representative from the isomorphism class of limits and assign the representative to  $\lim F$ . We consider this assignment as a function on objects of the functor we are going to define.

Next, we construct the function on morphisms. Given a morphism  $\alpha : F \to G$  in  $[J, \mathcal{A}]$ , consider the following diagram.

![](images/69f802494c0ac4b55c7f65aae2bfc740593367b40b478b0e5af773f8b5b30ce4.jpg)

Universality of  $\varprojlim G$  gives a unique mediating morphism  $\varprojlim \alpha$  from the cone  $(\lim F, \{\alpha_j \circ p_j\}, \overline{G})$ .

Given another morphism  $\beta : G \to H$  in  $[J, \mathcal{A}]$ , we can draw a diagram:

![](images/a1a8ad34ec3d74558aa99544f91f7fa921f494b1356fceada03918a050a7d153.jpg)

in which we want to have

$$
\varprojlim \beta \circ \varprojlim \alpha = \varprojlim (\beta \circ \alpha).
$$

In diagram (4.4), we find the followings:

(1) The top triangle commutes simply because it is the composition of natural transformations.

(2) The left square commutes since universality of  $\lim G$  gives a unique mediating morphism  $\varprojlim \alpha$  for the cone  $(\varprojlim F, \{\alpha_j \circ p_j\}, \overline{G})$ .  
(3) The right square commutes since universality of  $\lim H$  gives a unique mediating morphism  $\lim \beta$  for the cone  $(\lim G, \{\beta_j \circ q_j\}, \widetilde{H})$ .  
(4) (2) and (3) tell us that  $\lim \beta \circ \lim \alpha$  makes the large square commute. Cone  $(\varprojlim F, \{\beta_j \circ \alpha_j \circ p_j\}, H)$  and  $\varprojlim H$  should give a unique mediating morphism, which should be  $\lim \beta \circ \lim \alpha$  with no other choice.  
(5) Cone  $(\varprojlim F, \{(\beta \circ \alpha)_j \circ \overleftarrow{p_j}\}, H)$  and  $\varprojlim H$  give a unique mediating morphism  $\varprojlim (\beta \circ \alpha)$ .

From (1) we see that cones  $(\varprojlim F, \{\beta_j \circ \alpha_j \circ p_j\}, H)$  and  $(\varprojlim F, \{(\beta \circ \alpha)_j \circ p_j\}, H)$  are identical. Therefore, mediating morphisms given by (4) and (5) must coincide.

This concludes the construction of the functor  $\varprojlim: [J, \mathcal{A}] \to \mathcal{A}$ .

# 4.5.2 Colimits as a Functor

Let us continue a parallel discussion for colimits. We assume that all  $J$ -shaped diagrams in  $\mathcal{A}$  have a colimit. For each diagram  $F: J \to \mathcal{A}$ , we choose a representative from the isomorphism class of colimits and assign the representative to  $\varinjlim F$ . We consider this assignment as a function on objects of the functor we are going to define.

Next, we construct the function on morphisms. Given a morphism  $\alpha : F \to G$  in  $[J, \mathcal{A}]$ , consider the following diagram.

![](images/78322c03e4dc33f0200af15d842ed33d6bc9de69050be9d071a4a3696be28264.jpg)

Universality of  $\varinjlim F$  gives a unique mediating morphism  $\varinjlim \alpha$  to the cocone  $(F, \{q_j \circ \alpha_j\}, \varinjlim G)$ .

Given another morphism  $\beta : G \to H$  in  $[J, \mathcal{A}]$ , we can draw a diagram:

![](images/8d97c4b99c1bd33075698dba8302cd8f0431550c3ee4154035a409bb2bff64a4.jpg)

in which we want to have

$$
\varinjlim \beta \circ \varinjlim \alpha = \varinjlim (\beta \circ \alpha).
$$

In diagram (4.5), we find the followings:

(1) The top triangle commutes simply because it is the composition of natural transformations.  
(2) The left square commutes since universality of  $\varinjlim F$  gives a unique mediating morphism  $\varprojlim \alpha$  for the cocone  $(F, \{q_j \circ \alpha_j\}, \varinjlim G)$ .  
(3) The right square commutes since universality of  $\varprojlim G$  gives a unique mediating morphism  $\varinjlim \beta$  for the cocone  $(G, \{r_j \circ \beta_j\}, \varprojlim H)$ .  
(4) (2) and (3) tell us that  $\lim_{\rightarrow} \beta \circ \lim_{\rightarrow} \alpha$  makes the large square commute. Cocone  $(F, \{r_j \circ \beta_j \circ \alpha_j\}, \varinjlim H)$  and  $\varinjlim F$  should give a unique mediating morphism, which should be  $\lim_{\rightarrow} \beta \circ \lim_{\rightarrow} \alpha$  with no other choice.  
(5) Cocone  $(F, \{r_j \circ (\vec{\beta} \circ \alpha)_j\}, \varinjlim H)$  and  $\varinjlim F$  give a unique mediating morphism  $\varinjlim (\beta \circ \alpha)$ .

From (1) we see that cocones  $(F, \{r_j \circ \beta_j \circ \alpha_j\}, \varinjlim H)$  and  $(F, \{r_j \circ (\beta \circ \alpha)_j\}, \varinjlim H)$  are identical. Therefore, mediating morphisms given by (4) and (5) must coincide.

This concludes the construction of the functor  $\varinjlim : [J, \mathcal{A}] \to \mathcal{A}$ .

# Adjoints

5

We will see various phenomena involving adjunction, universal arrows, equivalence of categories, adjoint equivalence, and their interrelationship. Adjunction appears in everyday life in mathematics, computer science, and theoretical physics.

Let  $V$  be a finite-dimensional real vector space with inner product  $\langle -, - \rangle$ . Linear transformation  $A$  and its transpose  $^t A$  are, by definition, related as follows: for any pair  $x,y\in V$ , equation

$$
\langle A x, y \rangle = \langle x, ^ {t} A y \rangle
$$

holds. We often represent linear transformations as matrices, where transposition is really matrix transposition. If we work with the complex numbers, we usually introduce Hermitian inner products and Hermitian conjugates. If you are familiar with these examples, you are sure to become familiar with the notion of adjunction.

We will study the adjunction of functors

$$
\mathcal {A} (F X, A) \cong \mathcal {X} (X, U A).
$$

# 5.1 Adjunctions

Let  $\mathcal{X}$  and  $\mathcal{A}$  be locally small categories,  $F$  and  $U$  be functors. We will study various phenomena in which arrows  $h:FX\to A$  and  $f:X\to UA$  are in one-to-one correspondence as in the following diagram:

$$
\mathcal {A} \xrightarrow [ \leqslant F ]{U} \mathcal {X}
$$

$$
\begin{array}{c} F X \xleftarrow {F} X \\ h \Bigg {\downarrow} \\ A \xmapsto {} _ {U} U A, \end{array}
$$

for all pairs  $X\in \mathrm{Obj}(\mathcal{X})$  and  $A\in \mathrm{Obj}(\mathcal{A})$

Definition 5.1 (Adjunctions) If there are bijections

$$
\phi_ {X, A}: \mathcal {A} (F X, A) \cong \mathcal {X} (X, U A)
$$

for all pairs  $(X, A)$  depending naturally on  $X$  and  $A$ , then we say that  $F$  is a left adjoint of  $G$  and that  $G$  is a right adjoint of  $F$ . We denote this situation by  $F \dashv U$ . Naturality is explained later.

When  $h:FX\to A$  and  $f:X\to UA$  are in the above correspondence, namely,  $\phi_{X,A}(h) = f$ , we write a diagram like

$$
\frac {F X \stackrel {h} {\to} A}{X \underset {f} {\to} U A}.
$$

These two morphisms are called mutual transposition or adjunct. We call the part over the horizontal bar the numerator and the part under the bar the denominator in analogy with fractions.

We say that the family of bijections  $\phi_{X,A}$  is natural in  $X$  if

$$
\frac {F X ^ {\prime} \xrightarrow {F x} F X \xrightarrow {h} A}{X ^ {\prime} \xrightarrow [ x ]{} X \xrightarrow [ f ]{} U A}
$$

for any morphism  $x: X' \to X$  in  $\mathcal{X}$ . We may write as  $\phi_{X',A}(h \circ Fx) = f \circ x$ . We say that the family of bijections  $\phi_{X,A}$  is natural in  $A$  if

$$
\frac {F X \xrightarrow {h} A \xrightarrow {a} A ^ {\prime}}{X \xrightarrow {} f U A \xrightarrow {} U a U A ^ {\prime}}
$$

for any morphism  $a:A\to A'$  in  $\mathcal{A}$ . We may write as  $\phi_{X,A'}(a\circ h) = Ua\circ f$

Naturality in  $X$  and  $A$  can be presented in a single diagram:

$$
\frac {F X ^ {\prime} \xrightarrow {F x} F X \xrightarrow {h} A \xrightarrow {a} A ^ {\prime}}{X ^ {\prime} \xrightarrow {} X \xrightarrow {} f U A \xrightarrow {} U a}. \tag {5.1}
$$

![](images/b0a71c97be741750890ab40cff64f049ca352195b3f20aae8b021ff9823c7561.jpg)  
Fig.5.1 Adjunct pair

![](images/d3c30e3069476bccb9f097ea0aea76738ccaff6c92b4d21f3e8b8bb74d29592c.jpg)

Pivoting the adjunct pair  $h$  and  $f$ , the extension to the left is supported by functor  $F$  and to the right by  $U$  as in the following diagram:

$$
\frac {\text {b y f u n c t o r} F}{\text {e x t e n d e d t o l e f t}} \xrightarrow [ ]{\rightarrow F X \xrightarrow {h} A \rightarrow} \frac {\text {e x t e n d e d t o r i g h t}}{\text {b y f u n c t o r} U}.
$$

We will introduce the concept of the universal arrow later. As a preparation, we give a bit crowded drawing Fig. 5.1. Corresponding pairs of paths by the vertical translation, for example, two dashed paths, are adjuncts.

# 5.2 Unit and Counit

Let us specialize in an adjunct pair

$$
\frac {F X \stackrel {h} {\to} A}{X \underset {f} {\to} U A}
$$

by replacing  $A$  with  $FX$  and  $h$  with  $1_{FX}: FX \to FX$ . We denote its adjunct by  $\eta_X$ . We have

$$
\frac {F X \xrightarrow {1 _ {F X}} F X}{X \xrightarrow {} _ {\eta_ {X}} U F X}.
$$

Another specialization is to replace  $X$  with  $UA$  and  $f$  with  $1_{UA}: UA \to UA$ . We denote its adjunct by  $\varepsilon_A$ . We have

$$
\frac {F U A \xrightarrow {\varepsilon_ {A}} A}{U A \xrightarrow {} _ {1 _ {U A}} U A}.
$$

The family of morphisms  $\eta_{X}$  is said to be the unit of the adjunction. The family of morphisms  $\varepsilon_{A}$  is said to be the counit of the adjunction.

Proposition 5.1 (Natural transformations) The assignments  $X \mapsto \eta_X$  and  $A \mapsto \varepsilon_A$  define natural transformations  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$  and  $\varepsilon : FU \to \operatorname{Id}_{\mathcal{A}}$ .

Proof First, we make clear the goal. An assignment  $\eta : X \mapsto \eta_X$  is said to be a natural transformation if the following diagram commutes

$$
\begin{array}{c}X_{1}\xrightarrow{\eta_{X_{1}}}UFX_{1}\\ \Big{\downarrow}_{f}\quad\big{\circ}\qquad\Big{\downarrow}_{UFf}\\ X_{2}\xrightarrow{\eta_{X_{2}}}\text{$U$}FX_{2} \end{array}
$$

for any pair of objects  $X_{1}, X_{2} \in \mathrm{Obj}(\mathcal{X})$  and a morphism  $f: X_{1} \to X_{2}$ . Recall that the above diagram is a part of the following diagram:

![](images/1ad086b53e178925774b127e19f81e1008db7b57c80769fb078bc669e9e5d4c8.jpg)

which might convey more intuition to the reader. However, to save space we will not stick to this luxurious drawing style.

We can put the goal in other words: The two paths

$$
X _ {1} \xrightarrow [ \eta X _ {1} ]{} U F X _ {1} \xrightarrow [ U F f ]{} U F X _ {2} \tag {5.2}
$$

and

$$
X _ {1} \underset {f} {\rightarrow} X _ {2} \underset {\eta_ {X _ {2}}} {\longrightarrow} U F X _ {2} \tag {5.3}
$$

must coincide.

Both are paths in  $\mathcal{X}$ . We put them in the denominator positions of the fractional diagrams.

Let us begin with path (5.2). We place its adjunct in the numerator:

$$
\xrightarrow [ X _ {1} \xrightarrow {\eta_ {X _ {1}}} U F X _ {1} \xrightarrow [ U F f ]{F f} U F X _ {2} ]. \tag {5.4}
$$

Next, we place path (5.3) in the denominator and its adjunct in the numerator:

$$
\frac {F X _ {1} \xrightarrow {F f} F X _ {2} \xrightarrow {1 _ {F X _ {2}}} F X _ {2}}{X _ {1} \xrightarrow [ f ]{\rightarrow} X _ {2} \xrightarrow {\eta_ {X _ {2}}} U F X _ {2}}. \tag {5.5}
$$

We see that numerators in (5.4) and (5.5) are both

$$
F X _ {1} \xrightarrow {F f} F X _ {2}.
$$

Therefore, by adjunction, the denominators must coincide.

Next we show that the assignment  $\varepsilon : A \mapsto \varepsilon_A$  is a natural transformation. We have to show that the following diagram commutes:

$$
\begin{array}{c} F U A _ {1} \xrightarrow {\varepsilon_ {A _ {1}}} A _ {1} \\ F U f \Bigg \downarrow \qquad \bigcirc \qquad \Bigg \downarrow f \\ F U A _ {2} \xrightarrow {\varepsilon_ {A _ {2}}} A _ {2} \end{array}
$$

for any pair of objects  $A_{1}, A_{2} \in \mathrm{Obj}(\mathcal{A})$  and a morphism  $f: A_{1} \to A_{2}$ .

We can put the goal in other words: The two paths

$$
F U A _ {1} \xrightarrow {\varepsilon_ {A _ {1}}} A _ {1} \xrightarrow {f} A _ {2} \tag {5.6}
$$

and

$$
F U A _ {1} \xrightarrow {F U f} F U A _ {2} \xrightarrow {\varepsilon_ {A _ {2}}} A _ {2} \tag {5.7}
$$

must coincide.

Both are paths in  $\mathcal{A}$ . We put them in the numerator positions of the fractional diagrams.

Let us begin with path (5.6). We place its adjunct in the denominator:

$$
\frac {F U A _ {1} \xrightarrow {\varepsilon_ {A _ {1}}} A _ {1} \xrightarrow {f} A _ {2}}{U A _ {1} \xrightarrow {} U A _ {1} \xrightarrow {} U f} U A _ {2}. \tag {5.8}
$$

Next, we place the path (5.7) in the numerator and place its adjunct in the denominator:

$$
\frac {F U A _ {1} \xrightarrow {F U f} F U A _ {2} \xrightarrow {\varepsilon_ {A _ {2}}} A _ {2}}{U A _ {1} \xrightarrow {} U f U A _ {2} \xrightarrow {} 1 _ {U A _ {2}} U A _ {2}}. \tag {5.9}
$$

We see that denominators in (5.8) and (5.9) are both

$$
U A _ {1} \xrightarrow {U f} U A _ {2}.
$$

Therefore, by adjunction, the numerators must coincide.

![](images/566096299da0590ed538c5fab4c37256227a600749a7e6bb39c2b13852afd9ff.jpg)

Definition 5.2 Natural transformations  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$  and  $\varepsilon : F U \to \operatorname{Id}_{\mathcal{A}}$  derived from an adjunction  $F \rightharpoonup U$  are called the unit and counit of the adjunction, respectively.

# 5.3 Triangle Identities

Proposition 5.2 (Triangle identities) Given an adjunction  $F \vdash U$  with unit  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$  and counit  $\varepsilon : FU \to \operatorname{Id}_{\mathcal{A}}$ , we have two commutative diagrams called the triangle identities.

$$
\begin{array}{c c} U \xrightarrow {\eta U} U F U & F U F \xleftarrow {F \eta} F \\ \Bigg \downarrow_ {U \varepsilon} & \varepsilon F \\ U & F \end{array} \tag {5.10}
$$

Let us first check the types of objects, morphisms, functors, and natural transformations and see if they are properly fit in the diagrams (5.10).

$\eta U, U \varepsilon, F \eta,$  and  $\varepsilon F$  are combinations of functors and natural transformations. We have to make clear in what way they are concatenated.

Let us put (5.10) into the component-based style as follows.

![](images/623fd707efd995d4eb19680b0306c6d8f5e11eb711b39a1f91a8b89b1839bb0a.jpg)

In this diagram, the players are only objects and morphisms. So, the correctness of wiring depends simply on domain-codomain matching. We may proceed in this style in the rest of our discussion. However, component-free presentation is seen everywhere in various articles, papers, and books. Let us immerse ourselves in this style.

We begin with  $\eta U$ . We can read it as  $\eta$  is concatenated with  $U$  as in

![](images/9b73ce28179714ed1e3e2adbd0d5cdde28370ac41e8d7a6b28c4ab79bd78c91f.jpg)

Horizontal composition gives us another natural transformation

![](images/0c57f7fc4570db0c6ed8627eb400e10069f838fb8a6dbc5329f10d7521dc2ad4.jpg)  
namely

![](images/165710326ddb3bbb7d1c2e4d914af5376dcf9cfe538920af49bbb728885cbcbc.jpg)

The component of  $\eta U$  at  $A\in \mathrm{Obj}(\mathcal{A})$  is given by

$$
(\eta U) _ {A} \stackrel {\text {d e f}} {=} \eta_ {U A}: U A \rightarrow U F U A.
$$

Next, we analyze  $U \varepsilon$ . We can read it as  $\varepsilon$  is presupended by  $U$  as in

![](images/ca92914d6668f42cf553a9ef35c399f84b8ed757d4df1e3c2faf2215203a0ec7.jpg)

Horizontal composition gives us another natural transformation

![](images/b6586e7566b76ef65ce5a46b0eefae51f08d2ee6919e5da26a72bd1f22fb3c4a.jpg)  
namely

![](images/8f6c54afc40545fb98c069e8700aaa842167d7c8f0b9d4cbbcb723e951c97ed1.jpg)

The component of  $U\varepsilon$  at  $A\in \mathrm{Obj}(\mathcal{A})$  is given by

$$
(U \varepsilon) _ {A} \stackrel {\text {d e f}} {=} U (\varepsilon_ {A}): U F U A \to U A.
$$

We omit the discussion on horizontal compositions of  $F\eta$  and  $\varepsilon F$ . We just give their components. The component of  $F\eta : F \to FUF$  at  $X$  is given by

$$
(F \eta) _ {X} \stackrel {\mathrm {d e f}} {=} F (\eta_ {X}): F X \rightarrow F U F X.
$$

The component of  $\eta F:FUF\to F$  at  $X$  is given by

$$
(\varepsilon F) _ {X} \stackrel {\mathrm {d e f}} {=} \varepsilon_ {F X}: F U F X \to F X.
$$

Proof (Proposition 5.2)

We first prove

$$
U A \xrightarrow [ \eta_ {U A} ]{} U F U A \xrightarrow [ U _ {\varepsilon_ {A}} ]{} U A = U A \xrightarrow [ 1 _ {U A} ]{} U A.
$$

The both sides of the equation are paths in  $\mathcal{X}$ . We put them in the denominators with their adjuncts in the numerators as follows.

$$
\frac {F U A \xrightarrow {1 _ {F U A}} F U A \xrightarrow {\varepsilon_ {A}} A}{U A \xrightarrow {\eta_ {U A}} U F U A \xrightarrow {} U _ {\varepsilon_ {A}}} \tag {5.11}
$$

$$
\frac {F U A \xrightarrow {\varepsilon_ {A}} A}{U A \xrightarrow {} 1 _ {U A} U A} \tag {5.12}
$$

The numerators in (5.11) and (5.12) are equal. Therefore, the denominators must coincide.

Next, we prove

$$
F X \xrightarrow {F \eta_ {X}} F U F X \xrightarrow {\varepsilon_ {F X}} F X = F X \xrightarrow {1 _ {F X}} F X.
$$

The both sides of the equation are paths in  $\mathcal{A}$ . We put them in the numerators with their adjuncts in the denominators as follows.

$$
\frac {F X \xrightarrow {F \eta_ {X}} F U F X \xrightarrow {\varepsilon_ {F X}} F X}{X \xrightarrow {} _ {\eta_ {X}} U F X \xrightarrow {} _ {1 _ {F X}} U F X} \tag {5.13}
$$

$$
\frac {F X \xrightarrow {1 _ {F X}} F X}{X \xrightarrow {\eta_ {X}} U F X} \tag {5.14}
$$

The denominators in (5.13) and (5.14) are equal. Therefore, the numerators must coincide.

# 5.4 Universal Arrows and Adjunctions

We will explain adjunctions from the view point of universal arrows. In Sect. 5.1, the naturality of adjunction is described by the correspondence

![](images/b4933870ce490039ad5ffc0b25970e7b8bb4e74f4bfa7dbb6008163eac2880e3.jpg)  
Fig.5.2 Factorization of  $x:FX\to UA^{\prime}$

$$
\frac {F X ^ {\prime} \xrightarrow {F x} F X \xrightarrow {h} A \xrightarrow {a} A ^ {\prime}}{X ^ {\prime} \xrightarrow {} X \xrightarrow {} f U A \xrightarrow {} U a}. \tag {5.15}
$$

We replace  $A$  with  $FX, h$  with  $1_{FX}$ , and one with another among various morphisms  $a_i: FX \to A_i$  in the adjunction above as follows:

$$
\begin{array}{c} \dots \to F X \xrightarrow {1 _ {F X}} F X \xrightarrow {a _ {i}} A _ {i} \\ \hline \dots \to X \xrightarrow [ \eta_ {X} ]{} U F X \xrightarrow [ U a _ {i} ]{} U A _ {i} \end{array} ,
$$

where  $a_{i}$  with index  $i$  ranges over all the morphisms that have  $FX$  as their domain. There may exist an  $A^\prime$  such that  $\mathcal{A}(FX,A^{\prime})$  is empty, which we exclude from our discussion. We extract the denominator and rotate  $90^{\circ}$ . Then, we get Fig. 5.2. Given an arbitrary morphism  $x:X\to UA^{\prime}$ , we pose the question of whether or not  $x$  factors through  $\eta_{X}$  with a dashed arrow  $Ua^{\prime}$  (with  $a^\prime :FX\to A^\prime$ ) in Fig. 5.2. If this is the case,  $\eta_{X}$  is called a universal arrow from  $X$  to functor  $U$ . Further, if this is the case for all  $X\in \mathrm{Obj}(\mathcal{X})$ , then natural transformation  $\eta :\operatorname {Id}_{\mathcal{X}}\to UF$  is said to be universal to functor  $U$ . We will return to this problem shortly.

Let us replace  $X$  with  $UA$  and  $f$  with  $1_{UA}$ , and one with another among various morphisms  $x_i : X_i \to UA$  in adjunction (5.15) to get the following:

$$
\frac {F X _ {i} \xrightarrow {F x _ {i}} F U A \xrightarrow {\varepsilon_ {A}} A \to \cdots}{X _ {i} \xrightarrow {x _ {i}} U A \xrightarrow {} 1 _ {U A} U A \to \cdots},
$$

where  $x_{i}$  with index  $i$  ranges over all the morphisms that have  $UA$  as their codomain. There may exist an  $X'$  such that  $\mathcal{A}(X', UA)$  is empty, which we exclude from our discussion. We extract the numerator and rotate  $90^{\circ}$ . Then, we get Fig. 5.3. Given an arbitrary morphism  $a: FX' \to A$ , we pose the question of whether or not  $a$  factors through  $\varepsilon_{A}$  with a dashed arrow  $Fx'$  (with  $x': X' \to UA$ ) in Fig. 5.3. If this is the case,  $\varepsilon_{A}$  is called a universal arrow from functor  $F$  to  $A$ . Further, if this is the case for all  $A \in \mathrm{Obj}(\mathcal{A})$ , then natural transformation  $\varepsilon: FU \to \mathrm{Id}_{\mathcal{A}}$  is said to be universal from functor  $F$ . We will return to this problem shortly.

![](images/60f65c029740344b75ad87e06755add292f96808db1867e33acb3ff467dd1a85.jpg)  
Fig.5.3 Factorization of  $a:FX^{\prime}\to A$

# 5.5 Equivalent Formulations of Adjunction

We will show that adjunctions, universal arrows, and triangle identities are all equivalent, which allows us to choose the most appropriate definition depending on the situations.

Theorem 5.1 Given a pair of functors  $U: \mathcal{A} \to \mathcal{X}$  and  $F: \mathcal{X} \to \mathcal{A}$ , the following four conditions are equivalent.

1.  $F \vdash U$ .  
2. A pair of natural transformations  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$  and  $\varepsilon : FU \to \operatorname{Id}_{\mathcal{A}}$  makes the following two triangles commute

![](images/5234f5a5581a3757f23cdea843eb8b29960347acedcbfb52041ed9aae3f004fa.jpg)

3. There exists a universal arrow  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$  to functor  $U$ , where universal means that for all morphism  $f: X \to UA$  there exists a unique morphism  $h: FX \to A$  that makes the following triangle commute.

![](images/bb289f79020fc8977f124d2b79cf03ee3fc27c75985b01cbe5c4bc4fa3ab515c.jpg)

4. There exists a universal arrow  $\varepsilon : FU \to \operatorname{Id}_{\mathcal{A}}$  from functor  $F$ , where universal means that for all morphism  $h : FX \to A$  there exists a unique morphism  $f : X \to UA$  that makes the following triangle commute.

![](images/b295de006e6199b9ea480b954d5c747e21b221adbebb68222be6d1a5d83c0f84.jpg)

We adopt a strategy as follows.

![](images/5f5aef601bd6a428cbcc7a218b6f97b2fea2806ce37e11edf4c72c240dc23d0d.jpg)

Note that we have already shown  $1 \Rightarrow 2$  in Proposition 5.2.

Proof  $(2\Rightarrow 3$  in Theorem 5.1)

We have to find a morphism  $UFX \xrightarrow{?} UA$  in the following diagram.

![](images/2e5052d85c83524c83ca41880cb6211d76e1bb9391a7e2c7874bd604e11bc500.jpg)

We can think of only one morphism  $U F f: U F X \to U F U A$  that originates from  $U F X$ . Thanks to the naturality of  $\eta$  we obtain a commutative square

![](images/13b2bdf6d2027b3f43db9764ee49a042d5af4962bac241d44a3f9467c147de2a.jpg)

If we search for other materials that can be fit to this square, we find only one thing in the triangle identities. Let them combine.

![](images/d9070cab4ba37540969392d95244d1f7609840e21bf406d21b7667d6852e18da.jpg)

In this diagram, the triangle, square, and consequently trapezoid standing on its toe  $UA$  are all commutative. If we put  $h = \varepsilon_A\circ Ff$ , we have the following.

![](images/481638b726a6f2dc19a76dae792bd91ff33524d1e07c70bee8f07edaf4987e1e.jpg)

![](images/bb4dbbbdeaba365d409de52d6136ddd75011a110bf58d3e459d8cd1f22a1f78b.jpg)

We want to show that such a morphism  $h$  is unique. Note that when we apply functor  $U$  to morphism  $h$ , we can distribute  $U$  over the composition  $\circ$ , namely

$$
U h = U \left(\varepsilon_ {A} \circ F f\right) = U \left(\varepsilon_ {A}\right) \circ U (F f) = U \varepsilon_ {A} \circ U F f.
$$

Suppose we have another  $h' : FX \to A$  such that  $Uh \circ \eta_X = Uh' \circ \eta_X$ . Let us draw a square of natural transformation  $\varepsilon$  with a triangle that fit to the square.

![](images/ae671d77e43269cf6e99cc4a5d81476b223501362a302f0d58b63e8ac0c3c7b1.jpg)

This gives

$$
h ^ {\prime} = h = \varepsilon_ {A} \circ F (U h \circ \eta_ {X} = U h ^ {\prime} \circ \eta_ {X}).
$$

![](images/2639199331bde2a7fcc6167d5309a010601a0a0dfd16cc756b20c87691715199.jpg)

Proof (2  $\Rightarrow$  4 in Theorem 5.1)

We have to find a morphism  $FX \stackrel{?}{\to} FUA$  in the following diagram.

![](images/fae8e780241dd3df2ee19696edb04fb5934be7fa8089d07dd2c889583065b303.jpg)

We can think of only one morphism  $FUh: FUFX \to FUA$  that terminates at  $FUA$ . Thanks to the naturality of  $\varepsilon$  we obtain a commutative square

![](images/8409cf09437947187aeba016db65e13b99eb182351a1215d087ab8dddd420117.jpg)

If we search for other materials that can be fit to this square, we find only one thing in the triangle identities. Let them combine.

![](images/8e21b9a44f780afdf13df23159ee50e644632bd6a0ad314aaa407dcea7e170c5.jpg)

In this diagram, the triangle, square, and consequently trapezoid with a slant roof are all commutative. If we put  $f = Uh \circ \eta_X$ , we have the following.

![](images/2feb64b69366335f2bf65682f025b3749cefee7c3d76dd21b5e766e9f1f28cac.jpg)

![](images/ec0b5694357340f5852156e32f0ba4c7d6e97289c29ae35041508d28828bb5ef.jpg)

We want to show that such a morphism  $f$  is unique.

Suppose we have another  $f': X \to UA$  such that  $\varepsilon_X \circ Ff = \varepsilon_X \circ Ff'$ . Let us draw a square of natural transformation  $\eta$  with a triangle that fit into the square.

![](images/7fa24a5fd20ffd98932eef29b855873c97b02ffbb7ba0dcd9e87600c9b34ac47.jpg)

This gives

$$
f ^ {\prime} = f = U \left(\varepsilon_ {A} \circ F f ^ {\prime} = \varepsilon_ {A} \circ F f\right).
$$

![](images/cdf279e301ce11f18b0d6a8911c5f1e59f4a9da009472c61bff6c319370880c3.jpg)

Proof (3  $\Rightarrow$  1 in Theorem 5.1)

By assumption, for any  $f: X \to UA$  there exists a unique morphism  $h: FX \to A$  that makes the following triangle commute.

![](images/1f29bd078108136d667b626162a13d1617d0ddd9c415b28b08f91c6876e864c7.jpg)

Conversely, given  $h:FX\to A$ , we can put  $f = Uh\circ \eta_{X}$  to make the diagram above commute. Thus, we obtained a bijection

$$
\mathcal {X} (X, U A) \rightarrow \mathcal {A} (F X, A).
$$

Let us first show naturality in  $X$ . Take any morphism  $a: X' \to X$ .

![](images/dff02f63db8e3cc02ab8bdba540f8a0bdebc36c4e7cc4e816b3fb265c07524e8.jpg)

![](images/2c1acfcf0187b51f877ceac9dd27197e0023eee8bddccb1118eb823d486448e4.jpg)

Commutativity in this diagram is as follows.

![](images/c01956ee5d030d5d5eb37e51a22efc12e9ca8751b1b11a0cd78c91cb7139cd12.jpg)  
(1)

![](images/56ec9a7a6b2e9f2c1b5ffc1fdc20caa632a843a97f3b95185831b36cf6b4e49e.jpg)  
(2)

![](images/f00f42a4bdf5dc8f18f3cef8d36823c639f44bc084f5a75feff29684d717d804.jpg)  
(3)

![](images/ad8324fb4f4ab8559e60e682e6593a26db41aeedba61a5e44ab1355b4e4e33cc.jpg)  
(4)

(1) is given by universal arrow  $\eta$  to functor  $U$ .  
(2) by natural transformation  $\eta :\mathrm{Id}_{\mathcal{X}}\to UF$  
(3) by functor  $U$  
(4) by the combination of (1), (2), and (3).

Universal arrow  $\eta$  to  $U$  and (4) establishes

$$
\frac {F X ^ {\prime} \xrightarrow {F a} F X \xrightarrow {h} A}{X ^ {\prime} \xrightarrow [ a ]{} X \xrightarrow [ f ]{} U A}.
$$

This shows the bijection is natural in  $X$ .

Next, we show naturality in  $A$ . Take any morphism  $b:A\to A'$

![](images/2eb29959bf2b5c0287b01f43d78c7f5cfe384548e2b7ba270eac50a4caf183c0.jpg)

Commutativity in this diagram is as follows.

![](images/ec0cebe259b8f35361acceecfd00df5c73a1f8e538eb76750445039aacde1f35.jpg)  
(1)

![](images/b7a8955018b4fd4b02fc25cb17ae50e4d1eb57792e9e84bf276b9d2b2a350638.jpg)  
(2)

![](images/5398ba90e9a9dfed0d0b9d429a59cce9586588998a821d10518faeb3f0e481af.jpg)  
(3)

(1) is given by universal arrow  $\eta$  to functor  $U$ .  
(2) by functor  $U$  
(3) by the combination of (1) and (2).

Universal arrow  $\eta$  to  $U$  and (3) establishes

$$
\frac {F X \xrightarrow {h} A \xrightarrow {b} A ^ {\prime}}{X \xrightarrow [ f ]{} U A \xrightarrow [ U b ]{} U A ^ {\prime}}.
$$

This shows the bijection is natural in  $A$ .

![](images/1686e54722343f748c278ae1fb187e9a60d9158833ae039518fb1347d3ae6520.jpg)

Proof  $(4\Rightarrow 1$  in Theorem 5.1)

By assumption, for any  $h:FX\to A$  there exists a unique morphism  $f:X\to UA$  that makes the following triangle commute.

![](images/690af913b9aed72714f34240086be2571d4009d399ee47e77d3988eed3481ec1.jpg)

Conversely, given  $f: X \to UA$ , we can put  $h = \varepsilon_A \circ Ff$  to make the diagram above commute. Thus, we obtained a bijection

$$
\mathcal {A} (F X, A) \rightarrow \mathcal {X} (X, U A).
$$

What remains to show is the naturality in  $X$  and  $A$ .

Let us first show naturality in  $X$ . Take any morphism  $a: X' \to X$ .

![](images/6f089792d9454ef38b70065a2c788d951562002f540808852810ab768f391edb.jpg)

Commutativity in this diagram is as follows.

![](images/0db7908d5744503ce6364c69a3bba49c77b1fb27ec23eddb6ffbf9dff3f76645.jpg)  
(1)

![](images/b34ca15fc81d742abcf956bc2680e82da6dd0c56d6542c7bbe2c78b357e04feb.jpg)  
(2)

![](images/69119c758c1ca1c3373af5f69bf79b53e61499053af11dd5a351a242db0d6222.jpg)  
(3)

(1) is given by universal arrow  $\varepsilon$  from functor  $F$ .  
(2) by functor  $F$  
(3) by the combination of (1) and (2).

Universal arrow  $\varepsilon$  from  $F$  and (3) establishes

$$
\frac {F X ^ {\prime} \xrightarrow {F a} F X \xrightarrow {h} A}{X ^ {\prime} \xrightarrow [ a ]{} X \xrightarrow [ f ]{} U A}.
$$

This shows the bijection is natural in  $X$ .

Next, we show naturality in  $A$ . Take any morphism  $b:A\to A'$

![](images/922a08cfa8c32070d79ed323d4b937910ad7de51395f8e2ac09123d28ee868c7.jpg)

![](images/01a9e3927fde618c6d4fd0871bb4e185697c9bc2cc716a9203840708323b84c9.jpg)

Commutativity in this diagram is as follows.

![](images/95a33bd539eb40eb077dee7de44e463657f7584397f721c6996b76f2dbb3e266.jpg)  
(1)

![](images/86f6d733c3adae540254a16c5882927db2c7b5b281ce978fc16824b7c5bf6777.jpg)  
(2)

![](images/95b4a04c5c35ad241250c396b79b579b43d5d0d3f71185bd063f8a79968e13d9.jpg)  
(3)

(1) is given by universal arrow  $\varepsilon$  from functor  $F$ .  
(2) by natural transformation  $\varepsilon$  
(3) by the combination of (1) and (2).

Universal arrow  $\varepsilon$  from  $F$  and (3) establishes

$$
\frac {F X \xrightarrow {h} A \xrightarrow {b} A ^ {\prime}}{X \xrightarrow {} f U A \xrightarrow {} U b U A ^ {\prime}}.
$$

This shows the bijection is natural in  $A$ .

The concept of free object is often used as in the following theorem.

Theorem 5.2 Given a functor  $U: \mathcal{A} \to \mathcal{X}$ , the following two conditions are equivalent.

1. There exists another functor  $F:\mathcal{X}\to \mathcal{A}$  that yields  $F\vdash G$  
2. For any  $X \in \mathrm{Obj}(\mathcal{X})$  there exists a free object  $F_0X \in \mathrm{Obj}(\mathcal{A})$ . We say that  $F_0X \in \mathrm{Obj}(\mathcal{A})$  is a free object if there exists a morphism  $\eta_X : X \to UF_0X$  such that for all  $f : X \to UA$  there exists a unique  $f^\sharp : F_0X \to A$  that makes the following diagram commute.

$$
\begin{array}{c c} X \xrightarrow {\eta_ {X}} U F _ {0} X & F _ {0} X \\ \downarrow_ {\forall f} & \downarrow \exists ! f ^ {\sharp} \\ U A & A \end{array} \tag {5.16}
$$

In condition 2,  $F_0$  is just a function on objects. We will show that  $F_0$  is eventually extended to a functor  $F$ .

Example 5.1 Let  $\mathcal{X} = \mathbf{Set}$  and  $\mathcal{A} = \mathrm{Vect}_{\mathbb{C}}$ . Let  $U: \mathrm{Vect}_{\mathbb{C}} \to \mathbf{Set}$  be a forgetful functor.  $F: \mathbf{Set} \to \mathrm{Vect}_{\mathbb{C}}$  takes a set  $X$  and returns a complex vector space  $FX$  that has  $X$  as its basis. We give functions on objects in a rough informal style.

$$
\begin{array}{l} F X = \bigoplus_ {x \in X} \mathbb {C} \vec {b} _ {x} \\ U F X = \{\sum_ {x \in X} c _ {x} \vec {b} _ {x} \Bigg | c _ {x} \in \mathbb {C} \} \simeq \{\{c _ {x} \} _ {x \in X} \} \\ \eta_ {X}: X \to U F X \\ x \mapsto \vec {b} _ {x} \\ \end{array}
$$

Proof (Theorem 5.2)

We prove  $1 \Rightarrow 2$ . Given  $f: X \to UA$ , we have a unique adjunct  $f^{\sharp}: FX \to A$ :

$$
\frac {F X \xrightarrow {\exists ! f ^ {\sharp}} A}{X \xrightarrow {} _ {\forall f} U A}.
$$

By Theorem 5.1,  $\eta_X: X \to UFX$  is a universal arrow from  $X$  to functor  $U$ . If we replace  $F_0$  with  $F$ , we see that diagram (5.16) commutes.

Next, we prove  $2 \Rightarrow 1$ . The assumption gives a function on objects  $F_0$ . We extend it to a functor  $F: \mathcal{X} \to \mathcal{A}$ .

$$
\begin{array}{ccc}X & \xrightarrow{\eta_{X}} & U  F_{0}X\\ f & \Big{\downarrow} & \Big{\downarrow}\\ & & \Big{\downarrow}\\ X^{\prime} & \xrightarrow{\eta_{X^{\prime}}} & U  F_{0}X^{\prime} \end{array} \quad \begin{array}{ccc}F_{0}X\\ & \Big{\downarrow}\\ & \Big{\downarrow}\\ & F_{0}X^{\prime} \end{array}
$$

We seek a morphism  $?: F_0X \to F_0X'$  for  $f: X \to X'$ . We apply  $\sharp$  operation on

$$
\begin{array}{c}X\xrightarrow{\eta_{X}}UF_{0}X\\ \searrow \\ \eta_{X^{\prime}\circ f}\searrow \\ U?\\ UF_{0}X^{\prime} \end{array}
$$

to obtain

$$
\begin{array}{ccc}X\xrightarrow{\eta_{X}}UF_{0}X&F_{0}X\\ \searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\searrow\end{array} ,
$$

where the dashed morphism  $U(\eta_{X^{\prime}}\circ f)^{\sharp}$  is uniquely determined.

We are tempted to define a function on morphisms as follows. From now on we write  $F$  instead of  $F_0$ .

$$
F f = \left(\eta_ {X ^ {\prime}} \circ f\right) ^ {\sharp}.
$$

We must ask ourselves if this assignment complies with the functor axioms. Two tests must be passed.

(1)  $F1_{X} = 1_{FX}$  
(2) For any pair of composable morphisms,  $f: X \to X'$  and  $g: X' \to X''$  the equality  $Fg \circ Ff = F(g \circ f)$  must hold.

First, we examine (1). We have a diagram

![](images/154f105162e575cb7d23ab9521809ac16e9eefdbcb928c4f3bdf29e96935cfdd.jpg)

Compare the two squares on the left.

![](images/df9bfb3bf9a85583124cdcb48b379635b2432be3758ee8afbe62771af6a6a79c.jpg)  
(a)

![](images/4511cbd3277f348f0c86b1a30b9d71324194146e0632b399d293324628036584.jpg)  
(b)

The square with a round edge (a) is commutative because of a chain of mappings of  $1_X$  by functors  $F$  and  $U$ . The  $U_?$  in rectangle (b) must be unique by the assumption. Thus, we have  $F1_X = 1_{FX}$ .

Next, we examine axiom (2).

![](images/f4fde1392dc5fe1ed8ae4ae1d69ef85b198d3ec687e9b8c5b27b73f67e291b2b.jpg)

![](images/b80349b39d6589794ea74867af1d442dcadcc2307b3f8c75e14d74b86ee19f1c.jpg)

Our definition of a function on morphisms gives

$$
F (g \circ f) = (\eta_ {X ^ {\prime \prime}} \circ g \circ f) ^ {\sharp}
$$

$$
F g \circ F f = (\eta_ {X ^ {\prime \prime}} \circ g) ^ {\sharp} \circ (\eta_ {X ^ {\prime}} \circ f) ^ {\sharp}
$$

By uniqueness in the assumption guarantees commutativity for all squares and triangles in the diagram. Therefore, we have

$$
(\eta_ {X ^ {\prime \prime}} \circ g \circ f) ^ {\sharp} = (\eta_ {X ^ {\prime \prime}} \circ g) ^ {\sharp} \circ (\eta_ {X ^ {\prime \prime}} \circ f) ^ {\sharp}.
$$

This shows  $F(g \circ f) = Fg \circ Ff$ , completing the proof that  $F$  is really a functor.

We have shown that the collection of  $\eta_X$  comprises a natural transformation  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$ , and that  $\eta$  is a universal arrow to  $U$ . By Theorem 5.1, we conclude that  $F \dashv U$ .

# 5.6 Adjunction and Category Equivalence

We will see relations between adjunction and category equivalence.

Definition 5.3 A morphism  $f: A \to B$  is called a monomorphism if for any pair of morphisms  $C \xrightarrow[g']{g} A$  the following implication holds:

$$
f \circ g = f \circ g ^ {\prime} \Rightarrow g = g ^ {\prime}.
$$

We also say "  $f$  is monic."

Remark 5.1 In Set, monomorphism=injection. We use the same notation in Definition 5.3.

A function  $f: A \to B$  is called an injection if the following condition holds:

$$
\forall a, a ^ {\prime} \in A. i f f (a) = f \left(a ^ {\prime}\right) t h e n a = a ^ {\prime}.
$$

Suppose  $f$  is an injection. If  $f \circ g = f \circ g'$ , then  $f(g(c)) = f(g'(c))$  for all  $c \in C$ . Since  $f$  is injective, we have  $g(c) = g'(c)$  for all  $c \in C$ . We can conclude that  $g = g'$  and thus  $f$  is monic.

Conversely, suppose  $f$  is monic. Since  $C$  is arbitrary, we can put  $C = \{*\}$ , a singleton set. Let  $a, a' \in A$  be arbitrary pair of elements, and consider two functions  $g: * \mapsto a$  and  $g': * \mapsto a'$ . If  $f(a) = f(a')$ , then  $f \circ g = f \circ g'$ . Since  $f$  is monic, we have  $g = g'$ , therefore  $a = a'$ . Thus,  $f$  is injective.

Definition 5.4 A morphism  $f: A \to B$  is called a epimorphism if for any pair of morphisms  $B \xrightarrow[g']{g} C$  the following implication holds:

$$
g \circ f = g ^ {\prime} \circ f \quad \Longrightarrow \quad g = g ^ {\prime}.
$$

We also say "  $f$  is epic."

Remark 5.2 In Set, epimorphism=surjection. We use the same notation in Definition 5.4.

A function  $f: A \to B$  is called a surjection if the following condition holds:

$$
\forall b \in B. \exists a \in A. b = f (a).
$$

Suppose  $f$  is a surjection. For all  $b \in B$  there exist  $a \in A$  such that  $b = f(a)$ . If  $g \circ f = g' \circ f$ , then

$$
g (b) = g (f (a)) = g ^ {\prime} (f (a)) = g ^ {\prime} (b)
$$

for all  $b \in B$ . We have  $g = g'$ , and thus  $f$  is epic.

Conversely suppose  $f$  is an epimorphism. We suppose also  $f$  is not surjective. Then, we have

$$
\exists b \in B. \forall a \in A. b \neq f (a).
$$

Let  $C' = \{1, 2\} \sqcup C$ . We define two functions  $\bar{g}, \bar{g}' : B \to C'$  as follows.

$$
\begin{array}{l} \bar {g} (x) = \left\{ \begin{array}{l l} 1 & (x = b) \\ g (x) & (x \neq b) \end{array} \right. \\ \bar {g ^ {\prime}} (x) = \left\{ \begin{array}{l l} 2 & (x = b) \\ g ^ {\prime} (x) & (x \neq b) \end{array} \right. \\ \end{array}
$$

We have  $\bar{g} \circ f = \bar{g}' \circ f$  but  $\bar{g} \neq \bar{g}'$ . This contradicts the assumption that  $f$  is an epimorphism. Therefore,  $f$  must be surjective.

Example 5.2 In Top there is a non-surjective epimorphism. Let  $i \colon \mathbb{Q} \to \mathbb{R}$  an embedding. It is clearly non-surjective, but an epimorphism.

Lemma 5.1 Given two morphisms  $e: A \to B$  and  $s: B \to A$  with  $e \circ s = 1_B$ , then we know that  $e$  is an epimorphism and  $s$  is a monomorphism.

Remark 5.3 If we require  $f \circ g = 1_B$  at the same time,  $f$  and  $g$  are isomorphisms.

Proof Let us first prove  $f$  is epic. Assume  $a \circ e = b \circ e$ . If we compose  $s$  from the right, we have

$$
a \circ e \circ s = b \circ e \circ s,
$$

and since  $e \circ s = 1_B$  we further have  $a = b$ , which means that  $e$  is epic.

Next, we prove  $s$  is monic. Assume  $s \circ a = s \circ b$ . If we compose  $e$  from the left, we have

$$
e \circ s \circ a = e \circ s \circ b,
$$

and since  $e \circ s = 1_B$  we further have  $a = b$ , which means that  $s$  is monic.

Definition 5.5 Given two morphisms  $e: A \to B$  and  $s: B \to A$  with  $e \circ s = 1_B$ , morphism  $e$  is called a split epimorphism, and  $s$  is called a split monomorphism. Relations between  $e$  and  $s$  and relations between  $B$  and  $A$  are often phrased:

-  $s: B \to A$  is a section of  $e: A \to B$ .  
-  $e: A \to B$  is a retraction of  $s: B \to A$ .  
-  $B$  is a retract of  $A$ .

Proposition 5.3 Given two functors  $U: \mathcal{A} \to \mathcal{X}$  and  $F: \mathcal{X} \to \mathcal{A}$  with  $F \dashv U$ , we have the following:

(a)  $U$  is faithful  $\Leftrightarrow \varepsilon_{A}: FUA \to A$  is an epimorphism for any  $A \in \mathrm{Obj}(\mathcal{A})$ .  
(b)  $U$  is full  $\Leftrightarrow \varepsilon_{A}: FUA \to A$  is a split monomorphism for all  $A \in \mathrm{Obj}(\mathcal{A})$ .  
(c)  $U$  is full and faithful  $\Leftrightarrow \varepsilon_{A}: FUA \to A$  is an isomorphism for all  $A \in \mathrm{Obj}(\mathcal{A})$ .

Proof The adjunction is depicted as follows.

![](images/d1bdc0dd158476e639833e2fe9b7704a574cb2e95af06eac0ee55beea6e45175.jpg)

We consider the composition  $U_{A,A'}$  with  $b_{UA,A'}^{-1}$ .

![](images/df50a47c487f481d3345e22fd7678c0e8ecadcb4d64c8d261fd2c4aef055ba4e.jpg)

Since  $b_{UA,A'}^{-1}$  is bijective, we have the following equivalences.

$U_{A,A'}$  is injective  $\Leftrightarrow f\mapsto f\circ \varepsilon_A$  is injective

$U_{A,A'}$  is surjective  $\Leftrightarrow f\mapsto f\circ \varepsilon_A$  is surjective

We prove (a).

$U$  is faithful

$\Leftrightarrow$  For any pair  $(A,A^{\prime})$ $U_{A,A^{\prime}}$  is injective  
\Leftrightarrow For any pair  $(A,A^{\prime})$ $f\mapsto f\circ \varepsilon_{A}$  is injective  $(\mathcal{A}(A,A^{\prime})\to \mathcal{A}(FUA,A^{\prime}))$

That  $f \mapsto f \circ \varepsilon_{A}$  is injective means for any pair  $f_{1}, f_{2}$  if  $f_{1} \circ \varepsilon_{A} = f_{2} \circ \varepsilon_{A}$  then  $f_{1} = f_{2}$ , therefore means  $\varepsilon_{A}$  is an epimorphism.

We prove (b).

$U$  is full

$\Leftrightarrow$  For any pair  $(A,A^{\prime})$ $U_{A,A^{\prime}}$  is surjective  
\Leftrightarrow For any pair  $(A,A^{\prime})$ $f\mapsto f\circ \varepsilon_{A}$  is surjective  $(\mathcal{A}(A,A^{\prime})\to \mathcal{A}(FUA,A^{\prime}))$

Suppose  $f \circ \varepsilon_A = 1_{FUA}$  is surjective for any pair  $(A, A')$ . We specialize the case as  $A' = FUA$  and  $f \circ \varepsilon_A = 1_{FUA}$ .

$$
F U A \xrightarrow [ f \circ \varepsilon_ {A} ]{\varepsilon_ {A}} A \xrightarrow [ ]{f} A ^ {\prime} \quad \stackrel {{\text {s p e c i a l i z e s}}} {{\Longrightarrow}} F U A \xrightarrow [ 1 _ {F U A} ]{\varepsilon_ {A}} A \xrightarrow [ ]{\exists ! h} F U A
$$

By surjectivity, there exists  $h: A \to FUA$  such that  $h \circ \varepsilon_A = 1_{FUA}$ , which shows that  $\varepsilon_A$  is a split monomorphism.

Conversely, we assume that  $\varepsilon_{A}$  is a split monomorphism. There exists  $h:A\to$  FUA such that  $h\circ \varepsilon_{A} = 1_{FUA}$ . Given  $g:FUA\rightarrow A^{\prime}$ , we put  $f = g\circ h$ . Then, we have

$$
f \circ \varepsilon_ {A} = g \circ h \circ \varepsilon_ {A} = g \circ 1 _ {F U A},
$$

which shows that  $f\mapsto f\circ \varepsilon_{A}$  is surjective. The diagram

$$
F U A \xrightarrow {\begin{array}{c} h \\ \varepsilon_ {A} \end{array} } A \xrightarrow {\exists f} A ^ {\prime}
$$

may be a help to get the idea.

We prove (c).

Having proved (a) and (b), we need only apply the following general fact:

$$
\text {i s o m o r p h i s m} \Leftrightarrow \text {e p i m o r p h i s m a n d s p l i t m o n o m o r p h i s m}.
$$

We briefly reproduce the proof for  $\varepsilon_{A}$

$(\Rightarrow)$  is trivial.

$(\Leftarrow)$  Suppose  $\varepsilon_{A}$  is a split monomorphism. There exists  $u:A\to FUA$  such that  $u\circ \varepsilon_{A} = 1_{FU A}$ . Applying  $\varepsilon_{A}\circ$  from the left to the both sides, we get

$$
\varepsilon_ {A} \circ u \circ \varepsilon_ {A} = \varepsilon_ {A} = 1 _ {A} \circ \varepsilon_ {A}.
$$

Since  $\varepsilon_{A}$  is an epimorphism, we conclude that  $\varepsilon_{A} \circ u = 1_{A}$ . Thus,  $\varepsilon_{A}$  is an isomorphism.

Proposition 5.4 Given two functors  $U: \mathcal{A} \to \mathcal{X}$  and  $F: \mathcal{X} \to \mathcal{A}$ , the following two conditions are equivalent:

1. Functors  $U$  and  $F$  give an equivalence of  $\mathcal{A}$  and  $\mathcal{X}$ . To be more specific, there exist natural isomorphisms  $\alpha : \operatorname{Id}_{\mathcal{X}} \to UF$  and  $\beta : FU \to Id_{\mathcal{A}}$ .  
2.  $F \vdash G$ , and unit  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$  and counit  $\varepsilon : FU \to \operatorname{Id}_{\mathcal{A}}$  are natural isomorphisms.

Remark 5.4 When condition 2 is satisfied, functors  $U$  and  $F$  are said to give an adjoint equivalence of categories  $\mathcal{A}$  and  $\mathcal{X}$ . The proposition claims that the concepts

of category equivalence and adjoint equivalence are equivalent. Note that  $\alpha$  and  $\beta$  in condition 1 are not necessarily a unit and counit of the adjunction.

Proof  $2 \Rightarrow 1$  is easy. Set  $\alpha = \eta$  and  $\beta = \varepsilon$ , and forget about the fact that they came from an adjunction.

We prove  $1 \Rightarrow 2$ . We construct an adjunction with the following strategy:

- construct a correspondence between  $\mathcal{A}(FX, A)$  and  $\mathcal{X}(X, UA)$  natural in  $X$  and  $A$ ,  
- construct  $\eta$  and  $\varepsilon$  out of  $\alpha$  and  $\beta$ ,  
- prove that  $\eta$  and  $\varepsilon$  are both natural isomorphisms.

Recall that  $F$  and  $G$  are full and faithful functors, and that they both are essentially surjective on objects. See Proposition 2.1 and Remark 2.3.

Take an arbitrary pair of  $A \in \mathrm{Obj}(\mathcal{A})$  and  $X \in \mathrm{Obj}(\mathcal{X})$ . Given a morphism  $f: X \to UA$ , we construct a morphism  $f^\sharp: FX \to A$ . Let us consider the following diagram.

![](images/0f4cd06662d36b0bf3a4b356ef892bb1a4ae64ae8979e38e887788dab34512de.jpg)

Since  $U$  is full and faithful,

$$
f ^ {\sharp} = U _ {F X, A} ^ {- 1} (f \circ \alpha_ {X} ^ {- 1})
$$

exists. We have  $Uf^{\sharp} = f \circ \alpha_{X}^{-1}$ . This is the only candidate available for an adjunct.

$$
\frac {F X \xrightarrow {f ^ {\sharp}} A}{X \xrightarrow {} f U A} = \frac {F X \xrightarrow {1 _ {F X}} F X \xrightarrow {f ^ {\sharp}} A}{X \xrightarrow {} \alpha_ {X} U F X \xrightarrow {} U f ^ {\sharp}} U A.
$$

We still have to show naturality in  $X$  and  $A$ . From now on we write simply  $U^{-1}$  for the inverse function on morphisms.

We prove naturality in  $X$ . We have to show for any morphism  $X' \to X$

$$
\begin{array}{c} F X ^ {\prime} \xrightarrow {F x} F X \xrightarrow {f ^ {\sharp}} A \\ \hline X ^ {\prime} \xrightarrow [ x ]{} X \xrightarrow [ f ]{U} A \end{array}
$$

holds. In other words,

$$
(f \circ x) ^ {\sharp} = f ^ {\sharp} \circ F x.
$$

The situation is concisely described by the following diagram.

![](images/755ccc04c6fd50fd01ffc9e3baf8a051870024dbc9d7ad47ff14a0c18dfa0a93.jpg)

![](images/c4313e15284b7bcdc7756f38b18e034b679a00065b76fead4b920f72702f7e21.jpg)

The square on the right is commutative due to the natural transformation  $\alpha$ . The triangle below commutes since it is just a composition of morphisms. We show the triangle on the left commutes as follows.

$$
\begin{array}{l} (f \circ x) ^ {\sharp} = U ^ {- 1} (f \circ x \circ \alpha_ {X ^ {\prime}} ^ {- 1}) \\ = U ^ {- 1} \left(f \circ \alpha_ {X} ^ {- 1} \circ U F x\right) \\ = U ^ {- 1} \left(f \circ \alpha_ {X} ^ {- 1}\right) \circ U ^ {- 1} (U F x) \\ = f ^ {\sharp} \circ F x \\ \end{array}
$$

Thus, we established naturality in  $X$ .

Next, we prove naturality in  $A$ . We have to show for any morphism  $a: A \to A'$

$$
\frac {F X \xrightarrow {f ^ {\sharp}} A \xrightarrow {a} A ^ {\prime}}{X \xrightarrow {} f U A \xrightarrow {} U a}
$$

holds. In other words,

$$
(U a \circ f) ^ {\sharp} = a \circ f ^ {\sharp}.
$$

The situation is concisely described by the following diagram.

![](images/ea5e9b30bb9cf3a2570c60750823f7bb96080bcc94d8146e4ad152e68d227a4a.jpg)

![](images/21b7815db2cdc7b37a3b98e9a28bbac732d23c16eeb687eb9e382f671f6eb98a.jpg)

The two triangles on the right are commutative since both are just a composition of morphisms. We show the triangle on the left commute. Let us trace the rewriting:

$$
\begin{array}{l} (U a \circ f) ^ {\sharp} = U ^ {- 1} (U a \circ f \circ \alpha_ {X} ^ {- 1}) \\ = a \circ U ^ {- 1} (f \circ \alpha_ {X} ^ {- 1}) \\ = a \circ f ^ {\sharp} \\ \end{array}
$$

Thus, we get naturality in  $A$ .

We want to make clear the relation between the pair of natural transformations  $\alpha : \operatorname{Id}_{\mathcal{X}} \to UF$  and  $\beta : F U \to \operatorname{Id}_{\mathcal{A}}$  and the pair of  $\eta$  and  $\varepsilon$ .

Let us consider the diagram:

![](images/bd624cea3d3f79f36b2c98adce05b0f5e07798589a44149ae0e9661843c2d703.jpg)

We assign  $A = FX$  and  $f^{\sharp} = 1_{FX}$  and rewrite this diagram.

![](images/49f1ea11710ca4fd687d2f7fb36e2fde6fdce270f87a1850240a52d3fa9fa38a.jpg)

This shows  $\eta = \alpha$

Next, we study  $\varepsilon$ .

Let us consider the diagram:

![](images/89ea3f8ac8b6120842080a739c9dd7aa52cf7ba6b90ce3f218800fe66293f104.jpg)

We assign  $X = UA$  and  $f = 1_{UA}$  and rewrite this diagram.

![](images/8fd2a335f99d97c82be2280e5f985ed88add25fea705cd7cb142b11aad8e2af1.jpg)

This shows

$$
\varepsilon_ {A} = U ^ {- 1} (\alpha_ {U A} ^ {- 1}).
$$

![](images/9d29a8b1ce8274b5af0827659e687da405c10c4fb0366ba070a57a56103f4bc6.jpg)

# 5.7 Global Naturality of Adjunction

Some people feel that the naturality explained so far is a little bit unnatural. Let  $\mathcal{A}$  and  $\mathcal{X}$  be locally small categories. Consider the adjunction

$$
\mathcal {A} (F X, A) \cong \mathcal {X} (X, U A).
$$

LHS can be seen as a functor that sends  $(X,A)$  to a set:

$$
\mathcal {X} ^ {\mathrm {o p}} \times \mathcal {A} \rightarrow \mathbf {S e t}
$$

RHS can also be seen as a functor that sends  $(X,A)$  to a set:

$$
\mathcal {X} ^ {\mathrm {o p}} \times \mathcal {A} \rightarrow \mathbf {S e t}
$$

We show that both are really functors that are naturally isomorphic. We see this natural isomorphism establishes an adjunction.

(1) We prove  $\mathcal{A}(F, -, -): \mathcal{X}^{\mathrm{op}} \times \mathcal{A} \to \mathbf{Set}$  is a functor.

The function on objects is given by

$$
\mathcal {A} (F -, -) (X, A) = \mathcal {A} (F X, A)
$$

for all  $(X,A)\in \mathrm{Obj}(\mathcal{X}^{\mathrm{op}}\times \mathcal{A})$

Let  $(X, A)$  and  $(X', A')$  be any pair of objects in  $\mathcal{X}^{\mathrm{op}} \times \mathcal{A}$ . A morphism from  $(X, A)$  to  $(X', A')$  is a pair  $(x, a)$  where  $x: X' \to X$  is a morphism in  $\mathcal{X}$  and  $a: A \to A'$  is a morphism in  $\mathcal{A}$ . We write it as

$$
(x, a): (X, A) \rightarrow (X ^ {\prime}, A ^ {\prime}).
$$

We want to send this morphism to a function in a way

$$
(x, a) \stackrel {{\mathcal {A} (F -, -)}} {{\longmapsto}} \binom {\mathcal {A} (F X, A) \longrightarrow \mathcal {A} (F X ^ {\prime}, A ^ {\prime})} {f \longmapsto a \circ f \circ F x}
$$

We have to check if this definition conforms to the axioms of functors.

First we check the image of  $(1_X, 1_A)$ , the identity morphism in  $\mathcal{X}^{\mathrm{op}} \times \mathcal{A}$ . We have

$$
f = 1 _ {A} \circ f \circ F (1 _ {X}).
$$

since  $F(1_X) = 1_{FX}$ , which shows

$$
\mathcal {A} (F -, -) \left(1 _ {X}, 1 _ {A}\right) = 1 _ {\mathcal {A} \left(F X, A\right)}.
$$

Next, we check if the following triangle commutes:

$$
(X, A) \xrightarrow [ (x \circ x ^ {\prime}, a ^ {\prime} \circ a) ]{(x , a)} (X ^ {\prime}, A ^ {\prime}) \xrightarrow [ (x \circ x ^ {\prime}, a ^ {\prime} \circ a) ]{(x ^ {\prime}, a ^ {\prime})} (X ^ {\prime \prime}, A ^ {\prime \prime}), \tag {5.17}
$$

where  $x: X' \to X$ ,  $x': X'' \to X'$ ,  $a: A \to A'$ ,  $a': A' \to A''$ . We apply  $\mathcal{A}(F, -, -)$  to this triangle to get the following:

$$
\begin{array}{c} \mathcal {A} (F X, A) \xrightarrow {f \mapsto a \circ f \circ F x} \mathcal {A} (F X ^ {\prime}, A ^ {\prime}) \xrightarrow {f \mapsto a ^ {\prime} \circ f \circ F x ^ {\prime}} \mathcal {A} (F X ^ {\prime \prime}, A ^ {\prime \prime}). \\ \hskip 1 4. 2 2 6 3 7 8 p t f \mapsto (a ^ {\prime} \circ a) \circ f \circ F (x \circ x ^ {\prime}) \end{array}
$$

We have to see if this triangle commutes. The composition of the upper two edges is as follows.

$$
a ^ {\prime} \circ a \circ f \circ F x \circ F x ^ {\prime}
$$

Since  $Fx \circ Fx' = F(x \circ x')$ , we see that the triangle commutes. This completes the proof that  $\mathcal{A}(F-, -)$  is a functor.

(2) We prove  $\mathcal{X}(-,U -):\mathcal{X}^{\mathrm{op}}\times \mathcal{A}\to \mathbf{Set}$  is a functor.

The function on objects is given by

$$
\mathcal {X} (-, U -) (X, A) = \mathcal {X} (X, U A)
$$

for all  $(X,A)\in \mathrm{Obj}(\mathcal{X}^{\mathrm{op}}\times \mathcal{A})$

Let  $(X, A)$  and  $(X', A')$  be any pair of objects in  $\mathcal{X}^{\mathrm{op}} \times \mathcal{A}$ . A morphism from  $(X, A)$  to  $(X', A')$  is a pair  $(x, a)$  where  $x: X' \to X$  is a morphism in  $\mathcal{X}$  and  $a: A \to A'$  is a morphism in  $\mathcal{A}$ . We write it as

$$
(x, a): (X, A) \rightarrow (X ^ {\prime}, A ^ {\prime}).
$$

We want to send this morphism to a function in a way

$$
(x, a) \stackrel {{\mathcal {X} (-, U -)}} {{\longmapsto}} \left( \begin{array}{c} \mathcal {X} (X, U A) \longrightarrow \mathcal {X} (X ^ {\prime}, U A ^ {\prime}) \\ f \longmapsto U a \circ f \circ x \end{array} \right)
$$

Identity morphisms are mapped to identity morphisms. We apply  $\mathcal{X}(-, U-)$  to the triangle 5.17 to get the following:

$$
\begin{array}{c} \mathcal {X} (X, U A) \xrightarrow {f \mapsto U a \circ f \circ x} \mathcal {X} (X ^ {\prime}, U A ^ {\prime}) \xrightarrow {f \mapsto U a ^ {\prime} \circ f \circ x ^ {\prime}} \mathcal {X} (X ^ {\prime \prime}, U A ^ {\prime \prime}). \\ \hskip 1 4. 2 2 6 3 7 8 p t f \mapsto U (a ^ {\prime} \circ a) \circ f \circ (x \circ x ^ {\prime}) \end{array}
$$

Since  $Ua^{\prime}\circ Ua = U(a^{\prime}\circ a)$ , we see that this triangle commutes. This completes the proof that  $\mathcal{X}(-,U -):\mathcal{X}^{\mathrm{op}}\times \mathcal{A}\to \mathbf{Set}$  is a functor.

(3)  $\alpha : \mathcal{A}(F, -, -) \to \mathcal{X}(-, U)$  is a natural isomorphism if the square on the right commutes and all  $\alpha_{(X,A)}$  are isomorphisms in the following diagram.

![](images/346a5f2ac73f1ee4d90f9706b96cf607c4bc8c3d3d123ef6d06fe7a7b63d7447.jpg)

The above properties are guaranteed by Eq. (5.1).

Thus,  $F \dashv U$  is equivalent to the existence of a natural isomorphism

$$
\alpha \in [ \mathcal {X} ^ {\mathrm {o p}} \times \mathcal {A}, \operatorname {S e t} ] (\mathcal {A} (F -, -), \mathcal {X} (-, U -)).
$$

We consumed many words and sentences to define the functors involved. Such efforts let us formulate the naturality with a few sentences.

# 5.8 Adjunctions and Limits

We study the relationships between adjunctions and limits. We showed the operation of taking limits  $\varprojlim$  can be seen as a functor  $[J, \mathcal{A}] \to \mathcal{A}$  in Sect. 4.5.

Definition 5.6 Let  $J$  be a small category, and  $\mathcal{A}$  a category. Given  $A\in \mathrm{Obj}(\mathcal{A})$  we define a functor  $(J$ -shaped diagram)  $\Delta_A:J\to \mathcal{A}$  as follows.

- the function on objects maps all the objects of  $J$  to  $A$ .  
- the function on morphisms maps all the morphisms of  $J$  to  $1_A$ .

Such a functor  $\Delta_A$  is called a diagonal functor.

From now on, we assume  $\mathcal{A}$  is locally small to deal with functor category  $[J,\mathcal{A}]$ . We extend the function

$$
\begin{array}{l} \Delta : \operatorname {O b j} (\mathcal {A}) \rightarrow \operatorname {O b j} ([ J, \mathcal {A} ]) \\ A \mapsto \Delta_ {A} \\ \end{array}
$$

to a functor  $\mathcal{A} \rightarrow [J, \mathcal{A}]$  by defining functions on morphisms. Given a morphism  $a: A \rightarrow A'$  in  $\mathcal{A}$ , we assign a morphism  $\Delta_A \rightarrow \Delta_{A'}$  in the functor category  $[J, \mathcal{A}]$ , namely a natural transformation  $\alpha(a): \Delta_A \rightarrow \Delta_{A'}$  defined by

$$
\alpha (a) _ {j}: \Delta_ {A} (j) \to \Delta_ {A ^ {\prime}} (j),
$$

where  $\alpha(a)_j = a$  regardless of  $j$ . Such an assignment  $\alpha(a)$  is a natural transformation since the square on the right commutes in the following diagram.

![](images/3534dfd088131390d75487c634ed0486b0b83b994e8cc53ba95aa567b6f32799.jpg)

Thus,  $A\mapsto \Delta_A$  is extended to a functor from  $\mathcal{A}$  to  $[J,\mathcal{A}]$ .

Proposition 5.5 We have the following two natural isomorphisms.

$$
\begin{array}{l} \mathscr {A} (A, \varprojlim F) \simeq [ J, \mathscr {A} ] (\Delta_ {A}, F) \\ \mathscr {A} (\varinjlim F, A) \simeq [ J, \mathscr {A} ] (F, \Delta_ {A}) \\ \end{array}
$$

Remark 5.5 The limit functor is a right adjoint of  $\Delta_{-}$ . The colimit functor is a left adjoint of  $\Delta_{-}$ . Some authors use these facts as definitions of limits and colimits.

Remark 5.6 Let us sum up all the foregoing discussions. A natural transformation from  $\Delta_A$  to  $F$  is equivalent to a cone from  $A$  to  $F$ .

$$
\mathscr {A} (A, \varprojlim F) \simeq [ J, \mathscr {A} ] (\Delta_ {A}, F) \simeq \operatorname {C o n e s} (A, F)
$$

A natural transformation from  $F$  to  $\Delta_A$  is equivalent to a cocone from  $F$  to  $A$ .

$$
\mathscr {A} (\varinjlim F, A) \simeq [ J, \mathscr {A} ] (F, \Delta_ {A}) \simeq \operatorname {C o n e s} (F, A)
$$

We omit the proof since it is just the rephrasing of the definitions.

# Monads

Monads appear in various disciplines, especially in the science of computing. Understanding phenomena in computing requires more than a simple scheme of input and output correspondence. Non-deterministic computing, stateful computing, and computing that may fail are all everyday life in computer science. Moggi's ideas are lucid in formulating such uncertain mathematical objects in category theory. The Kleisli triple is the main target of this chapter.

# 6.1 Kleisli Triples

Moggi [1] regards a computer program as a process  $TB$  of computing a value of type  $B$  on input of type  $A$ , where, in our case,  $A$  and  $B$  are types such as Int, Float, or String,  $T$  is a functor such as the List or Maybe functors. The List functor realizes non-deterministic computation. The Maybe functor realizes computation that may fail. Monads or Kleisli triples come into play when we want to concatenate pieces of computation.

Definition 6.1 Given a category  $\mathcal{C}$ , we consider a triple  $(T, \eta, (-)^{\sharp})$ , where

-  $T$  is a function that sends each  $A \in \mathrm{Obj}(\mathcal{C})$  to  $TA \in \mathrm{Obj}(\mathcal{C})$ .  
-  $\eta$  is a family of morphisms  $\{\eta_A : A \to TA \mid A \in \mathrm{Obj}(\mathcal{C})\}$ .  
$(-)^{\sharp}_{A,B}$  is a function

$$
(-) _ {A, B} ^ {\sharp}: \mathscr {C} (A, T B) \rightarrow \mathscr {C} (T A, T B)
$$

for all pairs of  $A, B \in \mathrm{Obj}(\mathcal{C})$ . Since there is no possibility of confusion, we omit the subscripts and write as  $(-)^{\sharp}$ .

Such a triple is called a Kleisli triple on  $\mathcal{C}$  if it satisfies the following three conditions.

(1)  $f^{\sharp} \circ \eta_{A} = f$

(2)  $\eta_A^\sharp = 1_{TA}$

(3)  $g^{\sharp} \circ f^{\sharp} = (g^{\sharp} \circ f)^{\sharp}$

![](images/6b73402a8aa35f4efa59dc4032565942d16cdc6eb1632e70c2aa7925c06112f0.jpg)

![](images/a4515ac4e25f3900c98f411e622eb211db49785d2f253e433f98f2043630bcc1.jpg)

![](images/9e4cdaf12f34ac88fef50aab436dd8b214763d0550d479a64c8ecaf74e47aae0.jpg)

Remark 6.1 Condition (2) can be obtained from condition (1) by setting  $f = \eta_A$  in the accompanying diagram. We call a functor from a category  $\mathcal{C}$  to itself an endofunctor. We will show:

- A function on objects  $T$  can be extended to an endofunctor by augmenting a function on morphisms.  
- Having established  $T$  as a functor, the family of morphisms  $\eta$  turns out to be a natural transformation.

We will further show that the concept of Kleisli triples is equivalent to that of Monads.

In the following sections, we discuss models for

- non-deterministic computation,  
- computation with output,  
- computation by continuation passing, and  
- computation that may fail

in order.

Proposition 6.1 The function  $T$  appearing in a Kleisli triple  $(T, \eta, (-)^{\sharp})$  can be extended to an endofunctor  $T: \mathcal{C} \to \mathcal{C}$  by augmenting a function on morphisms.

Proof We first seek a function on morphisms compatible with  $T$ . For any  $f \in \mathcal{C}(A, B)$  we define  $Tf \in \mathcal{C}(TA, TB)$  by  $Tf = (\eta_B \circ f)^\sharp$  that makes the two triangles commute and thereby does the square in the following diagram.

# 6.1 Kleisli Triples

![](images/98cd8707143dbb95fb31679811e27e1667aafd242e03bd30a7e117283742deb3.jpg)

We show that  $T1_{A} = 1_{TA}$ , which is in the first place required for  $T$  to be a functor. Setting  $B = A$  and  $f = 1_{A}$  in the diagram above, we have the following.

![](images/28b80e07a4345a30333cd3eae6bd5ff920710ac38df67c7dc37b9033cd4e4a5b.jpg)

Using condition (2) of Definition 6.1, we have

$$
T 1 _ {A} = \eta_ {A} ^ {\sharp} = 1 _ {T A}.
$$

Next, we show that  $T(g \circ f) = Tg \circ Tf$ . We add two morphisms  $f$  and  $g$  to the diagram accompanying the condition (3) in Definition 6.1 and obtain the following.

![](images/9ddc18c69607565397ad781b3afcfbd1e9552c714f04ed6fff9d3b7dd3e74349.jpg)

The goal is to show the commutativity of the triangle above that looks like a crescent moon. We can do it as follows.

$Tg\circ Tf = (\eta_{C}\circ g)^{\sharp}\circ (\eta_{B}\circ f)^{\sharp}$  definition of  $T$  
$= ((\eta_{C}\circ g)^{\sharp}\circ \eta_{B}\circ f)^{\sharp}$  condition (3) for  
= (9C o g o f) commutativity of the 2nd triangle from right  
$= T(g\circ f)$  definition of  $T$

We conclude that the so-extended  $T$  is a functor.

![](images/1ab31966cdcde89c23e70913666d01c1e507fa52bb5efce0096db503dcb0b4a0.jpg)

From now on, we regard  $T$  appearing in a Kleisli triple as an endofunctor.

Proposition 6.2 Given a Kleisli triple  $(T, \eta, (-)^{\sharp})$ , the family of morphisms  $\eta$  is a natural transformation from the identity functor  $\operatorname{Id} : \mathcal{C} \to \mathcal{C}$  to  $T : \mathcal{C} \to \mathcal{C}$ . Namely, we have a natural transformation  $\operatorname{Id} \to T$ .

Proof The promotion of  $T$  to a functor tells us almost completely the naturality of  $\eta$ . But, let us try to put it in a commutative diagram below.

![](images/3c8d8ee6b1c4b45597475e3f0ea7245ac51f007dc86cc64d2c1cea70daa008a4.jpg)

The commutativity of the trapezoid at right comes from the definition of  $T$ , which is exactly the naturality of  $\eta : \mathrm{Id} \to T$ .

# 6.2 Moggi' Theory

We will see Moggi's ideas of computation in the following order.

- non-deterministic computation,  
- computation with output,  
- computation by continuation passing, and  
- computation that may fail

The  $\sharp$  operator in a Kleisli triple corresponds to

```erlang
$(=<<)$  : Monad m => (a -> mb) -> ma -> mb
```

in Haskell. It is a flipped version of the more familiar bind operator

```txt
$(>> =)$  : Monad m  $\Rightarrow$  mA-> (a -> mb) -> mb
```

We will discuss Monads later.

# 6.2.1 Non-determinism and the List Functor

We will embed the list functor into a Kleisli triple.

Listing 6.1 List as a Kleisli triple  
```txt
1 module NonDeterministic where 2 -- The List functor 3
```

```haskell
4 type T = ([])  
5  
6 -- Definition of  
7 --- eta :: A -> TA  
8 -- plays the role of  
9 --- return :: (Monad m) => a -> ma  
10 --- where m = T.  
11  
12 eta :: a -> Ta  
13 eta a = [a]  
14  
15 -- Definition of  
16 --- (-)^# :: Hom(A, TB) -> Hom(TA, TB)  
17 -- plays the role of  
18 --- (=<<) :: (Monad m) => (a -> ma) -> ma -> mb  
19 --- where m = T.  
20  
21 sharp :: (a -> Tb) -> Ta -> Tb  
22 sharp f [] = []  
23 sharp f (x:xs) = f x ++ sharp f xs  
24  
25  
26 -- Test data  
27  
28  
29 testFuncs = [(\\x -> [0,x,0]), \\x -> [0,x,x,0]), \\x -> [0,x,x,x,0])  
30  
31  
32  
33 -- Test1 for  
34 --- f# o eta_A = f  
35 -- the theoretical goal in code  
36 --- sharp f . eta == f  
37 -- written extensionally  
38 --- (sharp f . eta) a == f a  
39  
40 test1 = map (\f -> (sharp f . eta) 10 == f 10) testFuncs  
41 test1detail = map (\f -> (sharp f. eta) 10) testFuncs  
42  
43  
44 -- Test2 for  
45 --- eta_A# = id_TA  
46 -- the theoretical goal in code  
47 --- sharp eta == id  
48 -- written extensionally  
49 --- sharp eta (ta::T a) == (ta::T a)  
50  
51 testLists = [[], [1], [2,3], [4,5,6]]  
52  
53 test2 = map (\xs -> sharp eta xs == xs) testLists  
54 test2detail = map (\xs -> sharp eta xs) testLists  
55  
56  
57 -- Test3 for  
58 --- g^# o f^# = (g^# o f)^#
```

```haskell
59 -- the theoretical goal in code  
60 --- sharp g . sharp f == sharp (sharp g . f)  
61 -- written extensionally  
62 --- (sharp g . sharp f) (ta::T a) ==  
63 --- sharp (sharp g . f) (ta::T a)  
64  
65 test3cases = [(g,f,d) | g <- testFuncs,  
66 f <- testFuncs,  
67 d <- testLists]  
68  
69 test3 = map ( $\text{g,f,d}$ ) ->  
70 (sharp g . sharp f) d ==  
71 (sharp (sharp g . f)) d)  
72 test3cases
```

Line 4 gives an alias to the list functor.

Lines 6-23 implement  $\eta$  and  $\sharp$ .

Test data and code follow. Successful construction must satisfy the following conditions:

(1)  $f^{\sharp} \circ \eta_{A} = f$  
(2)  $\eta_A^\sharp = 1_{TA}$  
(3)  $g^{\sharp} \circ f^{\sharp} = (g^{\sharp} \circ f)^{\sharp}$

Lines 29-31 define test data. test1 in lines 40-41, test2 in lines 51-54, and test3 in lines 69-72 are tests for conditions (1), (2), and (3), respectively.

We do not provide proof, instead perform tests enough to give us some confidence. After loading the program, we carry out tests as follows.

```txt
\*NonDeterministic> test1   
[True,True,True]   
\*NonDeterministic> test2   
[True,True,True,True]   
\*NonDeterministic> test3   
[True,True,True,True,..True,True]
```

# 6.2.2 Computation with Output

In the following sample code, the results of consecutive computation are appended to an accumulator string in order.

Listing 6.2 CalcWithOutput.hs  
```txt
1 module CalcWithOutput where
2 -- Building a Kleisli triple
3 -- for a program with simple output
```

```haskell
4   
5 newtype Ta = T {unT :: String -> (a,String)}   
6   
7 -- Definition of   
8 ---- (-)^# :: Hom(A,TB) -> Hom(TA,TB)   
9 -- plays the role of   
10 ---- return :: (Monad m) => a -> ma   
11 ---- where m = T.   
12   
13 eta :: a -> Ta   
14 eta x = T (\s -> (x, s))   
15   
16 -- Definition of   
17 ---- (-)^# :: Hom(A,TB) -> Hom(TA,TB)   
18 -- plays the role of   
19 ---- (=<<) :: (Monad m) => (a -> ma) -> ma -> mb   
20 ---- where m = T.   
21   
22 sharp :: (a -> Tb) -> (Ta -> Tb)   
23 sharp f h = T (\st -> let   
24 y,st2) = unT h st   
25 (z,st3) = unT (f y) st2   
26 in   
27 (z,st3))   
28   
29   
30   
31 -- Test data   
32   
33   
34 f1 :: Integer -> T Integer   
35 f1 x = T (\s -> (x^2,   
36 s ++ show x ++ "^2=" ++ show (x^2) ++ ".\n"))   
37   
38   
39 f2 :: Integer -> T Float   
40 f2 x = T (\s -> (sqrt(fromInteger x),   
41 s ++ "sqrt of " ++ show x ++   
42 " is " ++ show (sqrt(fromInteger x)) ++ ".\n"))   
43   
44   
45   
46 testArgs = [(v, s) | v<- [10,100],   
47 s<- ["","----", "hello"]]   
48   
49 test2f1 = [ unT (sharp eta (f1 v)) s == unT (f1 v) s | (v,s) <- testArgs ]   
50   
51   
52 test2f2 = [ unT (sharp eta (f2 v)) s == unT (f2 v) s | (v,s) <- testArgs ]   
53
```

```haskell
59 ---- sharp f . eta = id   
60 -- written extensionally   
61 ---- (sharp f . eta) a == f a   
62 -- fully extensionally   
63 ---- unT ((sharp f . eta) (x::Int)) (s::String) ==   
64 ---- unT (f (x::Int)) (s::String)   
65   
66 test11 = unT ((sharp f1 . eta) 10) "" == unT (f1 10) ""   
67 test11detail = unT ((sharp f1 . eta) 10) ""   
68   
69 test12 = unT ((sharp f2 . eta) 10) "" == unT (f2 10) ""   
70 test12detail = unT ((sharp f2 . eta) 10) ""   
71   
72   
73 -- Test2 for   
74 ---- eta_A^# = id_(TA)   
75 -- the theoretical goal in code   
76 ---- sharp eta == id   
77 -- written extensionally   
78 ---- sharp eta (ta::T a) == (ta::T a)   
79 -- fully extensionally   
80 ---- unT (sharp eta (ta::T a)) (s::String) ==   
81 ---- unT (ta::T a) (s::String)   
82   
83 test21 = unT (sharp eta (f1 10)) "" == unT (f1 10) ""   
84 test22 = unT (sharp eta (f2 10)) "" == unT (f2 10) ""   
85   
86   
87 -- Test3 for   
88 ---- g^# o f^# = (g^# o f)^#   
89 -- the theoretical goal in code   
90 ---- sharp g . sharp f == sharp (sharp g . f)   
91 -- written extensionally   
92 ---- (sharp g . sharp f) (ta::T a) ==   
93 ---- sharp (sharp g . f) (ta::T a)   
94 -- fully extensionally   
95 ---- unT ((sharp g . sharp f) (ta::T a)) (s::String) ==   
96 ---- unT (sharp (sharp g . f) (ta::T a)) (s::String)   
97   
98 test31 = unT ((sharp f2 . sharp f1) (eta 10)) "" ==   
99 unT (sharp (sharp f2 . f1) (eta 10)) ""   
100   
101 test3 = [unT ((sharp f2 . sharp f1) (eta v)) s ==   
102 unT (sharp (sharp f2 . f1) (eta v)) s |   
103 (v,s) <- testArgs ]   
104   
105 -- other tests   
106 (xTest1, stTest1) =   
107 (unT $ sharp f2 $ sharp f1 $ eta 10) ""
```

Line 5 defines a functor  $T$ . Lines 13-14 implement  $\eta$  as a function eta. Lines 22-28 implement  $(-)^{\sharp}$  as a function sharp. Lines 30 and later prepare test data and code.

Successful construction must satisfy the following conditions:

(1)  $f^{\sharp} \circ \eta_{A} = f$  
(2)  $\eta_A^\sharp = 1_{TA}$  
(3)  $g^{\sharp} \circ f^{\sharp} = (g^{\sharp} \circ f)^{\sharp}$

Lines 30-53 prepare test data. test11 and test12 in lines 56-70, test21 and test22 in lines 83-84, and test3 in line 101 are tests for conditions (1), (2), and (3), respectively. Lines 106-107 give a total test.

Tests are carried out as follows.

```txt
\*CalcWithOutput> test11   
True   
\*CalcWithOutput> test12   
True   
\*CalcWithOutput> test21   
True   
\*CalcWithOutput> test22   
True   
\*CalcWithOutput> test3   
[True,True,True,True,True,True]   
\*CalcWithOutput>
```

Other suggested tests are given as follows.

```txt
\*CalcWithOutput> (unT $ unitT 10) ""  
(10, "")  
\*CalcWithOutput> xTest1  
10.0  
\*CalcWithOutput> putStr stTest1  
10^2=100.  
sqrt of 100 is 10.0.
```

So much for tests. They are not proofs. Rigorous proofs are given in Appendix C.

# 6.2.3 Continuation Passing

The idea of continuation passing is related to the concept of dual space. After walking through the sample code, we will reason the design for it.

# Listing 6.3 Continuation.hs

```txt
1 module Continuation where
2 -- Building a Kleisli triple for a program of CPS
3 -- In this version, T takes two arguments.
```

```haskell
4   
5 newtype T v a = T {unT :: (a -> v) -> v}   
6   
7 -- Definition of eta   
8 ---- eta :: A -> TA   
9 -- plays the role of   
10 ---- return :: (Monad m) => a -> ma   
11 ---- where m = T v.   
12   
13 eta :: a -> T v a   
14 eta a = T (\x -> x a)   
15   
16 -- Definition of sharp   
17 ---- (-)^# :: Hom(A,TB) -> Hom(TA,TB)   
18 -- plays the role of   
19 ---- (=<<) :: (Monad m) => (a -> ma) -> ma -> mb   
20 ---- where m = T v.   
21 -- Types of arguments in the definition below   
22 ---- f :: a -> T v b   
23 ---- m :: T v a   
24 ---- b' :: b -> v   
25   
26 sharp :: (a -> T v b) -> (T v a -> T v b)   
27 sharp f m = T (\b' -> unT m (\a -> unT (f a) b'))   
28   
29   
30   
31 -- Test data   
32   
33   
34 f1 :: Int -> T Int Int   
35 f1 x = T (\c -> c (x+1))   
36   
37 f2 :: Int -> T Int Int   
38 f2 x = T (\c -> c (x^2))   
39   
40 g1 :: String -> T Int String   
41 g1 x = T (\c -> c (x++""!)   
42   
43 g2 :: String -> T Int String   
44 g2 x = T (\c -> c (x++x))   
45   
46 -- Test1 for   
47 ---- f^# o eta_A = f   
48 -- the theoretical goal in code   
49 ---- sharp f . eta == f   
50 -- written extensionally   
51 ---- (sharp f . eta) a == f a   
52 -- fully extensionally   
53 ---- unT ((sharp f . eta) a) (h::a->v) ==   
54 ---- unT (f a) (h::a->v)   
55   
56 test111 = unT ((sharp f1 . eta) 3) (^2) == unT (f1 3) (^2)   
57 test112 = unT ((sharp f2 . eta) 3) (+1) == unT (f2 3) (+1)   
58 test121 = unT ((sharp g1 . eta) "hello") length ==
```

```haskell
59 unT (g1 "hello") length  
60 test122 = unT ((sharp g2 . eta) "hello") length ==  
61 unT (g2 "hello") length  
62 test129 = unT ((sharp g2 . eta) "hello") ((^2) . length) ==  
63 unT (g2 "hello") ((^2) . length)  
64  
65  
66 -- Test2 for  
67 --- eta_A^# = id_(TA)  
68 -- the theoretical goal in code  
69 --- sharp eta == id  
70 -- written extensionally  
71 --- sharp eta (ta::T a) == (ta::T a)  
72 -- fully extensionally  
73 --- unT (sharp eta (ta::T a)) (f::a->v) ==  
74 --- unT (ta::T a) (f::a->v)  
75  
76 test211 = unT (sharp eta (eta 3)) (+1) == unT (eta 3) (+1)  
77 test212 = unT (sharp eta (eta 3)) (^2) == unT (eta 3) (^2)  
78 test221 = unT (sharp eta (f1 3)) (+1) == unT (f1 3) (+1)  
79 test222 = unT (sharp eta (f2 3)) (+1) == unT (f2 3) (+1)  
80 test231 = unT (sharp eta (g1 "hello")) length ==  
81 unT (g1 "hello") length  
82 test232 = unT (sharp eta (g2 "hello")) length ==  
83 unT (g2 "hello") length  
84  
85  
86 -- Test3 for  
87 --- g^# o f^# = (g^# o f)^#  
88 -- the theoretical goal in code  
89 --- sharp g . sharp f == sharp (sharp g . f)  
90 -- written extensionally  
91 --- (sharp g . sharp f) (ta::T a) ==  
92 --- sharp (sharp g . f) (ta::T a)  
93 -- fully extensionally  
94 --- unT ((sharp g . sharp f) (ta::T a)) (h::a->v) ==  
95 --- unT (sharp (sharp g . f) (ta::T a)) (h::a->v)  
96  
97 test311 =  
98 unT ((sharp f2 . sharp f1) (eta 3)) (+1) ==  
99 unT ((sharp (sharp f2 . f1)) (eta 3)) (+1)  
100 test312 =  
101 unT ((sharp f2 . sharp f1) (eta 3)) (^2) ==  
102 unT ((sharp (sharp f2 . f1)) (eta 3)) (^2)  
103 test321 =  
104 unT ((sharp g2 . sharp g1) (eta "hello")) length ==  
105 unT ((sharp (sharp g2 . g1)) (eta "hello")) length  
106 test322 =  
107 unT ((sharp g2 . sharp g1) (g1 "hello")) length ==  
108 unT ((sharp (sharp g2 . g1)) (g1 "hello")) length
```

Line 5 defines a type constructor T that takes two type parameters v and a. Type constructor T itself in not a functor, but a partially applied T v is an instance of the Functor type class. We will discuss this in detail later.

Lines 7-28 give the definitions of  $\eta$  and  $(-)^{\sharp}$ . Lines 30-44 prepare test data and code. Tests for successful construction follow like those of previous examples.

Let us take a closer look at the definition of  $\eta$ .

$$
e t a a = T (\backslash x \rightarrow x a)
$$

T is just a wrapper. For the time being, forget this wrapper. Given a value  $\mathbf{a}$  of type  $A$ , the task of computing  $\backslash \mathbf{x} \rightarrow \mathbf{x}$  is to create a function that takes a function  $\mathbf{x}$  of type  $A \rightarrow V$  as an argument and returns the result of the function application  $\mathbf{x}$  of type  $V$ . The role of  $\mathsf{eta}$  is to embed  $A$  to  $(A \rightarrow V) \rightarrow V$ . The latter is often called the dual space of  $A$ .

In what follows, we use uppercase letters for type variables outside the code so that using the same letters for values does not cause confusions. For example, when we want to use a value  $a$  of type a (type variable), we write  $a \in A$ . Recall that we cannot use uppercase letters for type variables in Haskell code.

Lines 26-28 define the  $(-)^{\sharp}$  function.

$$
\begin{array}{l} \text {s h a r p}:: \left(a - > T v b\right) - > \left(T v a - > T v b\right) \\ \text {s h a r p f m} = \\ T (\backslash b ^ {\prime} \rightarrow u n T m (\backslash a \rightarrow u n T (f a) b ^ {\prime})) \\ \end{array}
$$

The construction looks a little bit clumsy. However, we can deduce the implementation in a straight forward manner. First, analyze the signature of sharp.

- Given  $f::a->T \lor b$ , we have sharp  $f::T \lor a->T \lor b$ .  
- Given successively  $\mathfrak{m} : : \mathrm{T} \vee \mathfrak{a}$ , we have sharp  $\mathfrak{f} \mathfrak{m} : : \mathrm{T} \vee \mathfrak{b}$ .

With all these in mind, let us play with building blocks. At first sight, the only thing we can do with  $\mathsf{f}::\mathsf{a} \rightarrow \mathsf{T} \lor \mathsf{b}$  is to apply it to some value  $a \in A$  and unbox the result.

$$
\mathrm {u n T} (\mathrm {f} \quad \mathrm {a})::: (\mathrm {b} - > \mathrm {v}) - > \mathrm {v}
$$

We can apply it to b' :: b->v to obtain the following.

$$
\text {u n T} (\text {f a}) \text {b} ^ {\prime}:: \text {v}
$$

At this point,  $\mathsf{a}$  is a free variable. We lambda-bind it to obtain the following.

$$
\backslash a \rightarrow u n T (f a) b ^ {\prime}:: a \rightarrow v
$$

Since we have

$$
\mathrm {u n T} \quad \mathrm {m}:: (\mathrm {a} - > \mathrm {v}) - > \mathrm {v}
$$

we can match blocks as follows.

$$
\mathrm {u n T m} (\backslash \mathrm {a} \rightarrow \mathrm {u n T} (\mathrm {f a}) \mathrm {b} ^ {\prime})::: \mathrm {v}
$$

At this point,  $b'$  is a free variable. We lambda-bind it to obtain

$$
\backslash b ^ {\prime} - > \text {u n T m} (\backslash a - > \text {u n T (f a) b ^ {\prime}}):: (b - > v) - > v
$$

Finally, we box it with T to obtain a value of type T v b. Are there any other ways to construct a value of this type?

We summarize the above result in the unboxed(unT) expressions  $(\mathbf{a} - > \mathbf{v}) - > \mathbf{v}$  and  $(\mathrm{b - > v}) - > \mathrm{v}$  as in the following diagram.

![](images/52628c18e29543a86d2bd059ae50e6c0c3cc5fc385c8827ee4297b96502d0189.jpg)

$(-)^{\sharp}$  makes the above triangle commute.

The conditions for  $(-)^{\sharp}$  are tested as follows.

```txt
*Continuation> test111  
True  
...  
omitted  
...  
*Continuation> test322  
True  
*Continuation>
```

# 6.2.4 Computation that May Fail and the Maybe Functor

Computation that may fail is provided by the Maybe functor. Values from a successful computation are boxed in the Just value constructor, while failure yields a polymorphic value Nothing. Composition of computation that may fail is performed under the Kleisli triple mechanism.

Listing 6.4 Maybe.hts  
```txt
1 module Maybe where  
2 -- Building a Kleisli triple for the Maybe functor  
3  
4 type T = Maybe
```

```haskell
5   
6 -- Definition of   
7 ---- eta :: A -> TA   
8 -- plays the role of   
9 ---- return :: (Monad m) => a -> ma   
10 ---- where m = T.   
11   
12 eta :: a -> Ta   
13 eta = Just   
14   
15 -- Definition of   
16 ---- (-)^# :: Hom(A,TB) -> Hom(TA,TB)   
17 -- plays the role of   
18 ---- (=<<) :: (Monad m) => (a -> ma) -> ma -> mb   
19 ---- where m = T.   
20 -- Types of arguments in the definition below   
21 ---- f :: a -> Tb   
22   
23 sharp :: (a -> Tb) -> (Ta -> Tb)   
24 sharp f Nothing = Nothing   
25 sharp f (Just x) = f x   
26   
27   
28   
29 -- Test data   
30   
31   
32 f1 :: Float -> T Float   
33 f1 0 = Nothing   
34 f1 x = Just (1.0/x)   
35   
36 f2 :: Float -> T Float   
37 f2 x = Just (x+1)   
38   
39 testFuncs = [f1,f2]   
40 testFloats = [10.0,100.0,0.1] :: [Float]   
41 testTAs = [Nothing, Just 0.0, Just 1.0]   
42   
43   
44 -- Test1 for   
45 ---- f^# o eta_A = f   
46 -- the theoretical goal in code   
47 ---- sharp f . eta == f   
48 -- written extensionally   
49 ---- (sharp f . eta) a == f a   
50   
51 test1cases  $= [(f,v)\mid f<- \text{testFuncs},v<- \text{testFloats}]$    
52 test1 = map ( $f,v$  -> (sharp f . eta) v == f v) test1cases   
54   
55 -- Test2 for   
56 ---- eta_A^# = id_(TA)   
57 -- the theoretical goal in code   
58 ---- sharp eta == id   
59 -- written extensionally
```

```haskell
60 ---- sharp eta (ta::T a) == (ta::T a)   
61   
62 test2  $=$  map  $\backslash$  ta-> sharp eta ta  $= =$  ta) testTAs   
63   
64 -- Test3 for   
65 ---- g# o f#  $\equiv$  (g# o f)^#   
66 -- the theoretical goal in code   
67 ---- sharp g . sharp f  $= =$  sharp (sharp g . f)   
68 -- written extensionally   
69 ---- (sharp g . sharp f) (ta::T a)  $= =$    
70 ---- sharp (sharp g . f) (ta::T a)   
71   
72 test3cases  $= [(g,f,ta)\mid$    
73 g<- testFuncs, f<- testFuncs,   
74 ta<- testTAs]   
75   
76 test3  $=$  map  $\backslash (\mathrm{g},\mathrm{f},\mathrm{ta})\rightarrow$    
77 (sharp g . sharp f) ta  $= =$    
78 sharp (sharp g . f) ta)   
79 test3cases   
80   
81 test3detail1  $=$    
82 map  $\backslash (\mathrm{g},\mathrm{f},\mathrm{ta})\rightarrow$    
83 (sharp g . sharp f) ta)   
84 test3cases   
85   
86 test3detail2  $=$    
87 map  $\backslash (\mathrm{g},\mathrm{f},\mathrm{ta})\rightarrow$    
88 sharp (sharp g . f) ta)   
89 test3cases
```

Test cases are designed in the same way as in the previous examples. Tests can be done as follows.

```csv
\*Maybe> test1   
[True,True,True,True,True,True]   
omitted   
\*Maybe> test3   
[True,True,True,True,True,True,True,True,True,True]   
\*Maybe>
```

# 6.3 Monads

We introduce the concept of Monads and see it is closely related to the concept of Kleisli triples.

Definition 6.2 Let  $\mathcal{C}$  be a category. A Monad is a triple  $(T, \eta, \mu)$ , where

-  $T: \mathcal{C} \to \mathcal{C}$  is an endofunctor,  
-  $\eta : \mathrm{Id}_{\mathcal{C}} \to T$  and  $\mu : T^2 \to T$  are natural transformations that make the following two diagrams commute for all  $A \in \operatorname{Obj}(\mathcal{C})$ .

![](images/db622407b81745eb56e2a5c0ba8363dd7d196348cbf396539b67160eb03cc8cf.jpg)

![](images/7138102cf30ff5504965f8c14daffc2a8296314a0c30bb1f170929e5bcec2aa8.jpg)

For later use, we rewrite the above diagrams in a list of equations below. (1) and (2) are derived from the left diagram, and (3) is from the right.

(1)  $\mu_{A} \circ T\eta_{A} = 1_{TA}$  
(2)  $\mu_{A} \circ \eta_{TA} = 1_{TA}$  
(3)  $\mu_{A} \circ \mu_{TA} = \mu_{A} \circ T\mu_{A}$

These equations are called the axioms for Monads.

Remark 6.2 The notation here may confuse the reader. We must first distinguish  $T(\eta_A)$  and  $\eta_{TA}$ . Both are morphisms from  $TA$  to  $T(T(A))$ . Let us construct such morphisms from available materials. We have two things at hand: natural transformation  $\eta$  and endofunctor  $T$ .

(1) Treat  $TA$  as an individual and look for a morphism  $\underline{T A} \to T(\underline{T A})$ . We notice that  $\eta_{TA}$ , the  $TA$  component of  $\eta$  is there to be used.

$$
\eta_ {T A}: T A \rightarrow T (T A)
$$

(2) Start with  $\eta_A: A \to TA$ , an  $A$  component of  $\eta$ , take its image by the functor  $T$ . Then, we obtain the following.

$$
T (\eta_ {A}): T A \to T (T A)
$$

So much for the construction of two morphisms that share their domain and codomain. In general, they are different morphisms. Yet, they are coequated by  $\mu_{A}$  as follows.

$$
T A \xrightarrow [ T (\eta_ {A}) ]{\eta_ {T A}} T (T A) \xrightarrow {\mu_ {A}} T A
$$

Further, the left commutative diagram in the above definition requires that the composition yields  $1_{TA}$ .

Remark 6.3 Let us see  $T(\mu_A)$  and  $\mu_{TA}$ . Both are morphisms from  $T(T(TA))$  to  $T(TA)$ . Let us construct such morphisms from available materials. We have two things at hand: natural transformation  $\mu$  and endofunctor  $T$ .

(1) Treat  $TA$  as an individual and look for a morphism  $T(T(\underline{T} A)) \to T(\underline{T} A)$ . We have the  $TA$  component of the natural transformation  $\mu$ , namely  $\mu_{TA}$ .

$$
\mu_ {T A}: T (T (T A)) \to T (T A)
$$

(2) Start with  $\mu_A: T(TA) \to TA$  and take its image by the functor  $T$ . We obtain the following

$$
T (\mu_ {A}): T (T (T A)) \rightarrow T (T A)
$$

So much for the construction of two morphisms that share their domain and codomain. In general, they are different. Yet, they are coequated by  $\mu_A$  as follows.

$$
T (T (T A)) \xrightarrow [ T (\mu_ {A}) ]{\mu_ {T A}} T (T A) \xrightarrow {\mu_ {A}} T A
$$

This is the second commutative diagram in Definition 6.2.

Remark 6.4 Required conditions in Definition 6.2 are described with componentwise commutative diagrams. We can restate the conditions with natural transformations as a whole using horizontal composition.

![](images/7db34620ea02efffe8165b436f6591792181ae57eef060faef4933b19fbfea9b.jpg)

![](images/64fef61126f6469b707f27fea2ab98597f6a7fa1e2334b44baeebd7dce2c7818.jpg)

Given a Kleisli triple, we can construct a Monad.

Theorem 6.1 Let  $\mathcal{C}$  and  $T: \mathcal{C} \to \mathcal{C}$  be a category and endofunctor. Given a Kleisli triple  $(T, \eta, (-)^{\sharp})$ , we set

$$
\mu_ {A} = \left(1 _ {T A}\right) ^ {\sharp}: T (T A) \rightarrow T A. \tag {6.1}
$$

Then,  $\mu : T \circ T \to T$  is a natural transformation, and a triple  $(T, \eta, \mu)$  is a Monad.

Remark 6.5 We are naturally led to the definition of  $\mu$  by Eq. (6.1) if we notice that replacing  $A$  with  $TA$ ,  $TB$  with  $TA$ , and  $f$  with  $1_{TA}$  in the left diagram below gives a specialized diagram at right.

![](images/cea9a1668754ee7654f4246971e4f848cf3be4b56007a2b18cce3950f9f86673.jpg)

Remember that  $T$  and  $\sharp$  are related by a commutative diagram appearing in the proof of Proposition 6.1:

![](images/325a225699c520788f45b663fdeb5685cce5d01875f868773f1fa581734adbfc.jpg)

Proof We first show that the family of morphisms  $\{\mu_A = 1_{TA}^\sharp \mid A\in \mathrm{Obj}(\mathcal{C})\}$  is a natural transformation. It is sufficient to show that the trapezoid at the right in the following diagram commutes.

![](images/b8ab1cd29f676a1bfba3531940f1ee10670265a0318c20eee9ef52ca7d01084e.jpg)

Iterate rewriting as follows. We consider a path that starts with  $T^2 A$ , goes down, and goes down-right:

$$
\begin{array}{l} 1 _ {T B} ^ {\sharp} \circ (T (T f)) \\ = 1 _ {T B} ^ {\sharp} \circ (\eta_ {T B} \circ (\eta_ {B} \circ f) ^ {\sharp}) ^ {\sharp} \quad \text {t w i c e r e p l a c i n g T w i t h \sharp} \\ = \left(1 _ {T B} ^ {\sharp} \circ \eta_ {T B} \circ (\eta_ {B} \circ f) ^ {\sharp}\right) ^ {\sharp} \quad \text {C o n d i t i o n (3) f o r} \sharp \\ = \left(1 _ {T B} \circ (\eta_ {B} \circ f) ^ {\sharp}\right) ^ {\sharp} \quad \text {C o n d i t i o n (1) f o r} \sharp \\ = (\eta_ {B} \circ f) ^ {\sharp \sharp} \quad \text {o m i t t i n g t h e i d e n t i t y} \\ \end{array}
$$

Next, we consider a path that starts with  $T^2 A$ , goes up-right, and goes down:

$$
\begin{array}{l} T f \circ 1 _ {T A} ^ {\sharp} \\ = (\eta_ {B} \circ f) ^ {\sharp} \circ 1 _ {T A} ^ {\sharp} \quad \text {r e p l a c i n g T w i t h \sharp} \\ = \left(\left(\eta_ {B} \circ f\right) ^ {\sharp} \circ 1 _ {T A}\right) ^ {\sharp} \quad \text {C o n d i t i o n (3) f o r \sharp} \\ = (\eta_ {B} \circ f) ^ {\sharp \sharp} \quad \text {o m i t t i n g t h e i d e n t i t y} \\ \end{array}
$$

This establishes the naturality of  $\mu$  defined via  $\mu_A = 1_{TA}^\sharp$ .

What remains to show is that  $\mu_A = 1_{TA}^\sharp$  satisfies the three equations in Definition 6.2.

(1) We show that  $1_{TA}^{\sharp} \circ T\eta_A = 1_{TA}$ , namely the commutativity of the left triangle of the diagram below.

![](images/d5fe9caf46d76eb0e21a22688ad4a6912807f2f5e634eb2a3aa5e8a74fac6476.jpg)

Iterate rewriting as follows.

$$
\begin{array}{l} 1 _ {T A} ^ {\sharp} \circ T \eta_ {A} \\ = 1 _ {T _ {A}} ^ {\sharp} \circ (\eta_ {T A} \circ \eta_ {A}) ^ {\sharp} \quad \text {r e p l a c e} T \text {w i t h} \sharp (*) \\ = (1 _ {T A} ^ {\sharp} \circ \eta_ {T A} \circ \eta_ {A}) ^ {\sharp} \quad \text {C o n d i t i o n (3) f o r \sharp} \\ = \left(1 _ {T A} \circ \eta_ {A}\right) ^ {\sharp} \quad \text {C o n d i t i o n (2) f o r \sharp (* *)} \\ = \eta_ {A} ^ {\sharp} \quad \text {o m i t t i n g t h e i d e n t i t y} \\ = 1 _ {T A} \quad \text {C o n d i t i o n (2) f o r \sharp} \\ \end{array}
$$

Take a careful look at the diagram

![](images/d5394a59634bcf8f159b64543ea384da44e34b8c506c5f42ecf0b3d2de3246f6.jpg)

to see  $T\eta_{A} = (\eta_{TA}\circ \eta_{A})^{\sharp}$  in the step  $(^{*})$

Take a careful look again at the diagram

![](images/b72d7d3c87340a7acb146446987345385a0e882643d04916f20978038c3b7894.jpg)

to see  $1_{TA}^{\sharp}\circ \eta_{TA} = 1_{TA}$  in the step  $(^{**})$

(2) We prove that  $1_{TA}^{\sharp} \circ \eta_{TA} = 1_{TA}$  by showing the triangle at right in the following diagram commutes.

![](images/ce698d4ef57f641f566e9ec15dee16bcdc23683ca872cbeb2f9743f1460366d5.jpg)

This is a direct consequence of the definition of  $1_{TA}^{\sharp}$  and  $\mu$ . Since the following diagram

![](images/67172e088b56705a919b6507bb2a6e5d9a5302721172ead0e33416c5f58dcb36.jpg)

must commute.

(3) Finally, we prove the commutativity of the following diagram.

![](images/688d83a83ee8d2a9e07e74500ebc2ac2ce00d7717c646200588781d9b8c68889.jpg)

Using the definition of  $\mu$ , namely  $\mu_A = 1_{TA}^\sharp$ , we will calculate the two paths from the upper-left corner to the lower-right.

![](images/e31d65862380905622d6d175cb23513420a555a04c6a3a1816c121b5036aad39.jpg)

First, we compute the path down-right.

$$
\begin{array}{l} 1 _ {T A} ^ {\sharp} \circ 1 _ {T ^ {2} A} ^ {\sharp} \\ = (1 _ {T A} ^ {\sharp} \circ 1 _ {T ^ {2} A}) ^ {\sharp} \quad \text {f o r m u l a} (g ^ {\sharp} \circ f) ^ {\sharp} = g ^ {\sharp} \circ f ^ {\sharp} \\ = 1 _ {T A} ^ {\sharp \sharp} \quad \text {o m i t t i n g} 1 _ {T ^ {2} A} \\ \end{array}
$$

Next, we compute the path right-down.

$$
\begin{array}{l} 1 _ {T A} ^ {\sharp} \circ T (1 _ {T A} ^ {\sharp}) \\ = 1 _ {T A} ^ {\sharp} \circ (\eta_ {T A} \circ 1 _ {T A} ^ {\sharp}) ^ {\sharp} \quad T \text {i s r e p l a c e d b y \sharp} \\ = \left(1 _ {T A} ^ {\sharp} \circ \eta_ {T A} \circ 1 _ {T A} ^ {\sharp}\right) ^ {\sharp} \quad \text {f o r m u l a} (g ^ {\sharp} \circ f) ^ {\sharp} = g ^ {\sharp} \circ f ^ {\sharp} \\ = \left(1 _ {T A} \circ 1 _ {T A} ^ {\sharp}\right) ^ {\sharp} \quad \text {f o r m u l a} f ^ {\sharp} \circ \eta_ {-} = f \\ = 1 _ {T A} ^ {\text {印}} \quad \text {o m i t t i n g} 1 _ {T A} \\ \end{array}
$$

Rewriting the first line to the second is inspired by the following commutative diagram, where morphism  $T(1_{TA}^{\sharp})$  appears at the top edge.

$$
\begin{array}{c} T ^ {3} A \xrightarrow {(\eta_ {T A} \circ 1 _ {T A} ^ {\sharp}) ^ {\sharp}} T ^ {2} A \\ \eta_ {T ^ {2} A} \Bigg | \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}
$$

Other rewriting steps are clearly justified by each accompanying comment.

We completed the proof by showing the last commutativity.

![](images/c15fdefd9927e349524e16e259e6f1a9270be0500b591faa772e08b36502a65c.jpg)

Theorem 6.2 Given a Monad  $(T, \eta, \mu)$  on a category  $\mathcal{C}$ , we put

$$
\begin{array}{l} (-) ^ {\sharp}: \mathcal {C} (A, T B) \longrightarrow \mathcal {C} (T A, T B) \\ f \longmapsto \mu_ {B} \circ T f \\ \end{array}
$$

Then, the data  $(T,\eta ,(-)^{\sharp})$  is a Kleisli triple on the category  $\mathcal{C}$

Remark 6.6 We defined the functor  $T$  from the  $(-)^{\sharp}$  operation. We are doing the reverse. Compare the two diagrams below.

![](images/198e69e2bb8b35a7983ec339a6556dc91172d9f7640b935a4e3ee0c07bb237e7.jpg)

![](images/9093b611f4f52a47dfe7fc135f74a950bb39af699bb708d533d324d7ebbe2964.jpg)

Proof The operation  $(-)^{\sharp}$  defined by  $f^{\sharp} \stackrel{\mathrm{def}}{=} \mu_B \circ Tf$  gives the following equations:

$$
f ^ {\sharp} \circ \eta_ {A} = f, \quad \eta_ {A} ^ {\sharp} = 1 _ {T A}, \quad g ^ {\sharp} \circ f ^ {\sharp} = (g ^ {\sharp} \circ f) ^ {\sharp},
$$

which we will show in order.

1. We prove  $f^{\sharp} \circ \eta_{A} = f$ .

From the definition of  $(-)^{\sharp}$ , we have to show

$$
\mu_ {B} \circ T f \circ \eta_ {A} = f.
$$

We look for any information available to approach this goal. There is the fact that  $\eta : \operatorname{Id} \to T$  is a natural transformation. We put it in a commutative diagram as follows.

![](images/02b79acf563d0ec39b71e82db994e9c378b4ae97929bd073863ca8115ad04866.jpg)

The trapezoid at right commutes. Namely, we have

$$
T f \circ \eta_ {A} = \eta_ {T B} \circ f.
$$

By composing  $\mu_B$  from left, we have

$$
\mu_ {B} \circ T f \circ \eta_ {A} = \mu_ {B} \circ \eta_ {T B} \circ f. \tag {6.2}
$$

An axiom of Monads tells that triangles in the diagram

![](images/b778f6e3ad714b140e9e3fcb6c4ac73f965257783efb4187611ad5c7ad3eb595.jpg)

commute. Especially, the commutative triangle at right gives us  $\mu_B\circ \eta_{TB} = 1_{TB}$  which means that the RHS of Equation (6.2) equals to  $f$

2. We prove  $\eta_A^\sharp = 1_{TA}$

Recall the definition of  $(-)^{\sharp}$ . We only have to show

$$
\mu_ {A} \circ T \eta_ {A} = 1 _ {T A}.
$$

We have nothing to do since this comes from the commutative triangle at left in the axiom above.

3. We prove  $g^{\sharp} \circ f^{\sharp} = (g^{\sharp} \circ f)^{\sharp}$ .

Recall again the definition of  $(-)^{\sharp}$ . We have to show

$$
(\mu_ {C} \circ T g) \circ (\mu_ {B} \circ T f) = \mu_ {C} \circ T (\mu_ {C} \circ T g \circ f).
$$

Since  $T$  is a functor, we can rewrite the subexpression of the RHS as follows.

$$
T \left(\mu_ {C} \circ T g \circ f\right) = T \mu_ {C} \circ T ^ {2} g \circ T f
$$

The whole RHS becomes

$$
\mu_ {C} \circ T (\mu_ {C} \circ T g \circ f) = \mu_ {C} \circ T \mu_ {C} \circ T ^ {2} g \circ T f.
$$

We rewrite the RHS further in two steps. Recall that  $\mu_C$  coequalizes  $T\mu_{C}$  and  $\mu_{TC}$  by the axiom

$$
\begin{array}{c} T ^ {3} C \xrightarrow {T \mu_ {C}} T ^ {2} C \\ \mu_ {T C} \Bigg |   \bigcirc \\ T ^ {2} C \xrightarrow [ \mu_ {C} ]{} T C \end{array} .
$$

From this, we can rewrite as follows.

$$
\underline {{\mu_ {C} \circ T}} \underline {{\mu_ {C} \circ T ^ {2}}} g \circ T f = \underline {{\mu_ {C} \circ \mu_ {T C}}} \circ T ^ {2} g \circ T f
$$

Next, we use the fact that  $\mu : T^2 \to T$  is a natural transformation. We have

$$
\mu_ {C} \circ \underline {{\mu_ {T C}}} \circ T ^ {2} g \circ T f = \mu_ {C} \circ \underline {{T g}} \circ \mu_ {B} \circ T f,
$$

which completes the proof.

The bird's eye view of the whole rewriting process is given below.

![](images/5c67cb81cbcc8bc7e6db9b2febe75f9bdaff5e567d093239482665d34fead4c8.jpg)

Theorems 6.1 and 6.2 established that Monads and Kleisli triples translate themselves into others. The remaining question is whether they have the same data when they go and come back. Fix the endofunctor  $T$  and  $\eta$  that are shared between the Monads and the corresponding Kleisli triple. Let  $\varphi$  be the correspondence in Theorem 6.1 that sends  $\sharp$  to  $\mu$ . Namely, we set

$$
\varphi (\sharp) = \mu .
$$

Likewise, let  $\psi$  be the correspondence in Theorem 6.2 that sends  $\mu$  to  $\sharp$ . Namely, we set

$$
\psi (\mu) = \sharp .
$$

Set  $\psi(\varphi(\sharp)) = \sharp'$ . We do not know if  $\sharp' = \sharp$ . Set  $\varphi(\psi(\mu)) = \mu'$ . We do not know if  $\mu' = \mu$ .

Theorem 6.3 Assume that a Kleisli triple  $(T, \eta, (-)^\sharp)$  and a Monad  $(T, \eta, \mu)$  share the functor  $T$  and  $\eta$ . Then, we have  $\psi(\varphi(\sharp)) = \sharp$  and  $\varphi(\psi(\mu)) = \mu$ .

Proof We start with  $\sharp$ . Let  $\varphi(\sharp) = \mu$  and  $\psi(\mu) = \sharp'$ . We have  $\mu_A = 1_{TA}^\sharp$  from the construction in Theorem 6.1. For any  $f: A \to TB$  we have

$$
\begin{array}{l} f ^ {\sharp^ {\prime}} \\ = \mu_ {B} \circ T f \quad \text {d e f i n i t i o n} \sharp^ {\prime} \text {b y} \mu \\ = 1 _ {T B} ^ {\sharp} \circ T f \quad \text {d e f i n i t i o n} \mu \text {b y} \sharp \\ = 1 _ {T B} ^ {\sharp} \circ \eta_ {T B} \circ f ^ {\sharp} \quad \text {r e p l a c i n g} T \text {w i t h} \sharp \\ = 1 _ {T B} \circ f ^ {\sharp} \quad \text {a x i o m} \sharp \\ = f ^ {\sharp} \\ \end{array}
$$

Next, we start with  $\mu$ . Let  $\psi(\mu) = \sharp$  and  $\varphi(\sharp) = \mu'$ . We have  $f^{\sharp} = \mu_B \circ Tf$  for any  $f: A \to TB$ , recalling the construction in Theorem 6.2. Set  $f = 1_{TB}$  and follow the rewriting below.

$$
\begin{array}{l} \mu_ {B} ^ {\prime} \\ = 1 _ {T B} ^ {\sharp} \quad \text {d e f i n i t i o n} \mu^ {\prime} \text {b y} \sharp \\ = \mu_ {B} \circ T 1 _ {T B} \quad \text {r e p l a c i n g} \sharp \text {w i t h} T \\ = \mu_ {B} \circ 1 _ {T ^ {2} B} \quad \text {f u n c t o r i a l i t y} T \\ = \mu_ {B} \\ \end{array}
$$

We completed the proof that  $\varphi$  and  $\psi$  are mutual inverses.

# 6.4 Monad Instances in Haskell

Examples presented in Sect. 6.2 are revisited as instances of type classes Applicative and Monad in the Haskell standard library.

# 6.4.1 Computation with Output(revisited)

We extract the necessary part of the sample code presented earlier, aiming to recall the definitions of

eta : a -> T a and sharp :: (a -> T b) -> (T a -> T b).

Listing 6.5 CalcWithOutput.hs(excerpt)  
```haskell
5newtype T a = T {unT :: String -> (a,String)}   
6   
7 -- Definition of   
8----(-)^#::Hom(A,TB)  $\rightharpoondown$  Hom(TA,TB)   
9 -- plays the role of   
10---- return : (Monad m)  $\Rightarrow$  a-> ma   
11---- where m = T.   
12   
13 eta :: a-> Ta   
14 eta x  $=$  T (\s-> (x,s))   
15   
16 -- Definition of   
17----(-)^#::Hom(A,TB) -> Hom(TA,TB)   
18 -- plays the role of   
19----  $= <   <   )$  ..(Monad m)  $\Rightarrow$  (a-> ma) -> ma->mb   
20---- where m = T.   
21   
22 sharp :: (a-> Tb) -> (Ta-> T b)   
23 sharp f h =   
24 T (\st-> let   
25 (y,st2)  $=$  unT h st   
26 (z,st3)  $=$  unT (f y) st2   
27 in   
28 (z,st3))
```

f1 and f2 are test cases.

Listing 6.6 CalcWithOutput.hs(excerpt)  
```haskell
34 f1 :: Integer -> T Integer  
35 f1 x = T (\s -> (x^2,  
36 s ++ show x ++ "^2=" ++ show (x^2) ++  
37 ".\n"))  
38  
39 f2 :: Integer -> T Float  
40 f2 x = T (\s -> (sqrt(fromInteger x),  
41 s ++  
42 "sqrt of " ++ show x ++  
43 " is " ++ show (sqrt(fromInteger x)) ++  
44 ".\n"))
```

We import this module and make the type constructor T an instance of type classes Functor, Applicative, and Monad.

Listing 6.7 CalcWithOutput2.xls  
```txt
1 module CalcWithOutput2 where  
2 import Control.Monad  
3 import CalcWithOutput  
4  
5 -- After building a Kleisli triple  
6 -- for a program with simple output,  
7 -- we declare instances of
```

```haskell
8 -- Functor, Applicative, and Monad  
9  
10  
11 -- Functor  
12  
13  
14 instance Functor T where  
15 -- fmap :: (a -> b) -> (T a -> T b)  
16 fmap f ta =  
17 T (\s -> let (a,s2) = (unT ta) s  
18 in (f a, s2)  
19  
20  
21 {- suggested tests  
22 -- f1 and f2 are imported from CalcWithOutput  
23  
24 unT (fmap (+1) (f1 10)) "hello\n"  
25  
26  
27  
28 -- Applicative  
29  
30  
31 instance Applicative T where  
pure x = T (\s -> (x,s))  
32 tf <\*> ta =  
33 T (\s -> let (h, s2) = unT tf s  
34 (a, s3) = unT ta s2  
35 in (h a, s3))  
36 -- pure :: a -> T a  
37 -- (<\*>) :: (T (a -> b)) -> Ta -> Tb  
38  
39  
40  
41  
42 -- Test data  
43  
44  
45 appTest1 :: T (Integer -> Integer)  
46 appTest1 =  
47 T (\s -> ((\x -> x * 3),  
48 s ++ "multiplied by 3 <= ")  
49)  
50  
51 {-- suggested tests  
52 :t appTest1 <\*> f1 10  
53 :t unT $ appTest1 <\*> f1 10  
54 unT (appTest1 <\*> f1 10) ""  
55 -}  
56  
57  
58 -- Monad  
59  
60  
61 instance Monad T where  
62 return = pure
```

```haskell
63 h  $>> = \text{f} =$  sharp f h  
64 -- return :: a -> T a  
65 -- ( $>> =$ ): T a -> (a -> T b) -> (T b)  
66  
67 {- suggested tests  
68 (unT $ return 10) ""  
69  
70 let (xTest1, stTest1) = (unT $ sharp f2 $ sharp f1 $ return  
71 10) ""  
72 putStr stTest1  
73  
74 let (xTest2, stTest2) = unT (return 10  $>> =$  f1  $>> =$  f2) ""  
75 putStr stTest2  
76  
77 let (xTest3, stTest3) = unT (do x <- return 10; y <- f1 x; f2  
y) ""  
78 putStr stTest3  
79 -}
```

Lines 14-19 declare T as an instance of the type class Functor implementing the fmap function. A suggested test described in line 24 is carried out as follows.

```txt
\*CalcWithOutput2> unT (fmap (+1) (f1 10)) "hello\n" (101,"hello\n10^2=100.\n")
```

The proofs for two equations that fmap must satisfy are given in Appendix C.

Lines 27-55 give an instance of the type class Applicative. The real meaning of this implementation will be made clear with the Monad instance.

A test described in line 54 yields the following.

```txt
\*CalcWithOutput2> unT (appTest1  $\text{一} * >$  f1 10) "" (300,"multiplied by  $3 <   = 10^{\wedge}2 = 100.\backslash n^{\prime \prime})$    
\*CalcWithOutput2>
```

Refer to Appendix C for proofs concerning various equations required to be an instance of Applicative.

Lines 61-63 implement the Monad instance. Suggested tests can be carried out as follows.

```txt
\*CalcWithOutput2> (unT $ return 10) ""  
(10,[])  
\*CalcWithOutput2> (xTest2,stTest2)=unT (return 10>>=f1>>=f2) ""  
\*CalcWithOutput2> putchar stTest2  
10^2=100.  
sqrt of 100 is 10.0.  
\*CalcWithOutput2> (xTest2,stTest2)=unT (return 10>>=f1>>=f2) ""  
\*CalcWithOutput2> putchar stTest2  
10^2=100.  
sqrt of 100 is 10.0.  
\*CalcWithOutput2> let (xTest3, stTest3) =  
    unT (do x <- return 10; y <- f1 x; f2 y) ""  
\*CalcWithOutput2> putchar stTest3  
10^2=100.  
sqrt of 100 is 10.0.  
\*CalcWithOutput2>
```

Refer to Appendix C for proofs concerning various equations required to be an instance of Monad.

# 6.4.2 Computation with Continuation(revisited)

We extract the necessary part of the sample code presented earlier, aiming to recall the definitions of

eta :: a -> T a and sharp :: (a -> T b) -> (T a -> T b).

Listing 6.8 Continuation.hs(excerpt)  
```txt
5newtype Tva  $=$  T{unT::  $(a\rightarrow v)\rightarrow v$    
6   
7 -- Definition of eta   
8 ---- eta :: A-> TA   
9 -- plays the role of   
10 ---- return : (Monad m)  $\Rightarrow$  a-> ma   
11 ---- where m  $=$  Tv.   
12   
13 eta :: a-> Tva   
14 eta a  $=$  T  $\backslash x\rightarrow x$  a)   
15   
16 -- Definition of sharp   
17 ---- (-)^#::Hom(A,TB) -> Hom(TA,TB)   
18 -- plays the role of   
19 ----  $(= <   <   )$  ::(Monad m)  $\Rightarrow$  (a->ma) -> ma->mb   
20 ---- where m  $=$  Tv.   
21 -- Types of arguments in the definition below   
22 ---- f::a->Tvb   
23 ---- m::Tva   
24 ---- b'::b->v   
25   
26 sharp::(a->Tvb) -> (Tva->Tvb)   
27 sharpf m=   
28 T  $\backslash \mathsf{b}^{\prime}\rightarrow$  unTm  $\backslash a\rightarrow$  unT(fa)b))
```

Test data have been given as follows.

Listing 6.9 Continuation.hs(excerpt)  
```haskell
34 f1 :: Int -> T Int Int  
35 f1 x = T (\c -> c (x+1))  
36  
37 f2 :: Int -> T Int Int  
38 f2 x = T (\c -> c (x^2))  
39  
40 g1 :: String -> T Int String  
41 g1 x = T (\c -> c (x++!"!"))  
42  
43 g2 :: String -> T Int String  
44 g2 x = T (\c -> c (x++x))
```

We import this module and instantiate Functor, Applicative, and Monad type classes for the continuation functor.

Listing 6.10 Continuation2.ms  
```haskell
1 module Continuation2 where  
2 import Control.Monad  
3 import Continuation  
4  
5 -- After building a Kleisli triple  
6 -- for a continuation,  
7 -- we declare instances of  
8 -- Functor, Applicative, and Monad  
9  
10  
11 -- Functor  
12  
13  
14 --- instance declarations  
15  
16 -- T v a is a bifunctor.  
17 -- However, we declare a Fuctor instance only for (T v).  
18  
19 instance Functor (T v) where  
20 fmap f h =  
21 T (\b' -> unT h (b'.f))  
22  
23 -- where  
24 -- fmap :: (a -> b) -> (T v a -> T v b)  
25 -- f :: a -> b  
26 -- unT h :: (a -> v) -> v  
27 -- b' :: b -> v  
28 -- result:: v  
29  
30  
31 -- Note that T itself is not an Applicative, but (T v) is.  
32  
instance (Applicative (T v)) where  
34 pure = eta  
35 -- pure :: a -> T v a
```

```haskell
tf <\*> ta =
T (\b' -> unT tf $ \f -> unT ta (b'. f))
-- where
-- (<\*>) :: (T v (a -> b)) -> T v a -> T v b
-- unT tf :: ((a->b)->v) -> v
-- unT ta :: (a ->v) -> v
-- b' :: b ->v
-- f :: a ->b
-- b'.f :: a ->v
--- for tests
{- defined in Continuation.hs
f2 :: Int -> T Int Int
f2 x = T (\c -> c (x^2))
g2 :: String -> T Int String
g2 x = T (\c -> c (x++x))
-}
test9 =
do x <- return "hello"
y <- g2 x
g2 y
-- unT test9 length
{-}
unT (f2 3) (+1) -> 10
unT (return 3 >= f2) (+1)
unT (sharp f2 (eta 3)) (+1)
unT (sharp f2 $ sharp f2 $ eta 3) id -----> 81
unT (return 3 >= f2 >= f2) id
unT (g2 "hello") length -----> 10
unT (sharp g2 (eta "hello") ) length
unT (return "hello" >= g2) length
(unT $ sharp g2 $ sharp g2 $ eta "hello") length -----> 20
unT (return "hello" >= g2 >= g2) length
-}
Pythagoras
```

```haskell
91 sq' :: (Num a) => a -> T va  
92 sq' x = return (x*x)  
93 -- sq' x = T (\f -> f (x*x))  
94 -- unT (sq' 3) id  
95  
96 add' :: (Num a) => a -> a -> T va  
97 add' x y = return (x+y)  
98 -- add' x y = T (\f -> f (x+y))  
99 -- unT (add' 11 19) id  
100  
101 sqrt' :: (Floating a) => a -> T va  
102 sqrt' x = return (sqrt x)  
103 -- sqrt' x = T (\f -> f (sqrt x))  
104 -- unT (sqrt' 10) (\x -> (x* x))  
105  
106 pyth x y = do  
107 x2 <- sq' x  
108 y2 <- sq' y  
109 z <- add' x2 y2  
110 sqrt' z  
111  
112 -- unT (pyth 3 4) id  
113  
114 pyth2 x y =  
115 sq' x >= \x2 -> sq' y >= \y2 -> add' x2 y2 >= sqrt'  
116  
117 -- unT (pyth2 3 4) id  
118  
119  
120 -- factorial  
121  
122 factorial' :: Integer -> T v Integer  
123 factorial' 0 = return 1  
124 factorial' n = do  
125 fmn1 <- factorial' (n-1)  
126 return (n*fmn1)  
127  
128 -- unT (factorial' 5) id  
129  
130 factorial2' :: Integer -> T v Integer  
131 factorial2' 0 = return 1  
132 factorial2' n = factorial2' (n-1) >= \fmn1 -> return (n*fmn1)  
133  
134 -- unT (factorial2' 5) id  
135  
136  
137 -- factorial'  
138 -- tail recursive  
139  
140 factorial' :: Integer -> T v Integer  
141 factorial' n = faux' n 1  
142  
143 faux' :: Integer -> Integer -> T v Integer  
144 faux' 0 k = return k  
145 faux' n k = faux' (n-1) (k*n)
```

```txt
146   
147 -- unT (factorial'5) id
```

Lines 19-21 implement an instance of Functor. Lines 33-37 implement an instance of Applicative. Lines 48-50 implement an instance of Monad.

So defined Monad instance makes all the following

```txt
unT (f2 3) (+1)  
unT (return 3 >= f2) (+1)  
unT (sharp f2 (eta 3)) (+1)
```

evaluate to 10.

All the following

```perl
unT (sharp f2 $ sharp f2 $ eta 3) id
unT (return 3 >= f2 >= f2) id
```

evaluate to 81.

All the following

```txt
unT (g2 "hello") length  
unT (sharp g2 (eta "hello")) length  
unT (return "hello" >= g2) length
```

evaluate to 10.

All the following

```txt
(unT $ sharp g2 $ sharp g2 $ eta "hello") length
unT (return "hello" >= g2 >= g2) length
```

evaluate to 20.

Lines from 87 to the end include familiar materials that demonstrate the power of Monads.

The python function calculates the sum of squares and passes the result to a given continuation. The python2 function is an equivalent version of python, replacing the do-notation with the sequence of bind  $(\gg =)$  operations.

A suggested test is carried out as follows.

```txt
\*Continuation2> unT (pyth 3 4) id   
5.0   
\*Continuation2>
```

# 6.5 Functor, Applicative, and Monad

In the previous section, we mentioned applicative functors without clearly defining them. Let us see briefly here.

Given an endofunctor  $T: \mathrm{Hask} \to \mathrm{Hask}$ , objects  $\mathsf{a}$  and  $\mathsf{b}$  of Hask, then we know that  $\mathsf{a} \dashrightarrow \mathsf{b}$  is also an object of Hask. These objects are mapped to  $\mathrm{T} \mathsf{a}, \mathrm{T} \mathsf{b}, \mathrm{T}(\mathsf{a} \dashrightarrow \mathsf{b})$ , respectively.

One may naturally be led to the question if there are any relations between  $\mathrm{T}$  ( $\mathsf{a} \rightarrow \mathsf{b}$ ) and  $\mathrm{T}$  ( $\mathsf{a} \rightarrow \mathsf{T}$  b). In some cases, we can define an operator

```javascript
$<  * >$  ：T（a->b）  $\rightarrow$  （Ta->Tb）.
```

If a functor  $T$  satisfies some conditions related to this question, we say that  $T$  is an Applicative functor. Monad functors are known to be applicative.

In this section, we will discuss the relations among the concepts of functor, applicative, and Monad.

The functor class defines the following interface.

```txt
class Functor f where  
fmap :: (a -> b) -> f a -> fb
```

A function of a signature is further required to satisfy constraints, namely the functor rules below.

```txt
fmap id = id  
fmap (g . f) = fmap g . fmap f
```

The Applicative class defines the following interface.

```txt
class Functor f => Applicative f where
    pure :: a -> f a
        (<*) :: f (a -> b) -> f a -> f b
```

The functions of these signatures are required to satisfy the constraints, namely the Applicative rules below.

```txt
pure id < $\succ$  v = v
pure (.)< $\succ$  u < $\succ$  v < $\succ$  w = u < $\succ$  (v < $\succ$  w)
f < $\succ$  pure x = pure (f x)
u < $\succ$  pure y = pure (\$ y) < $\succ$  u
```

The Monad class defines the following interface.

```txt
class Monad f where  $(\gg =)$  :: m a -> (a -> m b) -> m b return :: a -> m a
```

The functions of these signatures are required to satisfy the constraints, namely the Monad rules below.

```txt
return a  $>> = \mathrm{f} = \mathrm{f}$  a  
m  $>> =$  return  $= \mathrm{m}$ $\backslash (\mathrm{m} >> = \mathrm{f}) >> = \mathrm{g} = \mathrm{m} >> = (\backslash \mathrm{x} -> \mathrm{f} \mathrm{x} >> = \mathrm{g})$
```

We try to demonstrate the derivation (1), (2), and (3) from rules to rules.

![](images/70bd8c760588bd0c0b0d62607a6232776237d19aeab7466751b9e9684d563e2f.jpg)

In the derivation (1), we implement fmap by return.

```txt
fmap f m  $=$  m  $>> = \backslash a - >$  return (f a)
```

In the derivation (2) we implement pure and  $\langle * \rangle$  by the bind operator  $\gg =$  and return.

```txt
pure  $=$  return mf  $\text{<  } * >$  mx  $=$  mf  $\gg = \backslash f ->$  mx  $\gg = \backslash x ->$  return (f x)
```

In the derivation (3), we implement fmap by pure and  $<\ast>$ .

```txt
fmap f x = pure f <> x
```

Proposition 6.3 In the rewriting of (1), fmap defined by  $>>$  and return satisfies the functor rules.

Proof We use Monad rules.  
```haskell
fmap id m
    -- rewrite with (\(>>>) and (return)
= m >>>= \)a -> return (id a)
    -- eliminate id
= m >>>= \)a -> return a
    -- eta transformation
= m >>>= return
    -- the 2nd Monad rule
= m
fmap g . fmap f $ m
= fmap g (fmap f m)
    -- rewrite (fmap f) by (\(>>>) and (return)
= fmap g (m >>>= return . f)
    -- rewrite (fmap g) by (\(>>>) and (return)
= (m >>>= (return . f)) >>>= (return . g)
    -- use the 3rd Monad rule
= m >>>= (\)x -> (return . f) x >>>= (return . g))
    -- rewrite function composition
= m >>>= (\(x -> return (f x) >>>= (return . g))
    -- use the 1st Monad rule
= m >>>= (\)x -> (return . g) (f x))
    -- rewrite function composition
= m >>>= (\(x -> (return . g . f) x)
    -- use Eta transformation
= m >>>= return . g . f
    -- (. ) is associative. Insert a redundant parentheses.
= m >>>= return . (g . f)
    -- definition of fmap by Monad
= fmap (g . f) m
```

Proposition 6.4 In the rewriting of (2), pure and  $< * >$  defined by  $>> =$  satisfy all the Applicative rules.

Proof We first show pure id  $<  * > =$  id.  
```txt
pure id  $\langle *\rangle$  v
```

```lua
-- rewrite pure and  $<\ast>$   
= return id  $>>=$  \f -> (v  $>>=$  \x -> return (f x))  
-- return is a left unit  
= v  $>>=$  \x -> return (id x)  
-- omit id  
= v  $>>=$  \x -> return x  
-- Eta transformation  
= v  $>>=$  return  
-- return is a right unit  
= v
```

Next, we show the following.

```javascript
pure (.）  $\text{<} * >$  u  $<  >$  v  $<  >$  w = u  $<  >$  (v  $<  >$  w)
```

We rewrite the LHS.

```haskell
pure (.）  $<  >$  u -- replace (pure) with (return)  $=$  return(.）  $<  >$  u -- replace  $<  >$  with  $(\gg =)$ $=$  return(.）  $\gg =$  \\f->(u  $\gg =$  \\x->return(fx)) -- return is a left unit  $=$  u  $\gg =$  \\x->return(.）x) -- Eta transformation  $=$  u  $> =$  (return.（.）)   
pure(.）  $<  >$  u  $<  >$  v  $= (\mathrm{u} > > = (\mathrm{return}.(\cdot .))) <   >$  v -- rewrite  $<  >$ $= (\mathrm{u} > > = (\mathrm{return}.(\cdot .))) >> =$  \\f->(v  $\gg =$  \\x->return(fx)) --  $(\gg =)$  )is associative   
 $= \mathrm{u}\gg = (\backslash \mathrm{y}\rightarrow (\mathrm{return}.\cdot \cdot \cdot)\mathrm{y}\gg =$  \\f->(v  $\gg =$  \\x->return(fx)) -- rewrite the first instance of (return)   
 $= \mathrm{u}\gg = (\backslash \mathrm{y}\rightarrow (\mathrm{return}(\cdot .\mathrm{y})\gg =$  \\f->(v  $\gg =$  \\x->return(fx)) -- the 1st instance of (return) is a left unit   
 $= \mathrm{u}\gg = (\backslash \mathrm{y}\rightarrow \mathrm{v}\gg = \backslash \mathrm{x}\rightarrow \mathrm{return}(\cdot .\mathrm{y}\mathrm{x}))$  -- streamline the subexpression   
 $= \mathrm{u}\gg = (\backslash \mathrm{y}\rightarrow \mathrm{v}\gg = \backslash \mathrm{x}\rightarrow \mathrm{return}(\mathrm{y}.\mathrm{x})$
```

The scope of lambda binding extends to as right as possible. So, the parentheses at the top level are redundant. Just for readability.

```haskell
pure（.） $\ll >$  u  $\ll >$  v  $\ll >$  w  
 $= (\mathrm{u} >> = (\backslash \mathrm{y} -> \mathrm{v} >> = \backslash \mathrm{x} -> \mathrm{return}(\mathrm{y} . \mathrm{x}))$ $\ll >$  w  
-- rewrite  $\ll >$ $= (\mathrm{u} >> = (\backslash \mathrm{y} -> \mathrm{v} >> = \backslash \mathrm{x} -> \mathrm{return}(\mathrm{y} . \mathrm{x}))$ $\gg =$
```

```txt
$\backslash \mathrm{f}\rightarrow \mathrm{w} > > = \backslash \mathrm{z}\rightarrow$  return (f z) --  $(> > =)$  is associative   
 $= u > > = (\backslash g\rightarrow (\backslash y\rightarrow v > > = \backslash x\rightarrow$  return (y.x))g  $>> =$ $\backslash \mathrm{f}\rightarrow \mathrm{w} > > = \backslash \mathrm{z}\rightarrow$  return (f z)） -- Beta reduction   
 $= u > > = (\backslash g\rightarrow (v > > = \backslash x\rightarrow$  return (g.x))  $>> =$ $\backslash \mathrm{f}\rightarrow \mathrm{w} > > = \backslash \mathrm{z}\rightarrow$  return (f z)） --  $(> > =)$  is associative   
 $= u > > = \backslash g\rightarrow v > > =$ $(\backslash h\rightarrow (\backslash x\rightarrow$  return (g.x))h  $>> =$ $\backslash \mathrm{f}\rightarrow \mathrm{w} > > = \backslash \mathrm{z}\rightarrow$  return (f z)） -- Beta reduction   
 $= u > > = \backslash g\rightarrow v > > =$ $(\backslash h\rightarrow$  return (g.h)  $>> =$ $\backslash f\rightarrow w >> = \backslash z\rightarrow$  return (f z)） -- the 1st instance of (return) is a left unit   
 $= u > > = \backslash g\rightarrow v > > = \backslash h\rightarrow w > > = \backslash z\rightarrow$  return (g (h z))
```

So much for the LHS. Next, we focus on the RHS.

```latex
$\begin{array}{rl} & \mathrm{v <   * > w}\\ & = \mathrm{v} > > = \backslash \mathrm{f} - > \mathrm{w} > > = \backslash \mathrm{x} - > \mathrm{return} (\mathrm{f} \mathrm{x})\\ & \mathrm{u <   * > (v <   * > w)}\\ & = \mathrm{u} <   * > (\mathrm{v} > > = \backslash \mathrm{f} - > \mathrm{w} > > = \backslash \mathrm{x} - > \mathrm{return} (\mathrm{f} \mathrm{x}))\\ & \qquad --\mathrm{rewrite}<  * > \\ & = \mathrm{u} > > = \backslash \mathrm{g} - > (\mathrm{v} > > = \backslash \mathrm{f} - > \mathrm{w} > > = \backslash \mathrm{x} - > \mathrm{return} (\mathrm{f} \mathrm{x})) > > = \\ & \qquad \backslash \mathrm{h} - > \mathrm{return} (\mathrm{g} \mathrm{h})\\ & \qquad --(\gg =)is\mathrm{associative}\\ & = \mathrm{u} > > = \backslash \mathrm{g} - > \mathrm{v} > > = \\ & \qquad \backslash \mathrm{j} - > (\backslash \mathrm{f} - > \mathrm{w} > > = \backslash \mathrm{x} - > \mathrm{return} (\mathrm{f} \mathrm{x}))\mathrm{j} > > = \\ & \qquad \backslash \mathrm{h} - > \mathrm{return} (\mathrm{g} \mathrm{h})\\ & \qquad --\mathrm{Beta}\mathrm{reduction}\\ & = \mathrm{u} > > = \backslash \mathrm{g} - > \mathrm{v} > > = \\ & \qquad \backslash \mathrm{j} - > \mathrm{w} > > = \\ & \qquad \backslash \mathrm{f} - > (\backslash \mathrm{x} - > \mathrm{return} (\mathrm{j} \mathrm{x}))\mathrm{f} > > = \\ & \qquad \backslash \mathrm{h} - > \mathrm{return} (\mathrm{g} \mathrm{h})\\ & \qquad --\mathrm{Beta}\mathrm{reduction}\\ & = \mathrm{u} > > = \backslash \mathrm{g} - > \mathrm{v} > > = \\ & \qquad \backslash \mathrm{j} - > \mathrm{w} > >  = \\ & \qquad \backslash \mathrm{f} - > \mathrm{return} (\mathrm{j} \mathrm{f}) >> = \\ & \qquad \backslash \mathrm{h} - > \mathrm{return} (\mathrm{g} \mathrm{h})\\ & \qquad --\textbf{The 1st instance of (return) is a left unit}\\ & = \mathrm{u} >> = \backslash \mathrm{g} - > \mathrm{v} >> = \\ & \qquad \backslash \mathrm{j} - > \mathrm{w} >> = \\ & \qquad \backslash \mathrm{f} - > \mathrm{return} (\mathrm{g} (\mathrm{j}\mathrm{f}))\\ & \end{array}$
```

Changing local variables' names, we see that the LHS and RHS are identical. Next, we prove pure  $f < *$  pure  $x =$  pure (f  $x$ ). We calculate the LHS.

```txt
pure f  $<  *>$  pure x -- rewrite (pure) and  $<  *>$ $=$  return f  $> > =$ $\backslash g - >$  (return  $\mathbf{x} > > =$  return  $(\mathrm{g}\times)$  -- the 2nd instance of (return) is a left unit   
 $=$  return f  $> > =$ $\backslash g - >$  return  $(\mathrm{g}\times)$  -- the 1st instance of (return) is a left unit   
 $=$  return  $(f\times)$ $=$  pure  $(f\times)$
```

Finally, we show u <> pure y = pure ($ y) <> u. We calculate the LHS.

```txt
u  $<  >$  pure y -- rewrite  $<  >$ $\begin{array}{rl} & = u >> = \backslash f\rightarrow \mathrm{pure~y~} >> = \backslash x\rightarrow \mathrm{return~(f~x)}\\ & \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$  -- rewrite (pure)   
 $= u >> = \backslash f\rightarrow$  return y  $>> =$  \\x -> return (f x) -- the 1st instance of return) is a left unit   
 $= u >> = \backslash f\rightarrow$  return (f y)
```

We calculate the RHS.

```txt
pure (\( y) <\ast> u
-- rewrite (pure) and <\ast>
= return (\) y) >= \f -> (u >= \x -> return (f x))
-- the 1st instance of (return) is a left unit
= u >= \x -> return ((\) y) x)
= u >= \x -> return (x y)
```

Changing local variables' names, we see that the LHS and RHS are identical.

Proposition 6.5 In the derivation (3), fmap defined by pure satisfies all the functor rules.

Proof We show fmap  $\text{id} = \text{id}$ .

```txt
fmap id x -- rewrite (fmap)  $=$  pure id  $\text{<  } * >$  x -- (pure id) is a unit  $= \mathbf{x}$
```

Next, we show fmap (g . f) = fmap g . fmap f.

```txt
fmap (g . f) x
```

```haskell
-- rewrite fmap  
= pure (g . f) < $\Rightarrow$  x  
= pure ((. ) g f) < $\Rightarrow$  x  
(fmap g . fmap f) x  
= fmap g (fmap f x)  
-- rewrite fmap  
= pure g < $\Rightarrow$  pure f < $\Rightarrow$  x  
-- composition rule for (. ) and < $\Rightarrow$   
= pure (. ) < $\Rightarrow$  pure g < $\Rightarrow$  pure f < $\Rightarrow$  x  
-- homomorphism  
= pure (. ) g) < $\Rightarrow$  pure f < $\Rightarrow$  x  
-- homomorphism  
= pure (. ) g f) < $\Rightarrow$  x
```

This concludes that fmap  $(\mathbf{g}.\mathbf{f}) = \mathbf{f}$  map g . fmap f.

![](images/2fd4b1ff536dd6e56b28814c029e2c35a7fec7d2c7e11847f68f6087965ba713.jpg)

We have established implications among the concepts of Functor, Applicative, and Monad.

# 6.6 Monads and Adjoints

Monads and adjoints are tightly related. An adjoint gives a Monad. A Monad gives an adjoint. In this section, we will show that we can construct a Monad for a given adjoint. We leave the question if there always is an adjoint for a given Monad. This problem has been completely solved, but we only give an example of the list Monad case.

# 6.6.1 Adjoints to Monads

Theorem 6.4 Let  $F: \mathcal{X} \to \mathcal{A}$  be a left adjoint of  $U: \mathcal{A} \to \mathcal{X}$  with unit  $\eta$  and counit  $\varepsilon$ . Let  $T$  be an endofunctor defined by  $T = U \circ F: \mathcal{X} \to \mathcal{X}$ . Let  $\mu$  be a natural transformation defined by  $\mu = U \varepsilon F$ . Then, the triple  $(T, \eta, \mu)$  is a Monad on  $\mathcal{X}$ .

Proof We show that the triple  $(T, \eta, \mu)$  satisfies the Monad axioms:

(1)  $\mu_A\circ T\eta_A = 1_{TA}$  
(2)  $\mu_A\circ \eta_{TA} = 1_{TA}$  
(3)  $\mu_A\circ \mu_{TA} = \mu_A\circ T\mu_A$

We use the second alternative definition of adjoint justified by Theorem 5.1: there exist natural transformations  $\eta : \operatorname{Id}_{\mathcal{X}} \to UF$  and  $\varepsilon : F U \to \operatorname{Id}_{\mathcal{A}}$  that make the following two diagrams commute.

$$
\begin{array}{c c} U \xrightarrow {\eta U} U F U & F U F \xleftarrow {F \eta} F \\ \Bigg \downarrow_ {U \varepsilon} & \varepsilon F \\ U & F \end{array} \tag {6.3}
$$

1. We prove  $\mu T\eta = T$

Substituting  $T$  with  $UF$  and  $\mu$  with  $U\varepsilon F$  in, we can rewrite the goal as follows.

$$
U \varepsilon F U F \eta = U F
$$

We calculate horizontal and vertical compositions with functors and natural transformations intermixed. Note that horizontal arrows are drawn from left to right in the diagrams, which may confuse the reader when one compares a formula to its corresponding diagram.

We start with a subexpression  $U F \eta$  of the LHS. It is a horizontal composition of the natural transformation  $\eta$  and the functor  $U F$ . We can draw a diagram:

$$
\mathcal {X} \xrightarrow [ U F ]{\overset {\text {I d}} {\bigtriangledown \eta}} \mathcal {X} \xrightarrow {U F} \mathcal {X} \quad = \quad \mathcal {X} \xrightarrow [ U F U F ]{\overset {U F} {\bigtriangledown \eta}} \mathcal {X}
$$

We vertically compose this result with a natural transformation  $U \varepsilon F: U F U F \to U F$  to obtain the whole LHS. Note that functor  $U$  can be horizontally factored out:

$$
\begin{array}{c c} \overbrace {\underset {U F \eta} {\bigcup}} ^ {U F} \mathcal {X} & = \quad \mathcal {X} \xrightarrow {\underset {U F} {\bigcup}} \mathcal {A} \xrightarrow {U} \mathcal {X} \\ \hline U F & \end{array}
$$

The triangle at right in the diagram (6.3) tells us that the vertical composition of  $F\eta$  and  $\varepsilon F$  is  $\operatorname{Id}: F \to F$ . Thus, the result is  $\operatorname{Id}_{UF}$ , which is an alternative expression for  $UF$ . This completes the first goal.

2. We prove  $\mu \eta T = T$

Substituting  $T$  with  $UF$  and  $\mu$  with  $U\varepsilon F$  in, we can rewrite the goal as follows.

$$
U \varepsilon F \eta U F = U F
$$

We factor the LHS as the horizontal composition of  $U \varepsilon F$  and  $\eta UF$ .

![](images/57137305e94992b91984a1283f73f966aa64777b8ac95b546bcba0680492d99b.jpg)

We immediately find that this can be rewritten as a vertical composition:

![](images/7edc79b2150e7f2959fb5708fd334a06f76363cb6098827d88ff558dc9ee2a65.jpg)

We can factor out  $F$ .

![](images/a54796d455f6453cb298c4d4430b2d627be384a596a3ce8d84e7519a390e8a17.jpg)

The triangle at left in the diagram (6.3) tells us that the vertical composition is  $\operatorname{Id}: U \to U$ . Thus, the result is  $UF$ . This completes the second goal.

3. We prove  $\mu \mu T = \mu T\mu$

Substituting  $T$  with  $U F$  and  $\mu$  with  $U \varepsilon F$  in, we can rewrite the goal as follows.

$$
U \varepsilon F U \varepsilon F U F = U \varepsilon F U F U \varepsilon F
$$

The naturality of  $\varepsilon:FU\to \mathrm{Id}$  is expressed as  $\varepsilon F U = F U\varepsilon$  .We have

$$
U \varepsilon F U \underline {{\varepsilon}} F U F = U \varepsilon F U \underline {{F}} U \underline {{\varepsilon}} F.
$$

The linerlined subexpressions are identical. This completes the third goal.

# 6.6.2 ListMonad as Adjoint

The list Monad can be decomposed as a pair of adjoint functors.

Definition 6.3 Given a set  $A$  and a binary operation  $\bullet : A \times A \to A$ , we say the pair  $(A, \bullet_A)$  is a monoid if it satisfies the following conditions:

(1)  $\bullet_A$  is associative.  
(2)  $\bullet_A$  has left and right unit.

Having left and right units means that there is  $1_A \in A$  such that  $1_A \bullet a = a \bullet 1_A = a$  holds for any  $a \in A$ . Set  $A$  is called an underlying set. We say simply that  $A$  is a monoid if it is clear from the context.

Given two monoids  $(A, \bullet_A)$ ,  $(B, \bullet_B)$ , a mapping  $f: A \to B$  is said to be a monoid homomorphism if the following conditions are satisfied.

(1)  $f(x\bullet_Ay) = f(x)\bullet_Bf(y)$  
(2)  $f(1_A) = 1_B$

Definition 6.4 Given an alphabet  $\Sigma$ , namely a set of letters to be used. The set of all finite strings consisting of elements of  $\Sigma$  is a monoid with string concatenation as the binary operation  $\bullet$ , and the empty string  $\varepsilon$  as a unit. There are no relations other than those appearing in the axioms. We call this monoid a free monoid over  $\Sigma$  and write  $\Sigma^{*}$ . When we work with a programming language, we often adopt a list representation. For example, a finite string  $x_{1}x_{2}\dots x_{n}$  is represented by a list  $[x_{1},x_{2},\ldots ,x_{n}]$ . The empty string is represented by the empty list []. The concatenation of strings is translated into a concatenation of lists.

Remark 6.7 We observe the terminology in formal language theory. An alphabet is the set of letters that are used to construct a language.

Definition 6.5 Category Mon is called the category of all monoids. Its objects are all monoids. Its morphisms are all homomorphisms between the monoids.

We consider two functors between categories Set and Mon.

- A forgetful functor  $U: \mathbf{Mon} \to \mathbf{Set}$  with function on objects:

$$
U _ {0}: \operatorname {O b j} (\mathbf {M o n}) \rightarrow \operatorname {O b j} (\mathbf {S e t})
$$

$$
(A, \bullet_ {A}) \mapsto A
$$

For any monoid  $M = (A, \bullet_A)$ , we write  $U M = U_0(M) = A = \underline{M}$ . Function on objects is defined as follows. For any pair of monoids  $M$  and  $N$ , we set

$$
U _ {1} (M, N): \operatorname {M o n} (M, N) \rightarrow \operatorname {S e t} (\underline {{M}}, \underline {{N}})
$$

$$
f \mapsto \underline {{f}}
$$

We write  $f$  to indicate it is obtained from  $f$  forgetting the monoid structures.

- A free functor  $F$  with function on objects:

$$
F _ {0}: \operatorname {O b j} (\mathbf {S e t}) \rightarrow \operatorname {O b j} (\mathbf {M o n})
$$

$$
X \mapsto (\operatorname {L i s t} (X), + +)
$$

It maps a set  $X$  to the free monoid on  $X$ . The underlying set of  $F(X)$  is  $\operatorname{List}(X)$ , consisting of all the finite lists  $[x_1, \dots, x_n]$ . Function on morphisms is defined as follows. For any pair of sets  $X$  and  $Y$ , we set

$$
F _ {1} (X, Y): \operatorname {S e t} (X, Y) \rightarrow \operatorname {M o n} (\operatorname {L i s t} (X), \operatorname {L i s t} (Y))
$$

$$
f \mapsto \operatorname {m a p} f,
$$

where map is the same as those that have the same name in various programming languages.

We consider the composite  $FU: \mathbf{Mon} \to \mathbf{Mon}$ . Starting with a monoid  $(A, \bullet_A, 1_A)$ , the object function sends it to  $UA$ , the underlying set of the monoid  $A$ . We further apply  $F$  to  $UA$  to get  $FUA$  which is a free monoid on  $UA$ . An element of  $FUA$  is a list of elements in  $A$ . The binary operation is the concatenation of lists. Let  $[a_1, \dots, c_m]$  and  $[b_1, \dots, b_n]$  be a list of elements of  $A$ , which is, as stated above, elements of the monoid  $FUA$ . We have

$$
\left[ a _ {1}, \dots , a _ {m} \right] \bullet_ {F U A} \left[ b _ {1}, \dots , b _ {n} \right] = \left[ a _ {1}, \dots , c _ {m}, b _ {1}, \dots , b _ {n} \right]
$$

and

$$
[ ] \bullet_ {F U A} [ a _ {1}, \dots , a _ {m} ] = [ a _ {1}, \dots , a _ {m} ] \bullet_ {F U A} [ ] = [ a _ {1}, \dots , a _ {m} ].
$$

We construct a natural transformation  $\varepsilon$  from the functor  $FU: \mathbf{Mon} \to \mathbf{Mon}$  to  $\mathrm{Id}_{\mathbf{Mon}}: \mathbf{Mon} \to \mathbf{Mon}$ . For any monoid  $(A, \bullet_A, 1_A)$ , as we have just seen,  $FUA$  is a free monoid. We define a homomorphism from  $FUA$  to  $A$  as follows. Only we have to do is determine the image of each generator of the free monoid  $FUA$ .

$$
[ a _ {1}, \dots , a _ {n} ] \mapsto a _ {1} \bullet_ {A} a _ {2} \bullet_ {A} \dots \bullet_ {A} a _ {n},
$$

which extends straightforwardly to the whole domain, namely the free monoid. The homomorphism turns out to be the  $A$  component of a natural transformation. We leave the proof of naturality to the reader.

We consider the composite  $UF: \mathbf{Set} \to \mathbf{Set}$ . Starting with a set  $X$ , the object function sends it to  $FX$ , a free monoid on  $X$ . The underlying set of this monoid  $FX$ , that is  $UFX$ , is the set of all lists that consist of elements of  $X$  allowing repetition.

We construct a natural transformation  $\eta$  from  $\mathrm{Id}_{\mathrm{Set}}: \mathbf{Set} \to \mathbf{Set}$  to  $UF: \mathbf{Set} \to \mathbf{Set}$ . For any set  $X$ , we define

$$
\eta_ {X}: x \mapsto [ x ].
$$

This map turns out to be the  $X$  component of a natural transformation. We leave the proof of naturality to the reader.

We can claim the following proposition concerning  $U, F, \eta$ , and  $\varepsilon$  so constructed.

Proposition 6.6  $F: \mathbf{Set} \to \mathbf{Mon}$  is a left adjoint of  $U: \mathbf{Mon} \to \mathbf{Set}$ , with a unit  $\eta$  and a counit  $\varepsilon$ . (List  $= UF$ ,  $\eta, \mu = U\varepsilon F$ ) is a Monad obtained from this adjunction.

Proof We repeat diagrams (6.3) below.

![](images/8cb070b71c94a8b78219fd9402cbdf656a7f521c70ae8aca24d1a2c681a4cee9.jpg)

It is sufficient to show that the two triangles commute.

1. We calculate the composition of two edges in the triangle at left. Let  $A$  be a monoid.  $UA$  is the underlying set of  $A$ .  $\eta_{UA}$  is a mapping defined by

$$
\begin{array}{l} \eta_ {U A}: U A \rightarrow U F U A \\ \underline {{x}} \mapsto [ x ], \\ \end{array}
$$

where we used underlines to indicate that we forgot the algebraic structure. Before proceeding to the calculation of  $U \varepsilon_{A}$ , let us recall  $\varepsilon_{A}$  itself.

$$
\begin{array}{l} \varepsilon_ {A}: F U A \to A \\ [ x _ {1}, \dots , x _ {n} ] \mapsto x _ {1} \dots x _ {n} \\ \end{array}
$$

We forget the monoid structure by operating  $U$ . We have

$$
\begin{array}{l} U \varepsilon_ {A}: U F U A \rightarrow U A \\ \left[ x _ {1}, \dots , x _ {n} \right] \mapsto x _ {1} \dots x _ {n} \\ \end{array}
$$

Compose them to obtain

$$
\begin{array}{l} U \varepsilon_ {A} \circ \eta_ {U A}: U A \to U A \\ \underline {{x}} \mapsto \underline {{x}}, \\ \end{array}
$$

which shows that  $U \varepsilon_{A} \circ \eta_{UA} = 1_{UA}$  for all  $A$ . Thus, we conclude  $U \eta \circ \varepsilon U = \operatorname{Id}_{U}$ . 2. We calculate the composition of two edges in the triangle at right. Let  $X$  be a set. We have

$$
\begin{array}{l} \eta_ {X}: X \to U F X \\ x \mapsto [ x ]. \\ \end{array}
$$

If we further apply  $F$  to it, we obtain the following:

$$
\begin{array}{l} F \eta_ {X}: F X \rightarrow F U F X \\ \hat {x} \mapsto [ \hat {x} ], \\ \end{array}
$$

where  $\hat{x}$  is  $x$  regarded as an element of the free monoid.

$$
\begin{array}{l} \varepsilon_ {F X}: F U F X \rightarrow F X \\ [ \hat {x} _ {1}, \hat {x} _ {2}, \dots , \hat {x} _ {n} ] \mapsto \hat {x} _ {1} \hat {x} _ {2} \dots \hat {x} _ {n} \\ \end{array}
$$

We compose these to obtain

$$
\begin{array}{l} \varepsilon_ {F X} \circ F \eta_ {X}: F X \rightarrow F X \\ \hat {x} \mapsto \hat {x}, \\ \end{array}
$$

which shows  $\varepsilon_{FX} \circ F\eta_X = 1_{FX}$ . Thus, we conclude that  $\varepsilon F \circ F\eta = \operatorname{Id}_{FX}$ .

□

Example 6.1 Let  $U: \mathbf{Mon} \to \mathbf{Set}$  be a forgetful functor,  $F: \mathbf{Set} \to \mathbf{Mon}$  a free functor. We define a monoid  $(A, \bullet_A)$  as follows.

(1)  $A = \{1,a,a^2\}$  is the underlying set.  
(2) The binary operation is given in the table below:

<table><tr><td></td><td>1</td><td>a</td><td>a2</td></tr><tr><td>1</td><td>1</td><td>a</td><td>a2</td></tr><tr><td>a</td><td>a</td><td>a2</td><td>1</td></tr><tr><td>a2</td><td>a2</td><td>1</td><td>a</td></tr></table>

To sum up, this is a monoid with a generator  $a$  and a sole relation  $a^3 = 1$ . The forgetful functor  $U: \mathbf{Mon} \to \mathbf{Set}$  gives  $UA = \{1, a, a^2\}$ . Function on morphisms sends a monoid homomorphism

$$
\begin{array}{l} f: A \to A \\ 1 \mapsto 1 \\ a \mapsto a ^ {2} \\ a ^ {2} \mapsto a \\ \end{array}
$$

to a plain mapping  $Uf: A \to A$  forgetting its being a homomorphism. For examples of an element of  $FU(A)$ , we may list

$$
[ a, a ^ {2} ], \quad [ 1 ], \quad [ 1, a ^ {2} ], \quad [ a, a, a, a ].
$$

We can generate other elements of  $FU(A)$  by the free functor.

$FU(A)$  is a monoid as well as  $A$ . We can define a monoid homomorphism  $\varepsilon_A: FU(A) \to A$  as follows.

$\varepsilon_{A}$  sends a given list to the result of all possible monoid calculations. This setting makes  $\varepsilon_{A}$  a monoid homomorphism. For example, the calculation goes like this:

$$
\varepsilon_ {A}: [ a ] + + [ a ^ {2}, 1 ] + + [ a, a ] \mapsto \varepsilon_ {A} ([ a, a ^ {2}, 1, a, a ]) = a ^ {2}
$$

# Reference

1. Moggi E, Notions of computation and monads. https://person.dibris.unige.it/moggi-eugenio/ftp/ic91.pdf

# Representable Functors

7

In this chapter, aiming at Yoneda's lemma, we introduce the notion of representable functors. Roughly speaking, Yoneda's lemma shows that natural transformations are determined by local information. It can also be described as coherence or resonance. In the section on "reverse engineering," the resonance phenomenon is verified by Yoneda's lemma.

Closely related to the notions of limit and adjoint, it is possible to paraphrase the same mathematical phenomenon in different terms. Some examples are introduced at the end of the chapter.

It is cumbersome to properly write the naturality associated with various concepts, and so with the naturality that appears in Yoneda's lemma. The reader is requested to trace all the diagrams to get a feel of what naturality is all about.

# 7.1 Representation of Covariant Functors

Definition 7.1 Let  $\mathcal{A}$  be a locally small category and  $A$  a fixed object. For every object  $A'$ , we consider the set of morphisms  $\mathcal{A}(A, A')$ . We write this correspondence as follows:

$$
H ^ {A} = \mathscr {A} (A, -): \operatorname {O b j} (\mathscr {A}) \rightarrow \mathbf {S e t}
$$

$$
A ^ {\prime} \mapsto H ^ {A} (A ^ {\prime}) = \mathscr {A} (A, A ^ {\prime})
$$

We extend this definition to morphisms. For any morphism  $f: A' \to A''$  of  $\mathcal{A}$ , we define a mapping  $H^A(f)$  as follows:

$$
H ^ {A} (f) = \mathscr {A} (A, f): \quad \mathscr {A} (A, A ^ {\prime}) \longrightarrow \mathscr {A} (A, A ^ {\prime \prime})
$$

$$
g \longmapsto f \circ g
$$

The situation is depicted in Fig. 7.1.

![](images/e52de09dfab7b37a117ed7b1cc0f9743033b78e6e11e6ebc6ff4b8d9771537ce.jpg)  
Fig.7.1 Function on morphisms of the functor  $H^{A}$

Remark 7.1 We sometimes write  $f \circ -$  instead of  $H^{A}(f)$ . In a lambda expression, we may write as follows:

$$
H ^ {A} (f) = \lambda g \in \mathcal {A} (A, A ^ {\prime}). f \circ g
$$

Definition 7.2 Let  $\mathcal{A}$  be a locally small category. Let  $X:\mathcal{A}\to \mathbf{Set}$  be a functor. If the functor  $X$  is naturally isomorphic to  $H^{A}$  for some  $A\in \mathrm{Obj}(\mathcal{A})$ , we say  $X$  is representable. A representation of  $X$  is a pair  $(A,\phi)$  where  $\phi$  in

![](images/daa1b09b6cf07c9bc8794513e700404bcf110d41190f33736d10fb089d137026.jpg)

is a natural isomorphism.

Functor  $H^A: \mathcal{A} \to \mathbf{Set}$  is automatically a representable functor.

Example 7.1 A forgetful functor  $U: \mathbf{Grp} \to \mathbf{Set}$  is naturally isomorphic to  $\mathbf{Grp}(Z, -)$ . Given a group  $G$ , if we want a homomorphism  $\varphi$  from an infinite cyclic group  $\varphi$  to  $G$ , only we have to do is to determine the image  $\varphi(a) \in G$  of the generator  $a \in Z$ . In fact, we have no option but to set  $\varphi(a^n) = (\varphi(a))^n$ . Let us consider the other way around. Given any  $x \in U(G)$ , if we set  $\varphi(a^n) = x^n$ , we get a homomorphism  $\varphi: Z \to G$ .

We construct a natural transformation  $\alpha : \mathbf{Grp}(Z, -) \to U$ , which turns out to be a natural isomorphism.

We define  $\alpha$  as follows:

$$
\alpha_ {G}: \quad \operatorname {G r p} (Z, G) \longrightarrow U (G)
$$

$$
\varphi \longmapsto \varphi (a)
$$

Being a natural transformation requires the trapezoid at right in Fig. 7.2

![](images/e6dfef3f23684b7a309b33455da17f6668b68f57a049c197a35c54cd8230ee7b.jpg)

to commute.

To see this, we will show that the two paths of length two that originate at  $\varphi$  terminate at the same  $\bullet$  in Fig. 7.3. The path passing  $\varphi(a)$  terminates at  $(Uf)(\varphi(a)) = f(\varphi(a))$ . The path passing  $f \circ \varphi$  terminates at  $(f \circ \varphi)(a)$ . Notice that these terminating points are identical since both are the result of applying  $f$  and  $\varphi$  to  $a \in Z$ .

![](images/6a1fc550de4974ed1d3e974faeb59ca0b0fb211df6aabd7b8130d98b6d255e8e.jpg)  
Fig.7.2 Natural transformation  $\alpha : \mathbf{Grp}(Z, -) \to U$

![](images/53ec7122f84492f22659a8500bbeba27475856e655301df0fc7c7010f07e5522.jpg)  
Fig.7.3 Naturality of  $\alpha$

We have already known that for each  $G$  we have the inverse of  $\alpha_{G}$  as follows:

$$
\alpha_ {G} ^ {- 1}: \quad U (G) \longrightarrow \mathbf {G r p} (Z, G)
$$

$$
x \longmapsto (a ^ {n} \mapsto x ^ {n})
$$

Lemma 2.1 established that if all the components of a natural transformation are isomorphisms then the natural transformation itself is an isomorphism.

We can argue that representability is closely related to adjoints.

Theorem 7.1 Let  $\mathcal{A}$  and  $\mathcal{X}$  be locally small categories with adjunction:

$$
\phi_ {X, A}: \mathcal {A} (F X, A) \cong \mathcal {X} (X, U A).
$$

Then, the functor  $\mathcal{X}(X,U(-)):\mathcal{A}\to \mathbf{Set}$  is representable.

Proof We have to show that

$$
\phi_ {X, -}: \mathcal {A} (F X, -) \cong \mathcal {X} (X, U (-))
$$

is a natural transformation (consequently a natural isomorphism).

Recall the correspondence of an adjunction introduced in Sect. 5.1

$$
\frac {F X \xrightarrow {h} A \xrightarrow {a} A ^ {\prime}}{X \xrightarrow {} f U A \xrightarrow {} U a}
$$

This correspondence claims that the square in Fig. 7.4 commutes, which means  $\phi_{X, - }$  is natural. We know that for each  $A$ ,  $\phi_{X,A}$  is an isomorphism. Therefore, we can conclude that  $\phi_{X, - }$  is a natural isomorphism by Lemma 2.1.

Rewrite  $\mathcal{A}(FX, -)$  as  $H^{FX}$ . We have the following natural isomorphism:

$$
\phi_ {X, -}: H ^ {F X} \to \mathscr {X} (X, U (-)),
$$

which shows that  $\mathcal{X}(X,U(-))$  is representable.

![](images/24c527902f64740f6a45a428b10031e69136d94bd3aa0e69a4eaa7e459696ebd.jpg)  
Fig.7.4 Naturality of  $\phi_{X, - }$

We established that the composite functor  $\mathcal{X}(X,U(-))$  is representable. We can also show the right adjoint  $U$  is itself representable when it is a Set-valued functor.

Theorem 7.2 If there is an adjunction  $\phi$  between locally small categories  $\mathcal{A}$  and Set:

$$
\phi_ {X, A}: \mathcal {A} (F X, A) \cong \operatorname {S e t} (X, U A),
$$

then the functor  $U:\mathcal{A}\to \mathbf{Set}$  is representable.

Proof Let 1 be a singleton set. We have

$$
U (A) \cong \operatorname {S e t} (1, U (A)).
$$

This gives  $U \cong \operatorname{Set}(1, U(-))$ . Since we have already shown the RHS is representable, so is the LHS.

We consider the correspondence  $A \mapsto H^A$ , the function on objects that sends an object to a functor. We would like to augment it a function on morphisms that will make  $A \mapsto H^A$  a functor from the category  $\mathcal{A}$  to the functor category  $[\mathcal{A}, \mathbf{Set}]$ .

Recall that  $\mathrm{Obj}([\mathcal{A},\mathbf{Set}])$  consists of all the functors from  $\mathcal{A}$  to  $\mathbf{Set}$ , and that morphisms in  $[\mathcal{A},\mathbf{Set}]$  are natural transformations. If we only focus on function on objects, we might take

$$
\mathcal {A} \rightarrow [ \mathcal {A}, \mathbf {S e t} ].
$$

But, on morphisms, we should be careful about the directions of morphisms. The solution is that we should construct the following contravariant functor:

$$
\mathcal {A} ^ {\mathrm {o p}} \rightarrow [ \mathcal {A}, \mathbf {S e t} ].
$$

Definition 7.3 Let  $\mathcal{A}$  be a locally small category. We define a functor

$$
H ^ {-}: \mathcal {A} ^ {\mathrm {o p}} \rightarrow [ \mathcal {A}, \mathbf {S e t} ]
$$

as follows. The function on objects is given by  $A \mapsto H^{-}(A) = H^{A}$ . In lambda expression, we write

$$
H ^ {-} = \lambda A. \lambda B. \mathscr {A} (A, B)
$$

Given a morphism  $f: A' \to A$ . A natural transformation

$$
\mathcal {A} \xrightarrow {\begin{array}{c} H ^ {A} \\ \Big \downarrow H ^ {f} \\ H ^ {A ^ {\prime}} \end{array} } \mathbf {S e t}
$$

is defined by taking the  $B$ -component  $H_B^f$  as

$$
H ^ {-} (f) _ {B} = H _ {B} ^ {f}: \quad H ^ {A} (B) \longrightarrow H ^ {A ^ {\prime}} (B)
$$

$$
g \longmapsto g \circ f
$$

In the  $\lambda$  expression we write

$$
H ^ {f} = \lambda B. \lambda g \in \mathcal {A} (A, B). g \circ f
$$

# 7.2 Representation of Contravariant Functors

Discussions proceed almost parallelly with the previous section. However, examples in category Set, the most important ones, need some attention to asymmetry in arrow directions. Therefore, we repeat the whole arguments along with concrete examples.

Definition 7.4 Let  $\mathcal{A}$  be a locally small category and  $A$  a fixed object. For every object  $A'$ , we consider the set of morphisms  $\mathcal{A}(A', A) \in \mathrm{Obj}(\mathrm{Set})$ . We write this correspondence as follows:

$$
H _ {A} = \mathcal {A} (-, A): \operatorname {O b j} (\mathcal {A}) \rightarrow \operatorname {O b j} (\mathbf {S e t})
$$

$$
A ^ {\prime} \mapsto \mathcal {A} (A ^ {\prime}, A).
$$

We extend this correspondence to a function on morphisms in a unique way. For any morphism  $f: A'' \to A'$  of  $\mathcal{A}$ , we define a mapping  $H_A(f)$  as follows:

$$
H _ {A} (f) = \mathscr {A} (f, A): \quad \mathscr {A} \left(A ^ {\prime}, A\right) \longrightarrow \mathscr {A} \left(A ^ {\prime \prime}, A\right).
$$

$$
g \longmapsto g \circ f
$$

Thus, we have the functor

$$
H _ {A} = \mathscr {A} (-, A): \mathscr {A} ^ {\mathrm {o p}} \rightarrow \mathbf {S e t}.
$$

The situation is depicted in Fig. 7.5.

Remark 7.2 We sometimes write  $-\circ f$  instead of  $H_A(f)$ . In a lambda expression, we may write as follows:

$$
H _ {A} (f) = \lambda g \in \mathscr {A} \left(A ^ {\prime}, A\right). g \circ f
$$

Definition 7.5 Let  $\mathcal{A}$  be a locally small category. Let  $X:\mathcal{A}^{\mathrm{op}}\to \mathbf{Set}$  be a contravariant functor. If the functor  $X$  is naturally isomorphic to  $H_{A}$  for some  $A\in \operatorname {Obj}(\mathcal{A})$ , we say  $X$  is representable. A representation of  $X$  is a pair  $(A,\phi)$

![](images/50cc7599f42c3d20d1b5a59b164fe90e64cdefa38e398da3de6d9c99f3c0f34f.jpg)  
Fig.7.5 Contravariant functor  $H_{A}$  acts on morphisms

where  $\phi$  in

![](images/6af36abece8ce6e0186ff01952536fbe847c90f5210d7f48a2dda9af65a09de0.jpg)

is a natural isomorphism.

Contravariant functor  $H_A: \mathcal{A}^{\mathrm{op}} \to \mathbf{Set}$  is automatically a representable contravariant functor.

Example 7.2 We consider a contravariant functor  $\mathcal{P}:\mathbf{Set}^{\mathrm{op}}\to \mathbf{Set}$ . Function on objects sends a set  $X$  to its power set  $\mathcal{P}(X)$ . Function on morphisms sends a morphism  $f:X^{\prime}\rightarrow X$  to

$$
\mathscr {P} (f): \quad \mathscr {P} (X) \longrightarrow \mathscr {P} \left(X ^ {\prime}\right)
$$

$$
U \longmapsto f ^ {- 1} (U),
$$

where

$$
f ^ {- 1} (U) = \{x ^ {\prime} \in X ^ {\prime} \mid f (x ^ {\prime}) \in U \}.
$$

The characteristic function of a subset  $U \subset X$  is a function  $X \to \{0, 1\}$ . We write  $\mathbf{2} = \{0, 1\}$ . Then we have  $\mathcal{P} \cong H_2$ , which means that  $\mathcal{P}$  is representable.

We now study the correspondence  $A \mapsto H_A$ . Its variance will turn out to be covariant:

$$
\mathcal {A} \rightarrow [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ].
$$

Definition 7.6 Let  $\mathcal{A}$  be a locally small category. We aim to define a functor

$$
H _ {-}: \mathcal {A} \rightarrow [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ].
$$

Function on objects is given by  $A \mapsto H_A$ . We can write it in the lambda expression like

$$
H _ {-} = \lambda A. \lambda B. \mathcal {A} (B, A).
$$

Function on morphisms is defined as follows. Given a morphism  $f: A \to A'$ , we have to construct the corresponding natural transformation

$$
\mathcal {A} ^ {\mathrm {o p}} \xrightarrow { \begin{array}{c} H _ {A} \\ \Big \downarrow H _ {f} \\ H _ {A ^ {\prime}} \end{array} } \mathbf {S e t}
$$

The  $B$  component  $(H_{f})_{B}$  is given by

$$
\begin{array}{l} H _ {-} (f) _ {B} = \left(H _ {f}\right) _ {B}: \quad H _ {A} (B) \longrightarrow H _ {A ^ {\prime}} (B). \\ g \longmapsto f \circ g \\ \end{array}
$$

We can write it in the lambda expression like

$$
H _ {f} = \lambda B. \lambda g \in \mathscr {A} (B, A). f \circ g.
$$

Definition 7.7 Let  $\mathcal{A}$  be a locally small category. The functor

$$
H _ {-}: \mathscr {A} \to [ \mathscr {A} ^ {\mathrm {o p}}, \mathbf {S e t} ]
$$

is called the Yoneda embedding.

# 7.3 The Yoneda Lemma

The Yoneda lemma may be called a resonance theorem, which the reader will agree with after going through the whole discussion in this section. We will study the cases of covariant functors, contravariant functors (presheaves), and embeddings, in order.

# 7.3.1 Covariant Case

We fixed an object  $A$  of a category  $\mathcal{A}$  and defined a functor  $H^{A} = \mathcal{A}(A, -): \mathcal{A} \to \mathbf{Set}$  by  $A' \mapsto \mathcal{A}(A, A')$ . In what follows, we assume that  $\mathcal{A}$  is a small category. We consider a natural transformation  $\alpha: H^{A} \to X$  from the functor  $H^{A}: \mathcal{A} \to \mathbf{Set}$  to  $X: \mathcal{A} \to \mathbf{Set}$ .

Remark 7.3 We want to work within the functor category. It is possible for a locally small category  $\mathcal{A}$  to give the functor category  $[\mathcal{A},\mathbf{Set}]$  which is not locally small. To avoid this, we restrict  $\mathcal{A}$  to a small category or introduce another universe. We take the former option.

Let us observe a resonance caused by a natural transformation  $\alpha : H^A \to X$  in Fig. 7.6.

- First, focus on the  $A$  component of  $\alpha$ , namely, a mapping  $\alpha_{A}$  from the set  $H^{A}(A)$  to the set  $X(A)$ . The set  $H^{A}(A)$  has the identity morphism  $1_{A}$  as an element.  
- This identity morphism is sent to  $\alpha_A(1_A) \in X(A)$ .  
- Let  $A'$  be any object of  $\mathcal{A}$ . The  $A'$  component of  $\alpha$  is a mapping from the set  $H^{A}(A')$  to the set  $X(A')$ .  
- Let  $f$  be any element of  $H^{A}(A')$ . This  $f$  is, at the same time, a morphism  $f: A \to A'$ . Therefore, functor  $H^{A}$  sends  $f$  to

$$
H ^ {A} (f): H ^ {A} (A) \to H ^ {A} \left(A ^ {\prime}\right),
$$

which is a mapping between sets.

- Functor  $X$  sends morphism  $f$  to  $X(f)$ . By naturality of  $\alpha$ , the two paths in Fig. 7.6 originating from  $1_A$  must be identical as morphisms.  
- To sum up,  $\alpha_{A}(1_{A})$  determines all the components of  $\alpha$ . This is the resonance we are talking about.

We have just observed that there is a bijection between the set  $X(A)$  and the set of all natural transformations from the functor  $H^{A}$  to  $X$ , namely,  $[\mathcal{A}, \mathbf{Set}](H^{A}, X)$ . We still want to know how the bijection depends on  $A$  and  $X$ . To this end we need lots of preparation.

Our goal is given below.

![](images/0a43077f4ffff4f779c127d41459719e9763dc9463b5f361e15cc4e561edd7c0.jpg)  
Fig.7.6 Resonance between a covariant functor and a natural transformation

Theorem 7.3 (The Yoneda Lemma) Let  $\mathcal{A}$  be a small category. Then, the following isomorphism

$$
[ \mathcal {A}, \mathbf {S e t} ] (H ^ {A}, X) \simeq X (A)
$$

is natural in  $A$  and  $X$ .

Naturality, in this case, means that

- The LHS and RHS are functors, say  $L: \mathcal{A} \times [\mathcal{A}, \mathbf{Set}] \to \mathbf{Set}$  and  $R: \mathcal{A} \times [\mathcal{A}, \mathbf{Set}] \to \mathbf{Set}$ , respectively.  
- There is a natural isomorphism  $z: L \to R$ .

At first sight, the LHS of the equation in Theorem 7.3 looks like a functor of two arguments  $A$  and  $X$ . We give a rigorous description as follows. We use the construction of a product of categories. Review Definition 1.5.

The function on objects  $\mathrm{Obj}(A,X)\to \mathrm{Obj}(\mathbf{Set})$  is given as follows:

$$
\begin{array}{l} \mathcal {A} \times [ \mathcal {A}, \mathbf {S e t} ] \rightarrow \mathbf {S e t} \\ (A, X) \mapsto [ \mathscr {A}, \operatorname {S e t} ] (H ^ {A}, X) \\ \end{array}
$$

To be precise, this correspondence is the composition of two operations.

$$
\begin{array}{l} \mathcal {A} \times [ \mathcal {A}, \mathbf {S e t} ] \xrightarrow {(H ^ {-}) ^ {\mathrm {o p}} \times 1} [ \mathcal {A}, \mathbf {S e t} ] ^ {\mathrm {o p}} \times [ \mathcal {A}, \mathbf {S e t} ] \xrightarrow {[ \mathcal {A} , \mathbf {S e t} ] (- , -)} \mathbf {S e t} \\ (A, X) \longmapsto (H ^ {A}, X) \longmapsto [ \mathscr {A}, \operatorname {S e t} ] (H ^ {A}, X) \\ \end{array}
$$

Let us take a closer look at this composition. In the first stage,  $A \mapsto H^A$  is given by the contravariant functor  $H^{-} : \mathcal{A}^{\mathrm{op}} \to [\mathcal{A}, \mathbf{Set}]$ . In the second stage, the Hom functor  $[\mathcal{A}, \mathbf{Set}](-,-)$  expects its first argument  $H^A$  contravariantly. In this way, the composition observes the covariant-contravariant restriction.

Let us consider the functor  $\mathcal{A} \times [\mathcal{A}, \mathbf{Set}] \to \mathbf{Set}: (A, X) \mapsto [\mathcal{A}, \mathbf{Set}](H^A, X)$  with its second argument  $X$  fixed. We observe how its image depends on  $A$ . The image of  $f: A \to A'$  is found in the following diagram:

$$
\mathscr {A} \xrightarrow {(H ^ {-}) ^ {\mathrm {o p}}} [ \mathscr {A}, \mathbf {S e t} ] ^ {\mathrm {o p}} \longrightarrow [ \mathscr {A}, \mathbf {S e t} ] (H ^ {-}, X)
$$

$$
\begin{array}{c c c} A & \longrightarrow & H ^ {A} \\ f & \Bigg \downarrow & \Bigg \uparrow_ {H _ {f}} \\ & A ^ {\prime} & \longrightarrow H ^ {A ^ {\prime}} \end{array} \begin{array}{c c c} [ \mathscr {A}, \mathbf {S e t} ] (H ^ {A}, X) & \ni \alpha \\ & \Bigg \downarrow - \circ H ^ {f} \\ & \Bigg \downarrow \\ & [ \mathscr {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] (H ^ {A ^ {\prime}}, X) & \ni \alpha \circ H ^ {f} \end{array}
$$

Next, we fix  $A$  and observe the dependency on  $X$ . Let us consider a morphism  $\theta : X \to X'$  in  $[\mathcal{A}, \mathbf{Set}]$

![](images/b9fb3a69a1845902557de7901a52ca71d42c8b8000be1b6e571dd50664d87b6d.jpg)

which can be regarded as a natural transformation:

![](images/52cd3c59e9b50f882757608c92ef05d240abd679425ce59baec3e3883f820c51.jpg)

namely,  $\theta \mapsto (\theta \circ -)$ . We have to check if the functor really preserves the composition of morphisms:

$$
(\theta^ {\prime} \circ \theta) \circ - = (\theta^ {\prime} \circ -) \circ (\theta \circ -),
$$

which can be easily seen by the following diagram:

![](images/d4603b3ec5fdc287cdadef2e5c56d7e57a8837d33bb65c312ea0855a16befa2b.jpg)

Next, let us define the right-hand side of the equation in Theorem 7.3 as a functor in two variables  $A$  and  $X$ .

$$
\mathcal {A} \times [ \mathcal {A}, \operatorname {S e t} ] \longrightarrow \operatorname {S e t}
$$

$$
(A, X) \longmapsto X (A)
$$

This is called an evaluation functor. We fix  $X$  as a constant. For any morphism  $f: A \to A'$  we have

![](images/73cd80a7462e484c3bbc6055bc7446925a7eaaed3439b55a5f5c5a69962f0406.jpg)

which is a consequence of  $X$  being a functor  $\mathcal{A} \to \mathbf{Set}$ .

Fixing  $A$ , we want to define a functor  $[\mathcal{A}, \mathbf{Set}]$  with a function on objects  $X \mapsto X(A)$  and an appropriate function on morphisms as follows. For any morphism  $\theta$  in  $[\mathcal{A}, \mathbf{Set}]$

![](images/f92e2f3cab5f2783306b768a85832b4617d0bdf2030832b37eb5e626fb924c93.jpg)

which is actually a natural transformation between functors  $X$  and  $X'$ , we can simply take  $\theta \mapsto \theta_A$ . Composition of morphisms  $\theta : X \to X'$  and  $\theta': X' \to X''$  is given by

![](images/eb1a970a0847cff9ba3cbc371311433b3c6f1816b628157e92e32f9f40572fe6.jpg)

where we have commutative triangles at the left and right sides. This comes from the vertical composition of natural transformations  $\theta$  and  $\theta'$ . Combining the discussion before, we now have

$$
\mathscr {A} \times [ \mathscr {A}, \mathbf {S e t} ] \rightarrow \mathbf {S e t}: (A, X) \mapsto X (A)
$$

is a functor of two variables.

Proof (The Yoneda Lemma—Covariant case—Naturality in  $A$ )

The preparation above lets us proceed to prove that the following correspondence:

$$
y: [ \mathcal {A}, \operatorname {S e t} ] (H ^ {-}, X) \to X (-),
$$

whose component at  $A$  is given by

$$
y _ {A} = [ \mathscr {A}, \mathbf {S e t} ] (H ^ {A}, X) \rightarrow X (A): \alpha \mapsto \alpha_ {A} (1 _ {A})
$$

can be made into a natural transformation. For each morphism  $f: A \to A'$ , we have to show that the two paths from  $\alpha$  to  $X(A')$  in Fig. 7.7 are identical. In other words, we have to show the following equation holds:

$$
(\alpha \circ H ^ {f}) _ {A ^ {\prime}} (1 _ {A ^ {\prime}}) = (X f) (\alpha_ {A} (1 _ {A})).
$$

We transform the LHS step by step as follows:

$$
\begin{array}{l} (\alpha \circ H ^ {f}) _ {A ^ {\prime}} (1 _ {A ^ {\prime}}) \\ = \alpha_ {A ^ {\prime}} \left(\left(H ^ {f}\right) _ {A ^ {\prime}} \left(1 _ {A ^ {\prime}}\right)\right) \\ = \alpha_ {A ^ {\prime}} \left(1 _ {A ^ {\prime}} \circ f\right) \\ = \alpha_ {A ^ {\prime}} (f). \\ \end{array}
$$

![](images/56e2d347315b200e0cfd6856df044a973703c3aebc1ef01b1f34af11a273df0b.jpg)  
Fig.7.7 Naturality with  $A$  (covariant version)

The last expression above is equal to the RHS since  $\alpha$  is a natural transformation that makes the following square commute:

$$
\begin{array}{c} H ^ {A} (A) \ni 1 _ {A} \xmapsto {\alpha_ {A}} \alpha (1 _ {A}) \in X (A) \\ H ^ {A} (f) \Bigg | _ {\Bigg |} \Bigg | _ {\Bigg |} X (f) \\ H ^ {A} (A ^ {\prime}) \ni f \xmapsto {} _ {\alpha_ {A ^ {\prime}}} (X f) (\alpha_ {A} (1 _ {A})) \in X (A ^ {\prime}) \end{array}
$$

which lives in Fig. 7.6. This completes the proof.

Proof (The Yoneda Lemma—Covariant case—Naturality in  $X$ ) We fix  $A$  and show that the following correspondence:

$$
z: [ \mathscr {A}, \operatorname {S e t} ] (H ^ {A}, -) \to (-) (A),
$$

whose component at  $X$  is given by

$$
z _ {X} = [ \mathscr {A}, \operatorname {S e t} ] (H ^ {A}, X) \rightarrow X (A): \alpha \mapsto \alpha_ {A} (1 _ {A})
$$

can be made into a natural transformation.

Let  $\theta$  be a morphism in  $[\mathcal{A},\mathbf{Set}]$

![](images/74bebc020494b80b7545f9bf9c2466ca2fa71815a7fec8e9b7edd33ada4984be.jpg)

Only we have to show is that the two paths in Fig. 7.8 starting from  $\alpha$  coincide, which is clear from the definition of function composition.

![](images/1bb1eb58eddacd60a6665f3fcaaf7c593a2fd5c820b8891bfbf113eb199ccd18.jpg)  
Fig.7.8 Naturality in  $X$  (covariant version)

# 7.3.2 Contravariant Case (Presheaves)

We fixed an object  $A$  of a category  $\mathcal{A}$  and defined a contravariant functor  $H_A = \mathcal{A}(-, A): \mathcal{A}^{\mathrm{op}} \to \mathbf{Set}$  by  $A' \mapsto \mathcal{A}(A', A)$ . Let us consider a natural transformation  $\alpha: H_A \to X$  between functors  $H_A: \mathcal{A}^{\mathrm{op}} \to \mathbf{Set}$  and  $X: \mathcal{A}^{\mathrm{op}} \to \mathbf{Set}$ . Reversing all arrows in the covariant case gives us the result for the contravariant case. We repeat the whole parallel argument in the following. We suppose that  $\mathcal{A}$  is a small category from the same reason described in Remark 7.3. Let us observe a resonance caused by a natural transformation  $\alpha: H_A \to X$  in Fig. 7.9.

- First, focus on the  $A$  component of  $\alpha$ , namely, a mapping  $\alpha_{A}$  from the set  $H_{A}(A)$  to the set  $X(A)$ . The set  $H_{A}(A)$  has the identity morphism  $1_{A}$  as an element.  
- This identity morphism is sent to  $\alpha_A(1_A) \in X(A)$ .  
- Let  $A'$  be any object of  $\mathcal{A}$ . The  $A'$  component of  $\alpha$  is a mapping from the set  $H_A(A')$  to the set  $X(A')$ .  
- Let  $f$  be any element of  $H_A(A')$ . This  $f$  is, at the same time, a morphism  $f: A' \to A$ . Therefore, contravariant functor  $H_A$  sends  $f$  to

$$
H _ {A} (f): H _ {A} (A) \rightarrow H _ {A} \left(A ^ {\prime}\right),
$$

which is a mapping between sets.

- Contravariant functor  $X$  sends morphism  $f$  to  $X(f)$ . By naturality of  $\alpha$ , the two paths in Fig. 7.9 originating from  $1_A$  must be identical as morphisms.  
- To sum up,  $\alpha_{A}(1_{A})$  determines all the components of  $\alpha$ . This is the resonance we are talking about.

We have just observed that there is a bijection between the set  $X(A)$  and the set of all natural transformations from the functor  $H_{A}$  to  $X$ , namely,  $[\mathcal{A}^{\mathrm{op}},\mathbf{Set}](H_A,X)$ . We

![](images/84b163fe2fdc05bbbca9cd02bf9b0110c898a3ec879414adba4cb63d0381a1b2.jpg)  
Fig.7.9 Contravariant functors and the resonance of a natural transformation

still want to know how the bijection depends on  $A$  and  $X$ . To this end we need lots of preparation.

Our goal is given below.

Theorem 7.4 (The Yoneda Lemma (contravariant case)) Let  $\mathcal{A}$  be a small category. Then, the following isomorphism

$$
[ \mathcal {A} ^ {\mathrm {o p}}, \operatorname {S e t} ] (H _ {A}, X) \simeq X (A)
$$

is natural in  $A$  and  $X$ .

We need preparations to clearly state the naturality in  $A$  and  $X$ . We expect the LHS of the equation in Theorem 7.4 to be a functor in two variables  $A$  and  $X$ . Let us define the function on objects as follows:

$$
\mathcal {A} ^ {\mathrm {o p}} \times [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] \rightarrow \mathbf {S e t}
$$

$$
(A, X) \mapsto [ \mathcal {A} ^ {\mathrm {o p}}, \operatorname {S e t} ] (H _ {A}, X).
$$

To be precise, this correspondence is the composition of two operations.

$$
\begin{array}{l} \mathcal {A} ^ {\mathrm {o p}} \times [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] \xrightarrow {H _ {-} ^ {\mathrm {o p}} \times 1} [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] ^ {\mathrm {o p}} \times [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] \xrightarrow {[ \mathcal {A} ^ {\mathrm {o p}} , \mathbf {S e t} ] (- , -)} \mathbf {S e t} \\ (A, X) \longmapsto (H _ {A}, X) \longmapsto [ \mathscr {A} ^ {\mathrm {o p}}, \operatorname {S e t} ] (H _ {A}, X) \\ \end{array}
$$

Let us take a closer look at this composition. In the first stage,  $A \mapsto H_A$  is given by the covariant functor  $H_{-}^{\mathrm{op}}: \mathcal{A}^{\mathrm{op}} \to [\mathcal{A}^{\mathrm{op}}, \mathbf{Set}]^{\mathrm{op}}$ , which can be simply rewritten as  $H_{-}: \mathcal{A} \to [\mathcal{A}, \mathbf{Set}]$  as far as only objects are concerned. However, in the second stage, the Hom functor  $[\mathcal{A}^{\mathrm{op}}, \mathbf{Set}](-, -)$  expects its first argument  $H_A$  contravariantly.

Therefore, in the first stage we write  $\mathcal{A}^{\mathrm{op}}\rightarrow [\mathcal{A}^{\mathrm{op}},\mathbf{Set}]^{\mathrm{op}}$  for the left component. This way, the composition observes the covariant-contravariant restriction.

Let us consider the functor  $\mathcal{A}^{\mathrm{op}}\times [\mathcal{A}^{\mathrm{op}},\mathbf{Set}]\to \mathbf{Set}:(A,X)\mapsto [\mathcal{A}^{\mathrm{op}},\mathbf{Set}]$ $(H_{A},X)$  with its second argument  $X$  fixed. We observe how its image depends on  $A$ . The image of  $f:A'\rightarrow A$  is found to be  $-\circ H_{f}$  in the following diagram:

$$
\mathcal {A} ^ {\mathrm {o p}} \xrightarrow {H _ {-} ^ {\mathrm {o p}}} [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] ^ {\mathrm {o p}} \longrightarrow [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] (H _ {-}, X)
$$

$$
\begin{array}{c c c} A \longmapsto H _ {A} \longmapsto [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] (H _ {A}, X) & \ni \alpha \\ f \bigg \uparrow & \bigg \downarrow - \circ H _ {f} & \bigg \downarrow \\ A ^ {\prime} \longmapsto H _ {A ^ {\prime}} \longmapsto [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] (H _ {A ^ {\prime}}, X) & \ni \alpha \circ H _ {f} \end{array}
$$

Next, we fix  $A$ , the left argument of the functor  $\mathcal{A}^{\mathrm{op}} \times [\mathcal{A}^{\mathrm{op}}, \mathbf{Set}] \to \mathbf{Set}: (A, X) \mapsto [\mathcal{A}^{\mathrm{op}}, \mathbf{Set}](H_A, X)$ , and observe the dependency on  $X$ . Let us consider a morphism  $\theta: X \to X'$  in  $[\mathcal{A}, \mathbf{Set}]$

![](images/90235a71e5b5cc203ffe8751a54182bebd753ce7b93ff848bd83192521517826.jpg)

which can be regarded as a natural transformation:

![](images/a29dea2742f5fababcdbc7aa2e15646cc6721b2b2749223c93434ebc2ea0e2ca.jpg)

namely,  $\theta \mapsto (\theta \circ -)$

We have to check if the functor really preserves the composition of morphisms:

$$
\left(\theta^ {\prime} \circ \theta\right) \circ - = \left(\theta^ {\prime} \circ -\right) \circ \left(\theta \circ -\right)
$$

which can be easily seen by the following diagram:

![](images/b166a9eb0a5a0f7277ea3ac88b3a0efb6504dd090d93757e76479a4c083704af.jpg)

Next, let us define the right-hand side of the equation in Theorem 7.4 as a functor in two variables  $A$  and  $X$ .

$$
\mathcal {A} ^ {\mathrm {o p}} \times [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] \longrightarrow \mathbf {S e t}.
$$

$$
(A, X) \longmapsto X (A)
$$

This is called an evaluation functor which has been introduced already. We fix  $X$  as a constant. For any morphism  $f: A' \to A$  we have

$$
\begin{array}{c} A \longmapsto X (A) \\ \biguparrow_ {f} \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A ^ {\prime} \longmapsto X (A ^ {\prime})  , \end{array}
$$

which is a consequence of  $X$  being a functor  $\mathcal{A}\to \mathbf{Set}$

Fixing  $A$ , we want to define a functor  $[\mathcal{A}^{\mathrm{op}}, \mathbf{Set}]$  with a function on objects  $X \mapsto X(A)$  and an appropriate function on morphisms as follows. For any morphism  $\theta$  in  $[\mathcal{A}^{\mathrm{op}}, \mathbf{Set}]$

$$
\mathcal {A} ^ {\mathrm {o p}} \xrightarrow { \begin{array}{c} X \\ \Downarrow \theta \\ X ^ {\prime} \end{array} } \mathbf {S e t}
$$

which is actually a natural transformation between functors  $X$  and  $X'$ , we can simply take  $\theta \mapsto \theta_A$ . Composition of morphisms  $\theta : X \to X'$  and  $\theta': X' \to X''$  is given by

$$
\begin{array}{c} X \longmapsto X (A) \\ \theta^ {\prime} \circ \theta \left( \begin{array}{c c c} \theta & & \downarrow_ {\theta_ {A}} \\ X ^ {\prime} & & \downarrow_ {\theta_ {A} ^ {\prime}} \\ \theta^ {\prime} & & \downarrow_ {\theta_ {A} ^ {\prime}} \end{array} \right) (\theta^ {\prime} \circ \theta) _ {A} \\ X ^ {\prime \prime} \longmapsto X ^ {\prime \prime} (A), \end{array}
$$

where we have commutative triangles at the left and right sides. This comes from the vertical composition of natural transformations  $\theta$  and  $\theta'$ . Combining the discussion before, we now have

$$
\mathcal {A} ^ {\mathrm {o p}} \times [ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] \rightarrow \mathbf {S e t}: (A, X) \mapsto X (A)
$$

is a functor of two variables.

Proof (The Yoneda Lemma—Cotravariant case—Naturality in  $A$ )

The preparation above lets us proceed to prove that the following correspondence:

$$
y: [ \mathcal {A} ^ {\mathrm {o p}}, \operatorname {S e t} ] (H _ {-}, X) \to X (-),
$$

whose component at  $A$  is given by

$$
y _ {A} = \left[ \mathcal {A} ^ {\mathrm {o p}}, \operatorname {S e t} \right]\left(H _ {A}, X\right)\rightarrow X (A): \alpha \mapsto \alpha_ {A} \left(1 _ {A}\right)
$$

can be made into a natural transformation. For each morphism  $f: A \to A'$ , we have to show that the two paths from  $\alpha$  to  $X(A')$  in Fig. 7.10 are identical. In other words, we have to show the following equation holds:

$$
\left(\alpha \circ H _ {f}\right) _ {A ^ {\prime}} \left(1 _ {A ^ {\prime}}\right) = (X f) \left(\alpha_ {A} \left(1 _ {A}\right)\right). \tag {7.1}
$$

We transform the LHS step by step as follows:

$$
\begin{array}{l} (\alpha \circ H _ {f}) _ {A ^ {\prime}} (1 _ {A ^ {\prime}}) \\ = \alpha_ {A ^ {\prime}} \left(\left(H _ {f}\right) _ {A ^ {\prime}} \left(1 _ {A ^ {\prime}}\right)\right) \\ = \alpha_ {A ^ {\prime}} (f \circ 1 _ {A ^ {\prime}}) \\ = \alpha_ {A ^ {\prime}} (f). \\ \end{array}
$$

The last expression above is equal to the RHS in Eq. (7.1) since  $\alpha$  is a natural transformation that makes the following square commute:

$$
\begin{array}{c}H _ {A} (A) \ni 1 _ {A} \xmapsto {\alpha_ {A}} \rightarrow \alpha (1 _ {A}) \in X (A)\\H _ {A} (f) \Bigg \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad\\H _ {A} (A ^ {\prime}) \ni f \xmapsto {\alpha_ {A ^ {\prime}}} (\stackrel {{\alpha_ {A ^ {\prime}}} (f) =} {{\alpha_ {A ^ {\prime}}}} (X f) (\alpha_ {A} (1 _ {A}))} \in X (A ^ {\prime})\end{array}
$$

which lives in Fig. 7.9. This completes the proof.

![](images/8d8b290288df825e50b3d9803687b3a8acbaa3f742791435b06312695aa8382f.jpg)  
Fig.7.10 Naturality in  $A$  (contravariant case)

![](images/5f020fb3230899282cf1dde7c237448efeed23370ba6c7b0045d3c939365c0c1.jpg)  
Fig.7.11 Naturality in  $X$  (contravariant case)

Proof (The Yoneda Lemma—Contravariant version—Naturality in  $X$ ) We fix  $A$  and show that the following correspondence

$$
z: [ \mathscr {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] (H _ {A}, -) \to (-) (A),
$$

whose component at  $X$  is given by

$$
z _ {X} = \left[ \mathscr {A} ^ {\mathrm {o p}}, \operatorname {S e t} \right]\left(H _ {A}, X\right)\rightarrow X (A): \alpha \mapsto \alpha_ {A} \left(1 _ {A}\right)
$$

can be made into a natural transformation.

Let  $\theta$  be a morphism in  $[\mathcal{A}^{\mathrm{op}},\mathbf{Set}]$

![](images/402dcf98c385aab1b1e5054cd7a6b3c74079d4f54f58cb0a77ccf3a9848fe9f3.jpg)

Only we have to show is that the two paths in Fig. 7.11 starting from  $\alpha$  coincide, which is clear from the definition of function composition.

# 7.4 Milewski's "Understanding Yoneda"

In this and the next section, we will see that it is often the case that when creating a polymorphic function in a functional programming language, if a signature is given, the implementation may be almost determined by Yoneda's lemma.

# 7.4.1 Specification Determines Implementation

We will see an example of natural transformation imager and a polymorphic function iffie in the article of Milewski [1] (partially omitted and modified). The author himself calls it a teaser problem. Even if you don't understand it at first glance, you are requested to be patient.

Listing 7.1 yoneda.ms  
```haskell
1{-#LANGUAGE ExplicitForAll #-}   
2 imager ::forall r . ( (Bool -> r) -> [r])   
3 imager iffie = fmap iffie [True, False, True, True]   
4   
5 data Color  $=$  Red | Green | Blue deriving Show   
6 data Note  $= \mathrm{C}\mid \mathrm{D}\mid \mathrm{E}\mid \mathrm{F}\mid \mathrm{G}\mid \mathrm{A}\mid \mathrm{B}$  deriving Show   
7   
8 colorMap x = if x then Blue else Red   
9 heatmap x = if x then 32 else 212   
10 soundMap x = if x then C else G   
11   
12 idBool :: Bool -> Bool   
13 idBool x = x   
14   
15 {-suggested tests   
16 imager colorMap   
17 imager heatmap   
18 imager soundMap   
19 -}
```

Try running this program to see what happens.

```csv
\*Main> imager colorMap [Blue,Red,Blue,Blue] \*Main> imager heatmap [32,212,32,32] \*Main> imager soundMap [C,G,C,C]
```

The signature of imager in Line 2 says that it is a natural transformation from the Hom functor  $H^{\mathrm{Bool}}$  to List functor [ ]. According to Yoneda's lemma, this natural transformation has a one-to-one correspondence with an element of the "set" List Bool = [Bool]. Figure 7.12 is a redrawn version of the diagram used in the general theory of the Yoneda lemma to suit this example. According to Yoneda's lemma, we have

[ Hask, Set](HBooL, List) ≈ List(BooL).

In this formula, Set is written in, but informal alternative Hask might be replaced with. As mentioned above, it is not mathematically rigorous. Nevertheless, there is no practical problem, so let's continue the discussion. In Fig. 7.12, iffie is a representative in general of colorMap, heatmap, and soundMap. These are the

![](images/3dfbdde360170fb69888de49ba0265c0fd8861f6a43ebf5ffaebca1070e86c1f.jpg)  
Fig.7.12 Natural transformation imager

arbitrarily chosen morphisms  $\mathrm{Bool} \to a$ . For example, when  $a$  is taken as Color, there are  $2^3 = 8$  possible morphisms (ignoring undefined is one of the reasons for the lack of rigorousness mentioned above). Here are some examples.

```txt
colorMap1 = Red  
colorMap2 x = if x then Red else Blue  
colorMap3 x = if x then Red else Green
```

If we want to know the element of List Bool that corresponds the natural transformation imager, what should we do? The Yoneda lemma says that it is enough to find the image of  $1_{\mathrm{Bool}}$  by  $\mathrm{imagerr}_{\mathrm{Bool}}$ . We can do it as follows:

```txt
\*Main> imager idBool [True,False,True,True]
```

The obtained list of Bool is an internal information about the implementation of imager. This example gives us a lesson that an implementation details can be disclosed by the Yoneda lemma.

The information on the component  $\mathrm{imagerr}_{\mathrm{Bool}}$  can be automatically inferred by the Haskell-type inference functionality. So, it needn't specify the component explicitly.

# 7.4.2 A Function That Has the Same Signature as the Identity Function

Let us consider to what extent we can limit the possible implementation of a function that has the signature forall a. ((() -> a) -> a). The unit type is introduced as (), which has the only element (value) (). Since Haskell's name spaces for types and values are separated, we can use the same identifier for a type and value. To avoid confusion, we use  $\star$  for a value. A function that has this signature can be regarded

![](images/cd7128c22c5c3393667960497ab18c1b883b7e0f6a40d2fcf3ac682a0787caef.jpg)  
Fig.7.13 Natural transformation  $\alpha$

as a natural transformation  $\alpha : H^{(0)} \to \mathrm{Id}$ . The type  $(\cdot) -> (\cdot)$  has only one element  $1_{(0)}$ . Thus,  $\alpha$  is a natural isomorphism (Fig. 7.13).

The Yoneda lemma says that such a natural transformation  $\alpha$  corresponds to an element of  $\operatorname{Id}() = ()$ , which is the only one possible. Since  $(:) -> \mathbf{a}$  and  $\mathbf{a}$  are isomorphic, there is exactly one function that has signature for all  $\mathbf{a}$ .  $\mathbf{a} -> \mathbf{a}$ . We conclude that there is exactly one Haskell polymorphic function with signature  $\operatorname{id}:: \mathbf{a} -> \mathbf{a}$ .

# 7.5 Reverse Engineering by the Yoneda Lemma

We will see examples that have origins in an excellent article [2].

# 7.5.1 A Machine That Has a Hidden Parameter

Listing 7.2 unbox1.hs  
```txt
1{-#LANGUAGERankNTypes  $\# -\}$    
2   
3 factory1::a-> (forallb.(a->b）->b)   
4 factory1af  $=$  fa   
5   
6 unbox1::(forallb.(a->b）->b）->a   
7 unbox1t  $=$  t id   
8   
9--testdata   
10 machine1  $=$  factory1 10   
11   
12{-suggested tests
```

```latex
13 machine1  $\langle \mathbf{x}\rangle$ $\mathbf{x}^{*}\mathbf{x})$    
14 unbox1 machine1   
15 -}
```

In Line 3, the signature of factory1 can be interpreted as follows: Type (a -> b) is a functor  $H^a$  with a being fixed. The rightmost b in (a -> b) -> b is an image of b by the identity functor Id. We can explain roughly that type (forall b. (a -> b) -> b) corresponds to the natural transformation  $H^a \to \mathrm{Id}$ . To sum up, given a value of type a, we get a natural transformation parameterized by a. It is kind of a factory of natural transformation.

The function unbox1 in lines 6-7 reveals the secrecy of implementation. Using the Yoneda lemma

$$
\alpha : [ \operatorname {H a s k}, \operatorname {H a s k} ] ((a \rightarrow), \operatorname {I d}) \simeq \operatorname {I d} a,
$$

it seeks the image  $\alpha_{a}(1_{a})$  of  $1_{a}\in H^{a}(a)$

Line 10 gives a value 10 to factory1.

A test can be carried out as follows:

```txt
\*Main> machine1  $\text{工} _ { \mathrm { x } }   \rightarrow$  x\*x)   
100   
\*Main> unbox1 machine1   
10
```

![](images/fda4ba256393d13d7f044b7acd1e70457041adee7897bb79448d1ac6c17d7016.jpg)  
Figure 7.14 explains the naturality.  
Fig.7.14 Machine1

# 7.5.2 A Machine That Hides a List Inside

We consider a machine that hides implementation detail which is actually a list.

Listing 7.3 unbox2.fs  
```txt
1{-#LANGUAGERankNTypes  $\# -$    
2   
3 factory2::[a] -> (forall b . (a->b) -> [b])   
4 factory2 a f  $=$  map f a   
5   
6 unbox2::(forallb . (a->b) -> [b]) -> [a]   
7 unbox2 t  $=$  tid   
8   
9 -- test data   
10 machine2  $=$  factory2 [1,2,3,4]   
11   
12 {- tests   
13 machine2 (\x->x\*x)   
14 unbox2 machine2   
15 -}   
16   
17   
18 factory2':[a] -> (forallb . (a->b) -> [b])   
19 factory2' a f  $=$  reverse $mapf a   
20   
21   
22 rotateL ::forall a . [a] -> [a]   
23 rotateL [] =[]   
24 rotateL (x:xs)  $=$  xs++[x]   
25   
26 factory2',':[a] -> (forallb . (a->b) -> [b])   
27 factory2'，a f  $=$  rotateL $mapf a
```

Let us give an interpretation to Line 3. We interpret the signature of factory2 in Line 3 from a category theoretical point of view. Let us focus on the subexpression forall b. (a->b) -> [b], where a is free. We may regard free variables in aforall expression as a fixed object. Therefore, (a -> b) is a functor  $H^{a}$  with a being fixed, and [b] is an image of the List functor. So, forall b. (a->b) -> [b] is a natural transformation  $H^{a} \rightarrow []$ . Figure 7.15 depicts this situation. Haskell function factory2 is a factory that produces a natural transformation, given a value of type [a].

Function unbox2 reverse-engineers the machine2. It simply uses the Yoneda lemma.

[ Hask, Hask]  $((a \to), \text{List}] \simeq \text{List } a$

See Fig. 7.15.

![](images/e92308a46216fcf7eae9075f374a782ca028511515c33fabcdd019c15535e4d4.jpg)  
Fig.7.15 Machine2

Suggested tests are as follows:

```latex
\*Main> machine2  $\mathbf{\Pi}^{(x - > }$  x\*x)[1,4,9,16]\*Main>unbox2 machine2[1,2,3,4]
```

Function factory2' in lines 18-19 has the same signature with factory2. So, it is also a factory of natural transformations. See how it behaves.

```csv
\*Main> factory2' [1,2,3,4] (\x -> x*x)  
[16,9,4,1]  
\*Main> unbox2 $ factory2' [1,2,3,4]  
[4,3,2,1]
```

The result of reverse engineering is slightly different. Remember this. We add another factory factory2’ in lines 26-27 of natural transformations.

```txt
\*Main> factory2' [1,2,3,4] (\x -> x*x)  
[4,9,16,1]  
\*Main> unbox2 $ factory2' [1,2,3,4]  
[2,3,4,1]
```

The observed phenomena of getting different results from reverse engineering are all related to the signature for all a. [a] -> [a]. Functions of this signature use reverse and rotateL internally, which are both natural transformations

List  $\rightarrow$  List. These internal natural transformations are used in the horizontal composition. As an example, we depict the case of reverse as follows:

$$
\begin{array}{c c c c} a & \quad & 1 _ {a} \longmapsto^ {\alpha_ {a}} [ a _ {1}, \dots , a _ {n} ] \longmapsto^ {\text {r e v e r s e}} [ a _ {n}, a _ {n - 1}, \dots , a _ {1} ] \\ f \Bigg \downarrow & \quad & \Bigg \downarrow f \circ - \quad \Bigg \downarrow \operatorname {m a p} f & \quad \Bigg \downarrow \operatorname {m a p} f \\ b & \quad & f \longmapsto^ {\alpha_ {b}} [ f a _ {1}, \dots , f a _ {n} ] \quad \longmapsto^ {\text {r e v e r s e}} [ f a _ {n}, f a _ {n - 1}, \dots , f a _ {1} ] \end{array}
$$

The two squares are commutative. Therefore, the whole rectangle is also commutative. The commutativity of the square at right can be written in pseudocode as follows:

```txt
reverse . map f == map f . reverse
```

We have the following:

[Hask, Hask]  $((a\to)$ , reverse o List]  $\simeq$  (reverse o List)  $(a)$

This isomorphism tells us that we had to apply the Yoneda lemma with respect to a natural transformation from the functor  $(a\to)$  to functor reverse  $\circ$  List. Writing unbox2' is a trivial task.

The same is true for all functions with signature forall a. [a] -> [a].

# 7.5.3 A Machine That Has a Secret Morphism

Listing 7.4 unbox3.hs  
```txt
1{-#LANGUAGERankNTypes  $\# -\}$    
2   
3 factory3::(c->a) -> (forallb.(a->b) -> (c->b))   
4 factory3 a f = f . a   
5   
6 unbox3::(forallb.(a->b) -> (c->b)) -> (c->a)   
7 unbox3 t = t id   
8   
9 -- test data   
10 machine3  $=$  factory3  $\backslash \mathbf{x}\rightarrow \mathbf{x} + 1$    
11   
12 {- tests   
13 map (machine3  $\backslash \mathbf{x}\rightarrow \mathbf{x}*\mathbf{x})$  [1..10]   
14   
15 map (unbox3 machine3) [1..10]   
16 -}
```

Function factory3 in lines 3-4 is a factory of machines. Sources are morphisms. Products (machines) are natural transformations with signature (forall b . (a -> b) -> (c -> b)), so to say,  $\alpha : (a \rightarrow) \rightarrow (c \rightarrow)$ . See Fig. 7.16. Function unbox3 in lines 6-7 reverse-engineers the machine. The machine in line 10 is a test machine.

![](images/8eaf08e6705ee2d8b74f0538ea11030a86a291c65148ea50e94e2b086507ee9b.jpg)  
Fig.7.16 Machine3

Tests can be carried out as follows:

```latex
\*Main> map (machine3  $\mathbf{\Pi}(\mathbf{x}\rightarrow \mathbf{x}*\mathbf{x}))$  [1..10] [4,9,16,25,36,49,64,81,100,121]   
\*Main> map (unbox3 machine3) [1..10] [2,3,4,5,6,7,8,9,10,11]
```

We can infer that the machine is equipped with a function that adds one to the argument.

# 7.5.4 The Design Pattern with Yoneda

We can abstract a design pattern for reverse engineering machines.

Listing 7.5 unbox.hs  
```haskell
1{-#LANGUAGE RankNTypes  $\# -\}$    
2   
3 data I a  $=$  I a deriving Show   
4 instance Functor I where   
5 fmap f (I a)  $=$  I (f a)   
6   
7{- Defined in GHC.Base   
8 instance Functor  $((->a)$  where   
9 fmap  $f = (.)$  f   
10 -}   
11   
12 factory :: Functor f  $\Rightarrow$  fa -> (forall b . (a -> b) -> fb)   
13 factory a f  $=$  fmap f a   
14   
15 unbox :: (forall b . (a -> b) -> fb) -> fa   
16 unbox t  $=$  t id   
17   
18 -- test data   
19 machine41  $=$  factory (I 10)
```

```haskell
20 machine42 = factory [1,2,3,4]  
21 machine43 = factory (\x -> x + 1)  
22  
23 {- tests  
24 map machine41 [(\x -> x*2), (\x -> x*x), (\x -> x*x*x)]  
25 unbox machine41  
26  
27 machine42 (\x -> x*x)  
28 unbox machine42  
29  
30 map (machine43 (\x -> x*x)) [1..10]  
31 map (unbox machine43) [1..10]  
32 -}
```

Identity functor  $\mathbf{I}$  is introduced in lines 3-5. An instance of Functor  $((\dashv)$  a) is shown in lines 8-9 as an excerpt from a basic library.

A frequently observed pattern is abstracted in lines 12-13, where factory is a factory of natural transformations. The corresponding reverse engineering is defined in lines 15-16.

Lines 19-21 provide with Yoneda machines to test the identity, List, Hom functors.

Tests can be carried out as follows:

```txt
\*Main> map machine41 [(\x -> x*2)，(\x -> x*x)，(\x -> x*x*x)]  
[I 20,I 100,I 1000]  
\*Main> unbox machine41  
I 10  
\*Main> machine42 (\x -> x*x)  
[1,4,9,16]  
\*Main> unbox machine42  
[1,2,3,4]  
\*Main> map (machine43 (\x -> x*x)) [1..10]  
[4,9,16,25,36,49,64,81,100,121]  
\*Main> map (unbox machine43) [1..10]  
[2,3,4,5,6,7,8,9,10,11]
```

# 7.6 Adjoints Preserve Limits

Let  $\mathcal{A}$  be a small category. If we specialize  $X:\mathcal{A}\to \mathbf{Set}$  to  $H^{A^{\prime}}$  in the Yoneda Lemma 7.3, we get the following:

$$
[ \mathcal {A}, \operatorname {S e t} ] (H ^ {A}, H ^ {A ^ {\prime}}) \simeq \mathcal {A} (A ^ {\prime}, A).
$$

The Yoneda Lemma 7.4 for contravariant functors gives, by specializing  $X: \mathcal{A}^{\mathrm{op}} \to \mathbf{Set}$  to  $H_{A'}$ , the following equivalence:

$$
[ \mathcal {A} ^ {\mathrm {o p}}, \mathbf {S e t} ] \left(H _ {A}, H _ {A ^ {\prime}}\right) \simeq \mathcal {A} (A, A ^ {\prime})
$$

These observations lead us to the following theorem.

Theorem 7.5 For any small category  $\mathcal{A}$ , we have the following equivalences:

$$
H ^ {A} \simeq H ^ {A ^ {\prime}} \Leftrightarrow A \simeq A ^ {\prime}
$$

$$
H _ {A} \simeq H _ {A ^ {\prime}} \Leftrightarrow A \simeq A ^ {\prime}.
$$

We show that adjoints preserve limits.

Theorem 7.6 Let functors  $F: \mathcal{X} \to \mathcal{A}$  and  $U: \mathcal{A} \to \mathcal{X}$  be adjoints;  $F \dashv U$ . Namely,

$$
\mathscr {A} (F X, A) \simeq \mathscr {X} (X, U A).
$$

Then,  $U$  preserves limits, and  $F$  preserves colimits.

Proof We begin with the right adjoint  $U$ . Let  $J$  be an index category,  $D: J \to \mathcal{A}$  be a  $J$ -shaped diagram.

For any object  $X$  we have the following isomorphisms:

$$
\begin{array}{l} \mathscr {X} (X, U (\varprojlim D)) \\ \simeq \mathscr {A} (F X, \lim  D) \quad \text {a d j o i n t n e s s} \\ \simeq \lim  \mathcal {A} (F X, D) \quad \text {e x c h a g e o f H o m a n d l i m i t s} \\ \simeq \lim  _ {\text {a d j o i n t n e s s}} \mathcal {X} (X, U \circ D) \\ \simeq \operatorname {C o n e s} (X, U \circ D) \quad \text {l i m i t i n g c o n e s} \\ \simeq \mathscr {X} (X, \varprojlim (U \circ D)) \quad \text {l i m i t i n g c o n e s} \\ \end{array}
$$

Then, we have

$$
\mathcal {X} (-, U (\varprojlim D)) \simeq \mathcal {X} (-, \varprojlim (U \circ D)).
$$

Theorem 7.5 guarantees the following:

$$
U (\varprojlim D) \simeq \varprojlim (U \circ D).
$$

It says that right adjoint functors preserve limits.

Next, we study the left adjoint functor  $F$ .

For any object  $A$ , we have the following isomorphisms:

$$
\begin{array}{l} \mathscr {A} (F (\lim  D), A) \\ \simeq \mathcal {X} (\lim  \check {D}, U A) \quad \text {a d j o i n t n e s s} \\ \simeq \lim  \mathcal {X} (D, U A) \quad \text {e x c h a n g e o f H o m a n d c o l i m i t s} \\ \simeq \varprojlim \mathcal {A} (F \circ D, A) \quad \text {a d j o i n t n e s s} \\ \simeq \operatorname {C o n e s} (F \circ D, A) \quad \text {l i m i t i n g c o c o n e s} \\ \simeq \mathscr {A} (\varinjlim (F \circ D), A) \quad \text {l i m i t i n g c o c o n e s} \\ \end{array}
$$

Then, we have

$$
\mathscr {A} (F (\varinjlim D), -) \simeq \mathscr {A} (\varinjlim (F \circ D), -).
$$

Theorem 7.5 guarantees the following:

$$
F (\varinjlim D) \simeq \varinjlim (F \circ D)
$$

It says that left adjoint functors preserve colimits.

# References

1. Milewski B, Understanding yoneda. https://www.schoolofhaskell.com/user/bartosz/understanding-yoneda  
2. Piponi D (2006) Reverse engineering machine with the yoneda lemma. Weblog entry, A Neighborhood of Infinity. http://blog.sigfpe.com/2006/11/yoneda-lemma.html

# Monoidal Categories and Coherence

8

Monoidal categories allow a binary operation, often called a tensor product, among objects. Monoidal categories have been used in many areas of mathematics. Today, monoidal categories and their impressive pictorial representations are extensively used in research and application areas such as quantum computing [1], topological field theory [2], natural language processing [3], and other emerging areas. Many introductory articles and textbooks on monoidal categories are available today. So, learners have greater choice.

However, most textbooks do not spend enough lines and pages to concretely illustrate naturality every time it matters. The goal of this chapter is twofolds. The first is to introduce the reader to coherence problems with special emphasis on basic handling of functors of bracketed products and naturality of associators and unitors. The second is to provide the reader with lots of illustrating materials to digest basic concepts of functors and natural transformations through coherence problems.

# 8.1 Categories with Tensor Products

We first see a formal definition and then walk through concrete examples. So, please be patient for a moment.

Definition 8.1 A category  $\mathcal{C}$  is called a monoidal category if it is equipped with

- a functor  $\otimes : \mathcal{C} \times \mathcal{C} \to \mathcal{C}$  called the tensor product or the monoidal product,  
- an object  $\mathbb{1} \in \mathrm{Obj}\mathcal{C}$  called the unit object,  
- a family of isomorphisms called the associator

$$
\alpha = \left\{\alpha_ {X, Y, Z}: X \otimes (Y \otimes Z) \rightarrow (X \otimes Y) \otimes Z \mid X, Y, Z \in \operatorname {O b j} (\mathcal {C}) \right\},
$$

- a family of isomorphisms called the left unitor

$$
\lambda = \left\{\lambda_ {X}: \mathbb {1} \otimes X \rightarrow X \mid X \in \operatorname {O b j} (\mathcal {C}) \right\},
$$

and

- a family of isomorphisms called the right unitor

$$
\rho = \left\{\rho_ {X}: X \otimes \mathbb {1} \rightarrow X \mid X \in \operatorname {O b j} (\mathcal {C}) \right\},
$$

satisfying the following conditions:

(i) For all  $X, Y, Z, W \in \mathrm{Obj}(\mathcal{C})$ , the following pentagon diagram commutes:

$$
\begin{array}{c} (X \otimes Y) \otimes (Z \otimes W) \\ \alpha_ {X, Y, Z \otimes W} \\ X \otimes (Y \otimes (Z \otimes W)) \\ 1 _ {X} \otimes \alpha_ {Y, Z, W} \\ X \otimes ((Y \otimes Z) \otimes W) \xrightarrow {\alpha_ {X , Y \otimes Z , W}} (X \otimes (Y \otimes Z)) \otimes W \end{array} \tag {8.1}
$$

This condition is called the pentagon coherence.

(ii) For all  $X, Y \in \mathrm{Obj}(\mathcal{C})$ , the following triangle diagram commutes:

$$
\begin{array}{c} X \otimes (\mathbb {1} \otimes Y) \xrightarrow {\alpha_ {X , \mathbb {1} , Y}} (X \otimes \mathbb {1}) \otimes Y \\ \downarrow \\ 1 _ {X} \otimes \lambda_ {Y} \\ \hline X \otimes Y \end{array} \rho_ {X} \otimes 1 _ {Y} \tag {8.2}
$$

This condition is called the triangle coherence.

(iii) For all triplets of morphisms  $f: X \to X'$ ,  $g: Y \to Y'$ , and  $h: Z \to Z' \in \operatorname{Mor}(\mathcal{C})$ , the following diagram commutes:

$$
\begin{array}{c}X\otimes (Y\otimes Z)\xrightarrow{}_{f\otimes (g\otimes h)}X^{\prime}\otimes (Y^{\prime}\otimes Z^{\prime})\\ \alpha_{X,Y,Z}\Big{\downarrow}\qquad \qquad \qquad \qquad \qquad \qquad \Big{\downarrow}\alpha_{X^{\prime},Y^{\prime},Z^{\prime}}\\ (X\otimes Y)\otimes Z\xrightarrow{(f\otimes g)\otimes h} (X^{\prime}\otimes Y^{\prime})\otimes Z^{\prime} \end{array}
$$

(iv) For all morphisms  $f:X\to X^{\prime}\in \mathrm{Mor}(\mathcal{C})$  , the following diagram commutes:

$$
\begin{array}{c} \mathbb {1} \otimes X \xrightarrow {1 _ {\mathbb {1}} \otimes f} \mathbb {1} \otimes X ^ {\prime} \\ \lambda_ {X} \Bigg \downarrow \\ X \xrightarrow {f} X ^ {\prime} \end{array}
$$

(v) For all morphisms  $f: X \to X' \in \operatorname{Mor}(\mathcal{C})$ , the following diagram commutes:

![](images/86c476a1a7064733e5d9ed8b9a6a99e2e9b4f669c9a6325b0d54d5dc5552e14c.jpg)

A monoidal category is often presented as a six-tuple  $(\mathcal{C},\otimes ,\mathbb{1},\alpha ,\lambda ,\rho)$

Relaxed versions can be defined and often used. However, we will not need those for our purpose.

The functor  $\otimes : \mathcal{C} \times \mathcal{C} \to \mathcal{C}$  is often called a bifunctor. A morphism in  $\mathcal{C} \times \mathcal{C}$  is given by a pair of morphisms  $f: X \to Y$  and  $g: X' \to Y'$ . Morphism  $(f, g)$  in  $\mathcal{C} \times \mathcal{C}$  is sent to a morphism  $\otimes(f, g)$ , which if often written as  $f \otimes g$ .

Let us see the above axioms can be realized in concrete examples.

Example 8.1 The category Set is a monoidal category. The tensor product in this case is the Cartesian product functor  $\times : \mathbf{Set} \times \mathbf{Set} \to \mathbf{Set}$  whose function on objects is defined as

$$
\times : (X, Y) \mapsto X \times Y,
$$

and whose function on morphisms is defined as

$$
\times : (f, g) \mapsto f \times g.
$$

Recall that for  $f: X \to X'$  and  $g: Y \to Y'$

$$
f \times g: X \times Y \rightarrow X ^ {\prime} \times Y ^ {\prime}
$$

$$
(x, y) \mapsto (f (x), g (y)).
$$

Any singleton set plays the role of the unit object. We pick one  $\{*\}$ . The associativity constraint is defined by

$$
\alpha_ {X, Y, Z}: X \times (Y \times Z) \rightarrow (X \times Y) \times Z
$$

$$
(x, (y, z)) \mapsto ((x, y), z)
$$

for all triplets of sets  $X, Y$ , and  $Z$ . Note that each  $\alpha_{X,Y,Z}$  is an isomorphism, in Set, a bijection. The left unitor is defined by

$$
\lambda_ {X}: \{*, \} \times X \rightarrow X
$$

$$
(*, x) \mapsto x.
$$

The right unitor is defined by

$$
\rho_ {X}: X \times \{*, * \} \rightarrow X
$$

$$
(x, *) \mapsto x.
$$

Let us check the five conditions described in Definition 8.1 one by one.

(i) We calculate pointwise or elementwise, which is possible since we are working with sets, the two paths from  $X \otimes (Y \otimes (Z \otimes W))$  to  $((X \otimes Y) \otimes Z) \otimes W$  in the pentagon. Let  $x, y, z$ , and  $w$  be any elements of  $X, Y, Z$ , and  $W$ , respectively. The lower path goes like this.

![](images/1546aa288cec50e48bb3cb286fcf0fc63a0511b5e980afad0aade14dc603d34d.jpg)

The upper path goes like this.

![](images/b143afe47c2498f72120d8f3f9e77712e55bbe258462b28da1c7b8909e095107.jpg)

We see that the two paths yield the same result.

(ii) We calculate pointwise the two paths from  $X \times (\{*\} \times Y)$  to  $X \times Y$  in the triangle. Let  $x$  and  $y$  be any elements of  $X$  and  $Y$ , respectively. The upper path goes as follows:

![](images/007f42020b14a2920a50b4457ebc24e09171ab6d55f80abfd74d23682dbbdaa7.jpg)

The lower one step path goes as follows:

![](images/21b960d0d6de82669b51660b8d4252887fbd2a8382ab54246ee2a8cb637ef6d2.jpg)

The two paths yield the same result, which proves the commutativity of the triangle.

(iii-v) Easy exercises.

Conditions (iii), (iv), and (v) in Definition 8.1 for the associator and unitors say that these collections of isomorphisms yield natural isomorphisms between some functors. It is worthwhile to clearly state this fact since naturality of an associator and unitors plays the central role in the discussion of coherence later.

We need the notion of a finite product of categories. Recall the concept of product categories introduced in Definition 1.5.

Definition 8.2 Let  $\mathcal{C}_1, \mathcal{C}_2, \ldots, \mathcal{C}_n$  be categories. The product of these categories denoted by

$$
\mathcal {C} _ {1} \times \mathcal {C} _ {2} \times \dots \times \mathcal {C} _ {n}
$$

is a category with the following sets of objects and morphisms. The objects are all  $n$ -tuples

$$
\left(X _ {1}, X _ {2}, \dots , X _ {n}\right) \text {o r o f t e n w r i t t e n a s} X _ {1} \times X _ {2} \times \dots X _ {n}
$$

for  $X_{i}\in \mathrm{Obj}(\mathcal{C})$ . The morphisms are all  $n$ -tuples

$$
\left(f _ {1}, f _ {2}, \dots , f _ {n}\right) \text {o r o f t e n w r i t t e n a s} f _ {1} \times f _ {2} \times \dots f _ {n}
$$

for  $f_{i} \in \mathrm{Mor}(\mathcal{C}_{i})$ . Composition of morphisms is performed componentwise. Componentwise functors can be introduced in an obvious way.

Let us begin with the associator  $\alpha$ . Consider a functor

$$
1 _ {\mathcal {C}} \times \otimes : \mathcal {C} \times \underline {{\mathcal {C} \times \mathcal {C}}} \to \mathcal {C} \times \mathcal {C}
$$

$$
(X, Y, Z) \mapsto (X, Y \otimes Z)
$$

and its composition with  $\otimes$

$$
\otimes (1 _ {\mathcal {C}} \times \otimes): \mathcal {C} \times \mathcal {C} \times \mathcal {C} \to \mathcal {C}
$$

$$
(X, Y, Z) \mapsto X \otimes (Y \otimes Z).
$$

Consider another functor

$$
\otimes \times 1 _ {\mathcal {C}}: \underline {{\mathcal {C} \times \mathcal {C}}} \times \mathcal {C} \to \mathcal {C} \times \mathcal {C}
$$

$$
(X, Y, Z) \mapsto (X \otimes Y, Z)
$$

and its composition with  $\otimes$

$$
\begin{array}{l} \otimes (1 _ {\mathcal {C}} \times \otimes): \mathcal {C} \times \mathcal {C} \times \mathcal {C} \to \mathcal {C} \\ (X, Y, Z) \mapsto (X \otimes Y) \otimes Z. \\ \end{array}
$$

Now, we can consider a natural transformation between the two functors

$$
\alpha : \otimes (1 _ {\mathcal {C}} \times \otimes) \rightarrow \otimes (\otimes \times 1 _ {\mathcal {C}})
$$

$$
\alpha_ {X, Y, Z}: X \otimes (Y \otimes Z) \to (X \otimes Y) \otimes Z,
$$

which is required to be an isomorphism by the axiom in Definition 8.1. We often use more intuitive notation, where functors are presented with place holders. For example,  $\alpha$  can be written as

$$
\alpha : - \otimes (- \otimes -) \to (- \otimes -) \otimes -.
$$

The following diagram may help understand the situation. The trapezoid at right commutes for all triplets  $(f, g, h)$ .

$$
\mathcal {C} \times \mathcal {C} \times \mathcal {C} \xrightarrow {\begin{array}{c} - \otimes (- \otimes -) \\ \Downarrow \alpha \\ (- \otimes -) \otimes - \end{array} } \mathcal {C}
$$

$$
\begin{array}{c} (X, Y, Z) \xrightarrow {(- \otimes -) \otimes -} (X \otimes Y) \otimes Z \\ \left( \begin{array}{c} - \otimes (- \otimes -) \\ f, g, h \end{array} \right) \xrightarrow {- \otimes (- \otimes -)} \begin{array}{c} X \otimes (Y \otimes Z) \\ f \otimes (g \otimes h) \\ X ^ {\prime} \otimes (Y ^ {\prime} \otimes Z ^ {\prime}) \\ \alpha_ {X ^ {\prime}, Y ^ {\prime}, Z ^ {\prime}} \end{array} \begin{array}{c} (\alpha_ {X, Y, Z} \\ \bigcirc \\ (f \otimes g) \otimes h \\ (X ^ {\prime}, Y ^ {\prime}, Z ^ {\prime}) \xrightarrow {(- \otimes -) \otimes -} (X ^ {\prime} \otimes Y ^ {\prime}) \otimes Z ^ {\prime} \end{array}
$$

The natural transformation  $\lambda$  relates the functor  $\mathbb{1} \otimes -$  and the identity functor  $1_{\mathcal{C}}$  just denoted by  $-$ . See the following diagram. The trapezoid at right commutes for all  $f \in \operatorname{Mor}(\mathcal{C})$ .

![](images/8db5c78ed5c7cd4cf9120325ecc208e791d5226e7f9cf785a2a38220b1ff3e0b.jpg)

The natural transformation  $\rho$  relates the functor  $-\otimes \mathbb{1}$  and the identity functor  $-$ . See the following diagram. The trapezoid at right commutes for all  $f \in \operatorname{Mor}(\mathcal{C})$ .

![](images/048e207f1fed82601568d136abfe48fa430f3b42a846c17e266ea117ebf591c0.jpg)

Example 8.2 The category Set in Example 8.1 can be treated without referring to elements. We will work within a category with finite products and a terminal object. So, the following argument applies to various categories other than Set.

We first show that  $X_{1} \times (X_{2} \times X_{3})$  is isomorphic to  $X_{1} \times X_{2} \times X_{3}$ . Let  $Z$  be any object with three morphisms as follows.

![](images/ca71a6c965494567174ed2c66882d6d7d0ec075b09513b885ac5a4662626c029.jpg)

Then, we have the following diagram:

![](images/6bd142e967c3706ab2aeb1025f0cc79a7fccc0215cbc4fcabae803909fd59c17.jpg)

By the universality of  $X_{1} \times X_{2}$ , a unique morphism  $\alpha$  makes the adjacent triangles commute. Then, by the universality of  $(X_{1} \times X_{2}) \times X_{3}$ , a unique morphism  $\beta$  makes the two triangles in the following diagram commute:

![](images/0a15bb248c88904a5884793d619812a06bd66c46e31409070638e6789372d460.jpg)

This shows that the morphism  $\beta$  is a unique mediating morphism from the span  $(Z, f_{1}, f_{2}, f_{3})$  to the universal span with apex  $(X_{1} \times X_{2}) \times X_{3}$  and projections

$$
p _ {1} = \pi_ {1 2, 1} \circ \pi_ {(1 2) 3, 1 2}: (X _ {1} \times X _ {2}) \times X _ {3} \rightarrow X _ {1},
$$

$$
p _ {2} = \pi_ {1 2, 2} \circ \pi_ {(1 2) 3, 1 2}: (X _ {1} \times X _ {2}) \times X _ {3} \rightarrow X _ {2}, \text {a n d}
$$

$$
p _ {3} = \pi_ {(1 2) 3, 3}: (X _ {1} \times X _ {2}) \times X _ {3} \rightarrow X _ {3}.
$$

Likewise, we can show that  $(X_{1} \times (X_{2} \times X_{3}), q_{1}, q_{2}, q_{3})$  is a universal span, where

$$
q _ {1} = \pi_ {1 (2 3), 1}: X _ {1} \times (X _ {2} \times X _ {3}) \rightarrow X _ {1},
$$

$$
q _ {2} = \pi_ {2 3, 2} \circ \pi_ {1 (2 3), 2 3}: X _ {1} \times (X _ {2} \times X _ {3}) \rightarrow X _ {2}, \text {a n d}
$$

$$
q _ {3} = \pi_ {2 3, 3} \circ \pi_ {1 (2 3), 2 3}: X _ {1} \times (X _ {2} \times X _ {3}) \to X _ {3}.
$$

Since universal objects are isomorphic, there is a unique isomorphism

$$
\alpha_ {X _ {1}, X _ {2}, X _ {3}}: X _ {1} \times (X _ {2} \times X _ {3}) \rightarrow (X _ {1} \times X _ {2}) \times X _ {3}.
$$

We are going to show that the collection  $\left\{\alpha_{X_1,X_2,X_3}\mid X_1,X_2,X_3\in \mathrm{Obj}(\mathcal{C})\right\}$  forms a natural transformation

$$
\alpha : - \times (- \times -) \rightarrow (- \times -) \times -.
$$

For any morphisms  $f_{i}:X_{i}\to Y_{i}$  for  $(i = 1,2,3)$ , we want to show the trapezoid at left is commutative in the following diagram:

![](images/c8c6d388678c9c78314e99d28fc005301dc647d873c3695f2640a3fb18d8fd0c.jpg)

where unlabeled arrows are obvious projections depending on  $i$ 's. The outermost and innermost triangles commute by the definition of  $\alpha$ 's. The quadrilaterals formed by projections and  $f_{i}$ 's commute. See below:

![](images/1d4957955a5da3a5c6a46bad4206f0b4b9df7d3f1721b829220f740954e03bf6.jpg)

![](images/12e641c19623168ae35e06a74848333bb8d1a375bbd4a2eb59579f3d8b1aeabb.jpg)

Combining all these commutative pieces, we see the following two paths from  $\bigcirc$  to  $\triangle$  coincide for all  $i$ 's:

![](images/100c04f567c2a6297414e9f70f09f83587cd472b25b1bffe13e068084154673c.jpg)

Now, we can consider spans to  $\{Y_1,Y_2,Y_3\}$  as follows:

![](images/c51a1011a36337a58b3ec584b81e3145b311fc0a5f0b358c40289c3ec375457b.jpg)

In the above diagram, from two apexes  $X_{1} \times (X_{2} \times X_{3})$  and  $(Y_{1} \times Y_{2}) \times Y_{3}$  we find two spans to  $\{Y_{1}, Y_{2}, Y_{3}\}$ . The object  $(Y_{1} \times Y_{2}) \times Y_{3}$  with its projections is a universal span. So, the two mediating morphisms appearing in the diamond must be identical. We conclude that  $\alpha$  is a natural transformation, in our case especially a natural isomorphism.

We have to show that the two paths from  $X \times (Y \times (Z \times W))$  to  $((X \times Y) \times Z) \times W$  in the pentagon diagram below coincide.

![](images/f4de61483b3e33628f330d05540b674934e03512c9675860d00b9f2ca3b3ea2f.jpg)

Let us consider spans to  $\{X, Y, Z, W\}$  from each vertex of the pentagon. Take two vertices at left, for example, to get the following morphism between the spans:

![](images/04b60b7d7ae2e48e1c3e2edab60726df8d990f7a2c11f14bc54f1164eeeaaf5f.jpg)

where unlabeled arrows are obvious projections. The morphism  $1_{X} \times \alpha_{Y,Z,W}$  is a unique mediating morphism between the two spans. Likewise, all the morphisms appearing in the pentagon diagram above are mediating morphisms between universal

spans to  $\{X, Y, Z, W\}$ . Any compositions of the morphisms are also a mediating morphism. Then, we use the universality of  $((X \times Y) \times Z) \times W$ . A mediating morphism from  $X \times (Y \times (Z \times W))$  to  $((X \times Y) \times Z) \times W$  must be unique. So, the two paths must be identical. We conclude that the natural isomorphism  $\alpha$  makes the pentagon diagram commute.

Let  $T$  be a terminal object. Any one will do. We will soon see how terminal objects do great jobs. We define  $\lambda_{X}: T \times X \to X$  and  $\rho_{X}: X \times T \to X$  as projections. We first show that  $\lambda_{X}$  is an isomorphism.

![](images/bfa38e0544db2513928f9e75331be68aa96fe5ba0bc0f9cce3a6f2bf5ad1b299.jpg)

The symbol “!” in this diagram denotes the unique morphisms to the terminal object. The object  $T \times X$  with its projections is a universal span to  $\{T, X\}$ . Thus, the mediating morphism  $m$  is unique and  $\lambda_X \circ m = 1_X$ . Notice also that  $X$  with projections! and  $1_X$  is another universal span to  $\{T, X\}$ . In fact, let  $f: Z \to X$  be any morphism. We have the diagram below:

![](images/26c34c85f3244a7755ab8ff9d4f6964ffa5255ddff4242887832e75f2d0c8a32.jpg)

where the two triangles obviously commute. This means  $(X,!, 1_X)$  is a universal span. Let us replace  $Z$  with  $T \times X$ . We have the following:

![](images/01cd3e1ef0575abf5fd6d9a2c75846ec99e7cdd6a6737d1e7760717a85630216.jpg)

(8.4)

where  $\lambda_{X}$  plays the role of a mediating morphism. Connecting two diagrams (8.3) and (8.4), we have the following:

![](images/fba740e58a1da1fa659d6d7b242c774b2289de34880f804552b04a3d53cb3edb.jpg)

Since  $T \times X$  with its projections is a universal span to  $\{T, X\}$ , we have  $m \circ \lambda_{X} = 1_{T \times X}$  in addition to  $\lambda_{X} \circ m = 1_{X}$ . Thus, the morphism  $\lambda_{X}$  is an isomorphism.

Likewise,  $\rho_{X}$  is shown to be an isomorphism.

Next, we see if the triangle coherence holds. Let  $Z$  be any object with morphisms to  $X$  and  $Y$ .

![](images/df081e83c4f7ac5386205c1fe9732112fc4130aecdcf8019fb52ceb7ba3a69cc.jpg)

We see that  $X \times Y$  with its projections is not only a universal span to  $\{X, Y\}$  but also a universal span from  $X \times Y$  to  $\{X, T, Y\}$ . The mediator  $m$  is shared by both universal spans. Now, consider the following diagram:

![](images/eeb07768c21b01b9553ca7c2164e958619ed1762a20b3a7d438c7bb5329bfb56.jpg)

We find a span from  $X \times (T \times Y)$  to  $\{X, T, Y\}$ . Two mediating morphisms to a universal span  $(X \times Y, \{X, T, Y\})$  must be identical. Thus, the triangle coherence holds.

# 8.2 Coherence—Part One

We often treat tensor products in monoidal categories as though they are associative. In general they are only associative up to isomorphisms. Coherence prevents such an attitude from causing troubles.

The pentagon diagram (8.1) is the simplest instance of coherence. We will show that it is powerful enough to derive all other instances of coherence with the help of the triangle diagram (8.2). The commutativity of the pentagon diagram says that the two ways of using associators to get to the same object yield the same morphism.

The goal of this section is twofold.

- To streamline the discussion on coherence we add a working lemma that deals with two more instances of unitor coherence.  
- The lemma and its proof is designed to provide the reader with lots of concrete examples of functoriality and naturality.

The following lemma appeared as one of the exercise problems in [4, p. 165].

Lemma 8.1 Let  $\mathcal{C}$  be a monoidal category. For all  $X, Y, Z$ , and  $W \in \mathrm{Obj}(\mathcal{C})$ , the following two triangles commute:

$$
\begin{array}{c} \mathbb {1} \otimes (Z \otimes W) \xrightarrow {\alpha_ {\mathbb {1} , Z , W}} (\mathbb {1} \otimes Z) \otimes W \\ \lambda_ {Z \otimes W} \quad \downarrow \quad \lambda_ {Z} \otimes 1 _ {W} \\ Z \otimes W \end{array} \tag {8.5}
$$

$$
\begin{array}{c} X \otimes (Y \otimes \mathbb {1}) \xrightarrow {\alpha_ {X , Y , \mathbb {1}}} (X \otimes Y) \otimes \mathbb {1} \\ 1 _ {X} \otimes \rho_ {Y} \quad \downarrow \quad \rho_ {X} \otimes Y \\ X \otimes Y \end{array} \tag {8.6}
$$

Proof (First half) We prove the triangle (8.5) commutes.

If we substitute  $X$  and  $Y$  by 1 in the pentagon diagram adding two instances ① and ③ of the unitor coherence triangle, we obtain the following diagram:

![](images/8b165e250fcd45d18e7facc2ce55bdf9e8f39c833000a9177cd8c161df0fa87c.jpg)

where component subscripts of associators, unitors, and identities are omitted for readability.

We will show triangles ①, ③, and quadrilaterals ②, ④ all commute. Then, using the pentagon coherence, we will show the triangle ⑤ commutes, which implies then the triangle (8.5) commutes.

We can confirm that the triangle ① is a true instance of the unitor coherence as follows:

$$
\begin{array}{c} \mathbb {1} \otimes (\mathbb {1} \otimes (Z \otimes W)) \xrightarrow [ 1 _ {\mathbb {1}} \otimes \lambda_ {Z \otimes W} ]{\alpha_ {1 , 1 , Z \otimes W}} (\mathbb {1} \otimes \mathbb {1}) \otimes (Z \otimes W) \\ \mathbb {1} \otimes (Z \otimes W) \end{array}
$$

The quadrilateral ② can be seen as a naturality diagram for the natural transformation between the two functors

$$
\alpha_ {-, Z, W}: - \otimes (Z \otimes W) \rightarrow (- \otimes Z) \otimes W
$$

at the morphism  $\rho_{\mathbb{1}}: \mathbb{1} \otimes \mathbb{1} \to \mathbb{1}$  as follows:

$$
\begin{array}{c} \mathbb {1} \otimes \mathbb {1} \xrightarrow [ ]{(- \otimes Z) \otimes W} ((\mathbb {1} \otimes \mathbb {1}) \otimes Z) \otimes W \\ \rho_ {\mathbb {1}} \left| \begin{array}{c} - \otimes (Z \otimes W) \\ \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad (\mathbb {1} \times \mathbb {1}) \otimes (Z \otimes W) \\ \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad (\rho_ {\mathbb {1}}) \otimes 1 _ {Z}) \otimes 1 _ {W} \\ - \otimes (Z \otimes W) \\ \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \alpha_ {\mathbb {1}, Z, W} \\ | & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\ & | \\
$$

The trapezoid at right is the quadrilateral ②.

The triangle ③ is the image of an instance of the unitor coherence

$$
\begin{array}{c} (\mathbb {1} \otimes \mathbb {1}) \otimes Z \xleftarrow {\alpha_ {1 , 1 , Z}} \mathbb {1} \otimes (\mathbb {1} \otimes Z) \\ \rho_ {1} \otimes 1 _ {Z} \xrightarrow {\circ} 1 _ {1} \otimes \lambda_ {Z} \\ \mathbb {1} \otimes Z \end{array}
$$

by the functor  $-\otimes W$ . Therefore, the triangle ③ commutes.

The quadrilateral ④ can be seen as a naturality of

$$
\alpha_ {1, -, W}: \mathbb {1} \otimes (- \otimes W) \rightarrow (\mathbb {1} \otimes -) \otimes W
$$

at the morphism  $\lambda_Z: \mathbb{1} \otimes Z \to Z$  as follows:

![](images/86d70b00fd878cf5c7a5821dc444a4e81d1a6e5ec68ad519a1ef4dd72d2cf3b6.jpg)

The trapezoid at right is the quadrilateral ④.

Now, we proceed to see if the triangle ⑤ commutes. Using commutativity we have seen so far, we can transform the path from left to right in the following sequence. Notice that the pentagon coherence is used in the step from the third to fourth.

![](images/2baeb0aec890bc5318c3b25951e7dd3fa03f1dab320c0e8fb75f67180622848f.jpg)

Thus, we have the following.

![](images/40f635a89ae37ebf9847a96cef9dbf4dd98800e54e2905e1ab257a660ba52eea.jpg)

The two paths share the same arrow  $\alpha_{\mathbb{1},Z,W}$  at their ends. Since it is an isomorphism, the triangle ⑤ commutes.

We have come halfway. Let us study the following diagram:

![](images/55798c829114655417bf2ef3bf6ca6ab0fccbfa3186697dea748eb72de95e1a3.jpg)

The outermost triangle is ⑤, which we have just proved commutative. The commutativity of the inner triangle is our goal.

We show that the three quadrilaterals surrounding the inner triangle are all commutative. Let us begin with the upper quadrilateral ⑥.

![](images/067ce5057edaa890569c3a26f911a7f66cf93fe8d994cf25d1d54e5616e8e999.jpg)

By the naturality of  $\lambda$  at the morphism  $\lambda_{Z\otimes W}:\mathbb{1}\otimes (Z\otimes W)\to Z\otimes W$ , we see the trapezoid at right in the above diagram, namely, the quadrilateral ⑥ commute.

Next, we see the quadrilateral ⑦.

![](images/524d018c4ff7a1db83a4bc27e7b14fbc8678dc865739bcb385ef69619b4f455f.jpg)

By the naturality of  $\lambda$  at the morphism  $\lambda_Z \otimes 1_W : (\mathbb{1} \otimes Z) \otimes W \to Z \otimes W$ , we see the trapezoid at right in the above diagram, namely, the quadrilateral ⑦ commute.

Finally, we see the quadrilateral ⑧.

![](images/8c659df14901d5b036a05d9f40f0ea82b556c021534522bfadbd209c121710de.jpg)

By the naturality of  $\lambda$  at the morphism  $\alpha_{\mathbb{1},Z,W}:\mathbb{1}\otimes (Z\otimes W)\to (\mathbb{1}\otimes Z)\otimes W$ , we see the trapezoid at right in the above diagram, namely, the quadrilateral ⑧ commute.

Using the commutative quadrilaterals ⑥, ⑦, ⑧, and the large triangle, we can transform the first path to the last as follows. Trace it from upper left to lower right.

![](images/cbe118fd6b2e4a89f046f9eff36c506849eedb713c211209c99390046864e46e.jpg)

The first path and the last one are identical morphisms. They share one arrow of isomorphism, which can be canceled to obtain the commutativity of the inner triangle.

This establishes the commutativity of (8.5).

Proof (Second half) We prove the triangle (8.6) commutes. Since most arguments go in the same way, we only show the outline.

If we substitute  $Z$  and  $W$  in the pentagon diagram by 1 adding two instances of the unitor coherence triangle, we obtain the following diagram:

![](images/2a3c5e104e2a6621a125769ff6514eceb01af8d049020a59990cbe042f69143c.jpg)

The quadrilateral ① commutes by the naturality of  $\alpha$ . To be more specific, the naturality of

$$
\alpha_ {X, Y, -}: X \otimes (Y \otimes -) \rightarrow (X \otimes Y) \otimes -
$$

at the morphism  $\lambda_{1}:\mathbb{1}\otimes \mathbb{1}\to \mathbb{1}$

The triangle ② is an instance of the unitor coherence.

The quadrilateral ④ commutes by the naturality of  $\alpha$ . To be more specific, the naturality of

$$
\alpha_ {X, -, \mathbb {1}}: X \otimes (- \otimes \mathbb {1}) \to (X \otimes -) \otimes \mathbb {1}
$$

at the morphism  $\rho_Y:Y\otimes \mathbb{1}\to Y$

Applying the functor  $X \otimes -$  to an instance of the unitor coherence, we get the triangle ⑤.

So, ①, ②, ④, and ⑤ all commute leaving ③ unknown at present.

We can transform the first path to the last as follows. Read from left to right.

![](images/4f05f060eea272ebd93fb472c0c0107874e8269a16a24ebdab971a8d5f738b35.jpg)

We used the pentagon coherence at the last step.

The first path and the last one share two arrows, which are isomorphisms. By canceling these out, we conclude the triangle ③ is commutative.

Let us study the following diagram. We have just seen that the outer triangle is commutative.

![](images/0bc643401140dfc147b734fa98f8f2304d6838afb28b53139f89cd42ce6c03a3.jpg)

The quadrilateral ⑥ commutes by the naturality of  $\rho : -\otimes \mathbb{1} \to -$  at the morphism  $\alpha_{X,Y,\mathbb{1}}: X \otimes (Y \otimes \mathbb{1}) \to (X \otimes Y) \otimes \mathbb{1}$ .

The quadrilateral ⑦ commutes by the naturality of  $\rho : -\otimes \mathbb{1} \to -$  at the morphism  $\rho_{X\otimes Y}$ .

The quadrilateral ⑧ commutes by the naturality of  $\rho : -\otimes \mathbb{1} \to -$  at the morphism  $1_X \otimes \rho_Y$ .

Using the commutative quadrilaterals ⑥, ⑦, ⑧, and the large triangle, we can transform the first path to the last as follows:

![](images/2f5022d120ed4134d4f213e0fb516907422c38547153a74ed23b362a22ce8a57.jpg)

Since the first path and the last one share one isomorphism arrow, we see the inner triangle commutes.

# 8.3 Monoidal Functors

Monoidal categories have more structures than vanilla categories. So, we would like functors between monoidal categories to preserve these extra structures in some way.

Definition 8.3 A strict monoidal functor from a monoidal category  $(\mathcal{C},\otimes ,\mathbb{1},\alpha ,$ $\lambda ,\rho)$  to a monoidal category  $(\mathcal{C}^{\prime},\otimes^{\prime},\mathbb{1}^{\prime},\alpha^{\prime},\lambda^{\prime},\rho^{\prime})$  is a functor  $T:\mathcal{C}\to \mathcal{C}'$  such that, for any  $X,Y,Z\in \mathrm{Obj}(\mathcal{C})$  and  $f,g\in \mathrm{Mor}(\mathcal{C})$

$$
T (X \otimes Y) = T X \otimes T Y, \quad T (f \otimes) = T f \otimes T g, \quad T \mathbb {1} = \mathbb {1} ^ {\prime},
$$

$$
T \alpha_ {X, Y, Z} = \alpha_ {T X, T Y, T Z} ^ {\prime}, \qquad T \lambda_ {X} = \lambda_ {T X} ^ {\prime}, \qquad T \rho_ {X} = \rho_ {T X} ^ {\prime}.
$$

Strict monoidal functors play the central role in the next section. However, many working examples show strictness is over requirement. We see one such an example below.

Example 8.3 Let  $\Bbbk$  be a field. Let us consider the category  $\mathrm{Vect}_{\Bbbk}$  of finite dimensional  $\Bbbk$ -vector spaces. We know the usual tensor product  $\otimes_{\Bbbk}$ . With some elaboration based on the basis or purely depending on universality, we can write down a reasonable associator and unitors that satisfy the coherence conditions. But, let us believe all of these are rigorously done.

Let  $U$  be the forgetful functor from  $(\mathrm{Vect}_{\mathbb{C}},\otimes_{\mathbb{C}},\ldots)$  to  $(\mathrm{Vect}_{\mathbb{R}},\otimes_{\mathbb{R}},\ldots)$ , where associators and unitors are omitted in the presentation. "Forgetful" means, in this case, is to regard every one-dimensional complex vector space as a two-dimensional real vector space with basis 1 and  $\sqrt{-1}$ . Let  $V_{1}$  and  $V_{2}$  be any complex vector spaces of dimension  $n_1$  and  $n_2$ , respectively. While  $\dim_{\mathbb{C}}V_1\otimes_{\mathbb{C}}V_2 = n_1\times n_2$  and  $\dim_{\mathbb{R}}U(V_1\otimes_{\mathbb{C}}V_2) = 2\times n_1\times n_2$ , we see  $\dim_{\mathbb{R}}U(V_1)\otimes_{\mathbb{R}}U(V_2) = 4\times n_1\times n_2$ . So,  $U(V_{1}\otimes_{\mathbb{C}}V_{2})$  and  $U(V_{1})\otimes_{\mathbb{R}}U(V_{2})$  are neither equal nor isomorphic.

Since this kind of forgetful functors play important roles in many places, we have to relax equality to isomorphicity or naturality in various ways.

# 8.4 Coherence—Part Two

In the second half of the discussion of coherence, we construct some higher order structures out of a monoidal category. This kind of activity is found everywhere in mathematics but especially often in category theory.

We first introduce a category of binary words.

Definition 8.4 We introduce the notion of binary words defined recursively as follows:

- The empty word  $e$  is a binary word of length 0.  
- The symbol  $a$  is a binary word of length 1.  
- If  $\nu$  and  $w$  are binary words of length  $m$  and  $n$ , respectively, then  $(\nu) \otimes (w)$  is a binary word of length  $m + n$ .

The objects of the category  $\mathcal{W}$  are all binary words. For any pair of binary words  $\nu$  and  $w$  of the same length, there is exactly one morphism  $\nu \rightarrow w$ . Thus,  $\mathcal{W}$  is a preorder with every morphism is invertible. The category  $\mathcal{W}$  is a strict monoidal category. The unit object is  $e$ . The associator and unitors are uniquely determined since  $\mathcal{W}$  is a preorder.

Remark 8.1 A preorder is a category in which, for any two objects  $x$  and  $y$ , there is at most one morphism from  $x$  to  $y$ . The preorderedness makes all the diagrams in  $\mathcal{W}$  commute. Consider any diagram including an object  $\bullet$  below:

![](images/6f23626492b17ab304b9723d3b25d9b1a16ff8983fc820781b099d26e163073d.jpg)

Since all the morphisms in the category  $\mathcal{W}$  are invertible, we do not care the directions in the diagram. The diagram above can be seen as a directed path from  $\bullet$  to  $\bullet$  and  $1_{\bullet}$  is the only morphism allowed. Thus, the path is the identity morphism of the object  $\bullet$ , which means that the diagram commutes.

Example 8.4 Let  $\nu_{1},\dots,\nu_{5},\nu_{2}^{\prime},\nu_{4}^{\prime}\in \mathrm{Obj}(\mathcal{W})$  as follows:

$$
v _ {1} = a \otimes (a \otimes (a \otimes a))
$$

$$
v _ {2} = (a \otimes a) \otimes (a \otimes a)
$$

$$
v _ {3} = ((a \otimes a) \otimes a) \otimes a
$$

$$
\nu_ {4} = a \otimes ((a \otimes a) \otimes a)
$$

$$
v _ {5} = (a \otimes (a \otimes a)) \otimes a
$$

$$
v _ {2} ^ {\prime} = (a \otimes e) \otimes (e \otimes a)
$$

$$
\nu_ {4} ^ {\prime} = e \otimes ((a \otimes a) \otimes a)
$$

The words  $\nu_{1}, \ldots, \nu_{5}$  all have length 4. The length of the word  $\nu_{2}'$  is 2. The word  $\nu_{4}'$  has length 3. Recall that the length of a binary word is the number of  $a$ 's in the word. Pictorial representations of  $\nu_{1}, \nu_{2}, \ldots$ , and  $\nu_{5}$  are shown below:

![](images/3f8132e914ef84fc06865068a0d26e35fd84e220b6ed1df0c55ba9896514b211.jpg)

![](images/fde669f7d4621daf33db5025c88bea521c0c2f70e88ff48d1b37af9b98d2df88.jpg)

Notice that these five binary trees correspond to vertices in the pentagon diagram (8.1). We will deal with this kind of binary trees with Haskell code later.

Coherence is compactly formulated in the following theorem.

Theorem 8.1 For any monoidal category  $\mathcal{C}$  and  $X\in \mathrm{Obj}(\mathcal{C})$ , there is a unique strict monoidal functor  $\mathcal{W}\to \mathcal{C}$  with  $a\mapsto X$

If there exists a strict monoidal functor as the theorem claims, the function on objects must send each binary word  $w \in \mathrm{Obj}(\mathcal{W})$  to the corresponding object  $w_{X} \in \mathrm{Obj}(\mathcal{C})$  by replacing every occurrence of  $a$  in  $w$  with  $X$ , and every occurrence of  $e$  with  $\mathbb{1}$ . Let  $\nu$  and  $w$  be two binary words of the same length. There can be several paths consisting of composite morphisms from  $\nu$  to  $w$ , which must be all identical in a preorder such as  $\mathcal{W}$ . The existence of a strict monoidal functor means that all functor images of paths connecting one object to another must commute. In other words, we are facing a problem of well-definedness.

Before diving into the proof, let us play with Haskell code.

Listing 8.1 BinaryWords.vs  
```txt
1 data Tree a = Pure a | Node (Tree a) (Tree a) deriving Eq  
2  
3 instance Show a => Show (Tree a) where  
4 show (Pure a)  
5 = show a  
6 show (Node (Pure a) (Pure b))  
7 = show a ++ ". ." ++ show b  
8 show (Node (Pure a) t)  
9 = show a ++ ". (" ++ show t ++ ")""  
10 show (Node t (Pure a))  
11 = "(" + + show t ++ )." ++ show a  
12 show (Node t1 t2)  
13 = "(" + + show t1 ++ ).(" + + show t2 + + ")")  
14  
15  
16 data BWord = A | E deriving Eq  
17  
18 instance Show BWord where  
19 show A = "a"  
20 show E = "e"  
21  
22 -- test data  
23 v1 = Node (Pure A) (Node (Pure A) (Node (Pure A) (Pure A)))  
24 v2 = Node (Node (Pure A) (Pure A)) (Node (Pure A) (Pure A))  
25 v3 = Node (Node (Node (Pure A) (Pure A)) (Pure A)) (Pure A)  
26 v4 = Node (Pure A) (Node (Node (Pure A) (Pure A)) (Pure A))  
27 v5 = Node (Node (Pure A) (Node (Pure A) (Pure A))) (Pure A)  
28 v2' = Node (Node (Pure A) (Pure E)) (Node (Pure E) (Pure A))  
29 v4' = Node (Pure E) (Node (Node (Pure A) (Pure A)) (Pure A))  
30  
31 -- associator  
32 alpha :: Tree a -> Tree a  
33 alpha (Pure a) = Pure a  
34 alpha (Node t1 (Node t2 t3)) = Node (Node t1 t2) t3  
35 alpha x = x
```

```haskell
36
37 -- utilities
38 -- generates right heavy trees
39 rgenerate :: [a] -> Tree a
40 rgenerate [x] = Pure x
41 rgenerate (x:xs) = Node (Pure x) (rgenerate xs)
42
43 -- generates left heavy trees
44 lgenerate :: [a] -> Tree a
45 lgenerate = iter . reverse
46 where
47 iter [x] = Pure x
48 iter (x:xs) = Node (iter xs) (Pure x)
49
50 -- repeatedly apply alpha at the top node
51 --util it sees Pure at right
52 alpha' :: Eq a => Tree a -> Tree a
53 alpha' t@(Node t1 (Pure x)) = t
54 alpha' t@(Node t1 t2) = alpha' (alpha t)
55
56 --transforms to the canonical tree
57 ialpha :: Eq a => Tree a -> Tree a
58 ialpha (Pure x) = Pure x
59 ialpha (Node t1 (Pure x)) = Node (ialpha t1) (Pure x)
60 ialpha t = ialpha (alpha' t)
61
62 {-
63 ghci> map (lgenerate [1..5] ==) $ map ialpha $ mkwords [1..5]
64 [True, True, True, True, True, True, True, True, True, True, True, True, True, True, True]
65 }
```

```txt
89   
90 {-   
91 ghci> split [1..5]   
92 [(1],[2,3,4,5]，([1,2],[3,4,5])，([1,2,3],[4,5]) 1   
93 -}   
94   
95 mkwords :: [a] -> [Tree a]   
96 mkwords [x] = [Pure x]   
97 mkwords xs =   
98 [Node t1 t2 |   
99 (x1,x2)<- split xs,t1<- mkwords x1,t2<- mkwords x2]
```

Line 1 defines a binary tree structure. Leaf nodes are created by the Pure constructor. Lines 3-13 define a String representation for our binary trees, where the Tree constructor is presented by an infix operator dot instead of  $\otimes$  and the branching structure by parentheses.

Line 16 defines an alphabet, the set of symbols, for the binary words, the symbols “e” and “a” are defined as the value constructors E and A, respectively. Lines 18-20 define a String representation for these symbols.

Lines 23-29 define test data that appeared in Example 8.4.

Lines 32-35 define the associator  $\alpha$ . It can be used as follows:

```txt
ghci> v1  
a.(a.(a.a))  
ghci> alpha v1  
(a.a).(a.a)
```

We can present this more pictorially.

![](images/069c4c24fe1d98ab9c9c1123324b01cdc8fd5a38e552d4c18dc9b852a670fef7.jpg)

Lines 39-48 define utility functions rgenerate and lgenerate. The former generates a most right heavy tree and the latter most left. Our Tree type is polymorphic. So, we can use it with various types, for example, the Integer type as follows:

```txt
ghci> rgenerate [1..5]  
1.(2.(3.(4.5))）  
ghci> lgenerate [1..5]  
((1.2).3).4).5
```

Let us give a pictorial representation.

![](images/32b353cabb84283d50333729e4966ebd234a060598abfecb48258b6408ee1465.jpg)

![](images/c791b0447bc8dbc03308805d2d8cfa2fabd30cfff5b3eda9daa865aa1178b06d.jpg)

Lines 52-54 define the alpha' function that applies the alpha function repeatedly at the top level node to finally obtain a tree whose left branch is Pure.

Lines 57-60 define the ialpha function that recursively downward making all the right branches Pure. Thus, ialpha transforms any binary trees to its canonical tree, that is, the most left heavy one.

ghci> rgenerate [1..5]

1.(2.(3.(4.5)))

ghci> ialpha $ rgenerate [1..5]

((1.2).3).4).5

In some cases, repeated application of  $\alpha$  at the top node is enough to obtain the canonical tree. For example, see below:

ghci> take 4 $ iterate alpha $ rgenerate [1..5]

[1.(2.(3.(4.5)）)，(1.2).(3.(4.5))，((1.2).3).(4.5)，((1.2).3).4).5]

Let us give a pictorial representation.

![](images/67a7d73d90d4ae10b06e3618d50ef278604c889d089c58275a5bf1b3074629a4.jpg)

![](images/f585f9f8c1a0a995c6f2a6effa639d74aec3e65f602232acacc4ed3ad2e70b40.jpg)

![](images/a17a7753ac60edb50e91101c678d78a1660d913446d2009b7ba609d07eee2fcc.jpg)

![](images/591c9f96b236757e5c24751c1e25cff8a3ee27d8134d6f4e2b8357e6542b8b5f.jpg)

However, this is not always the case.

ghci> v5

(a.(a.a)).a

ghci> alpha v5

(a.(a.a)).a

This situation is solved by our ialpha function as follows:

```txt
ghci> ialpha v5 ((a.a).a).a
```

Lines 69-71 define the len function that implements the length function in Example 8.4. Note that the len function cannot be applied to binary words that contain the symbol  $e$ . However, this is enough for our purpose.

Lines 73-75 define the rank function that measures how left heavy the tree is. For example, the ranks of  $\nu_{1},\ldots ,\nu_{5}$  in Example 8.4 can be calculated as follows:

```txt
ghci> map rank [v1,v2,v3,v4,v5] [3,1,0,2,1]
```

Lines 86-88 define the split function that generates all possible binary divisions of a given list without disturbing sequence.

```txt
ghci> split [1..5]  
[[[1], [2,3,4,5]), ([1,2], [3,4,5]), ([1,2,3], [4,5]), ([1,2,3,4], [5])]]
```

Lines 95-99 define the mkwords function that generates all the binary trees whose leaves are taken from a given list from left to right.

```txt
ghci> mkwords [1..4]  
[1.(2.(3.4)),1.((2.3).4),(1.2).(3.4),(1.(2.3)).4,((1.2).3).4]
```

We can see that the elements of the resulting list correspond to the vertices of the pentagon coherence (8.1).

The number of all possible binary trees of length 5 is obtained as follows.

```txt
ghci> length $ mkwords [1..5] 14
```

A more convincing test for the function ialpha is shown below:

```txt
ghci> and $ map (lgenerate [1..7] ==) $ map ialpha $ mkwords [1..7] True
```

Now, we return to Theorem 8.1.

Definition 8.5 Let  $\mathcal{W}_0$  be a subcategory of  $\mathcal{W}$  by excluding all the binary words and morphisms containing  $e$ .

Let  $\mathcal{C}$  be a monoidal category and  $X\in \mathrm{Obj}(\mathcal{C})$ . For the moment, we will work within the category  $\mathcal{W}_0$ . Let  $G_{n,X}$  be a directed graph whose vertices are all binary words in  $\mathcal{W}_0$ , and whose edge  $\nu \rightarrow w$  is a certain morphism, called a basic arrow defined shortly, from  $\nu_{X}$  to  $w_{X}$  in  $\mathcal{C}$ .

We define basic arrows recursively:

-  $\alpha_{u_X, v_X, w_X}: u_X \otimes (v_X \otimes w_X) \to u_X \otimes (v_X \otimes w_X)$  and its inverse  $\alpha_{u_X, v_X, w_X}^{-1}$  is basic,  
for  $\beta$  already defined basic,  $1\otimes \beta$  and  $\beta \otimes 1$  are basic.

When the object  $X$  is fixed in the discussion, we simply write  $\alpha_{u,v,w}$  instead of  $\alpha_{u_X,\nu_X,w_X}$ . A basic arrow is a morphism obtained by tensoring one  $\alpha$  or  $\alpha^{-1}$  with several 1's. A basic arrow contains exactly one  $\alpha$  or  $\alpha^{-1}$  in its  $\otimes$  factors. We call the former case a forward basic arrow, the latter backward basic arrow. A path obtained by composing only basic forward arrows is called a forward path. A path obtained by composing only basic backward arrows is called a backward path.

In the graph  $G_{n,X}$  the paths from  $v$  to  $w$  are a composition of basic arrows, which starts from  $v_X$  and ends at  $w_X$ .

We want to show that any two paths from  $\nu$  to  $w$  yield the same arrow in  $\mathcal{C}$ . In other words, the graph  $G_{n,X}$  is a commutative diagram in  $\mathcal{C}$ .

Definition 8.6 For any  $w \in \mathrm{Obj}(\mathcal{W})$ , we assign a integer rank  $(w)$  recursively as follows:

-  $\operatorname{rank}(e) = \operatorname{rank}(a) = 0$ , and  
-  $\operatorname{rank}(\nu \otimes w) = \operatorname{rank}(\nu) + \operatorname{rank}(w) + \operatorname{len}(w) - 1$ .

We have already seen the implementation in Haskell. See Listing 8.1.

Let  $w^{(n)}$  be the most left heavy binary word in  $\mathcal{W}_0$ . Or in other words, the word  $w^{(n)}$  is a binary tree all of whose recursive right branches are leaf nodes. See the binary tree representation of  $w^{(n)}$  below:

![](images/f0ce3c9654bf50718ae8a493617799bb748bf7f4a6c4889acc4bd23ede1d8466.jpg)

where leaf nodes are numbered from 1 to  $n$ .

Lemma 8.2 For any  $w \in \mathrm{Obj}(\mathcal{W}_0)$ , we have  $\mathrm{len}(w) \geq 0$ .

Proof The lemma restricts its claim to words in  $\mathcal{W}_0$ . So, the rank function is nondecreasing with respect to the  $\otimes$  operation. To be specific, we have

$$
\operatorname {r a n k} (v \otimes w) = \operatorname {r a n k} (v) + \operatorname {r a n k} (w) + \operatorname {l e n} (w) - 1 \geq \operatorname {r a n k} (v) + \operatorname {r a n k} (w).
$$

![](images/07f0f0f6c9b723c0686a2471e7f34fb98f9aa7e6dc4f5e36363186916cdcc369.jpg)

Lemma 8.3 Let  $w \in \mathrm{Obj}(\mathcal{W}_0)$ . If  $\operatorname{rank}(w) = 0$ , then  $w = w^{(n)}$ .

Proof We prove by induction on the  $\otimes$  constructs. If  $w = a$ , that is no  $\otimes$  appears, then  $w = w^{(1)}$  by definition, which is the base case.

Let  $w = w_{1} \otimes w_{2}$ . Since we know that the rank function is non-negative and non-decreasing with respect to  $\otimes$ , we must have  $\mathrm{rank}(w_{1}) = \mathrm{rank}(w_{2}) = 0$  and  $\mathrm{len}(w_{2}) = 1$ . By induction hypothesis, the left branch is  $w_{1} = w^{(n - 1)}$ . The right branch  $w_{2}$  must be a leaf. This completes the proof.

Lemma 8.4 Forward basic arrows always decrease the rank of a word.

Proof Let  $\nu \otimes (w_1 \otimes w_2)$  be a subword of a binary word in question. If we apply  $\alpha_{u, w_1, w_2}$  to this part of the binary word, the rank of this subword changes while the length being unchanged. So, all we have to do is to compare the ranks of a subword before and after the operation.

$$
\begin{array}{l} \operatorname {r a n k} (v \otimes \left(w _ {1} \otimes w _ {2}\right)) = \operatorname {r a n k} (v) + \operatorname {r a n k} \left(w _ {1}\right) + \operatorname {r a n k} \left(w _ {2}\right) + \operatorname {l e n} \left(w _ {1}\right) + 2 \times \operatorname {l e n} \left(w _ {2}\right) - 2 \\ \operatorname {r a n k} \left(\left(v \otimes w _ {1}\right) \otimes w _ {2}\right) = \operatorname {r a n k} (v) + \operatorname {r a n k} \left(w _ {1}\right) + \operatorname {r a n k} \left(w _ {2}\right) + \operatorname {l e n} \left(w _ {1}\right) + \operatorname {l e n} \left(w _ {2}\right) - 2 \\ \end{array}
$$

Since the length of  $w_{2}$  is not zero, the lemma holds.

![](images/7510cef06fa7051aec8e949a4ce24b6f65b67fd8a4aa5f691a3e4a77d76be93b.jpg)

Lemma 8.5 For any  $w \in \mathrm{Obj}(\mathcal{W}_0)$  of length  $n$ , there is a forward basic path from  $w$  to  $w^{(n)}$  in  $G_{n,X}$ .

The algorithm to find a forward path is implemented in Listing 8.1. There are other algorithms to reach this goal. Any way, we have one.

Lemma 8.6 Let  $v, w \in \mathrm{Obj}(\mathcal{W}_0)$  be of the same length  $n$ . If there are two forward paths from  $v$  to  $w$  in  $G_{n,X}$ , then they are identical morphisms in  $\mathcal{C}$ .

To prove the above lemma, we need the following diamond lemma.

Lemma 8.7 (The Diamond Lemma) Let  $\nu \in \mathrm{Obj}(\mathcal{W}_0)$ . If there are forward paths  $\beta : \nu \to \nu'$  and  $\gamma : \nu \to \nu''$ , then there are forward paths  $\nu' \to z$  and  $\nu'' \to z$  that make the following diagram commute:

![](images/f1ba3737e722894c344fa7437deb7d4a3c2a96c7b99bc37f1a6bd9738a743e64.jpg)

Before proving this, we return to the previous lemma and give it a proof using this diamond lemma.

Proof (Lemma 8.6) We prove by induction on the rank of  $w$ . Suppose the lemma holds for all  $w$  of lower ranks.

Let  $\beta = \beta_{k} \circ \dots \circ \beta_{1}: w \to w^{(n)}$  and  $\gamma = \gamma_{\ell} \circ \dots \circ \gamma_{1}: w \to w^{(n)}$  are two forward paths, where  $\beta_{i}$ 's and  $\gamma_{i}$ 's are basic forward arrows. We have the following diagram with the commuting diamond:

![](images/cb2bd7cc06b1d867b9b7073665d1d7171d29effffdbeb2fcbf77b598921545ca.jpg)

Since  $w^{\prime}$ ,  $w^{\prime \prime}$ , and  $z$  have a lower rank, the two triangles are commutative by the induction hypothesis. This shows that the outer quadrilateral commutes.

Let us prove the diamond lemma.

Proof (Lemma 8.7) We prove by induction on the rank of  $\nu$ . If  $\operatorname{rank}(\nu) = 0$ , then  $\nu = w^{(n)}$ . We have nothing to do in the base case since there can be no forward paths from  $\nu$  other than the identity.

Let us suppose the lemma holds for all  $\nu$  of smaller ranks. Let  $\nu = u\otimes w$ . The morphism  $\beta$  may appear in three forms:

-  $\beta = \beta' \otimes 1_w : \beta$  acts inside  $u$ .  
-  $\beta = 1_{u} \otimes \beta^{\prime \prime} : \beta$  acts inside  $w$ .  
-  $\beta = \alpha_{u,s,t}$  where  $w = s\otimes t$

The path  $\gamma$  has the same case division. If both  $\beta$  and  $\gamma$  act inside  $u$  or  $w$ , we can additionally apply induction on the length of  $\nu$ . We omit this branch of proof.

(Case 1) Let  $\beta = \beta' \otimes 1_w$  acts inside  $u$  and  $\gamma : 1_u \otimes \gamma'$  inside  $w$ . The following diagram commutes since  $\otimes$  is a bifunctor, namely, component morphisms act parallelly and independently.

$$
u ^ {\prime} \otimes w \xrightarrow [ 1 _ {u ^ {\prime}} \otimes \gamma^ {\prime} ]{\beta^ {\prime} \otimes 1 _ {w}} u ^ {\prime} \otimes w ^ {\prime} \xrightarrow [ \beta^ {\prime} \otimes 1 _ {w ^ {\prime}} ]{1 _ {w ^ {\prime}}} u ^ {\prime} \otimes w ^ {\prime}
$$

This is a desired diamond.

(Case 2) Let  $\nu = u\otimes (s\otimes t)$ . Let  $\beta = \alpha_{u,s,t}$  and  $\gamma = \gamma^{\prime}\otimes 1_{s\otimes t}$ . We have the following diagram:

$$
\begin{array}{c} u \otimes (s \otimes t) \\ \stackrel {{\alpha_ {u, s, t}}} {{\leftarrow}} \\ (u \otimes s) \otimes t \\ \stackrel {{(\gamma^ {\prime} \otimes 1 _ {s}) \otimes 1 _ {t}}} {{\leftarrow}} \\ (u ^ {\prime} \otimes s) \otimes t \end{array} \stackrel {{\gamma^ {\prime} \otimes 1 _ {s \otimes t}}} {{\leftarrow}} u ^ {\prime} \otimes (s \otimes t)
$$

This diagram commutes since  $\alpha$  is a natural isomorphism between the functors  $-\otimes (-\otimes -)$  and  $(- \otimes -) \otimes -$  as follows:

$$
\begin{array}{c} (u, s, t) \xrightarrow {(- \otimes -) \otimes -} (u \otimes s) \otimes t \\ \gamma^ {\prime} \times 1 _ {s} \times 1 _ {t} \\ (u ^ {\prime}, s, t) \xrightarrow [ (- \otimes -) \otimes - ]{(- \otimes -) \otimes -} (u ^ {\prime} \otimes s) \otimes t \end{array}
$$

The trapezoid at right must commute, which is identical to the desired diamond.

(Case 3) Let  $v = u \otimes (s \otimes t)$ . Let  $\beta = \alpha_{u,s,t}$  and  $\gamma = 1_u \otimes (\gamma' \otimes 1_t)$ . We have the following diagram:

$$
\begin{array}{c} \underset {u, s, t} {\alpha_ {u, s, t}} \\ (u \otimes s) \otimes t \\ \quad (1 _ {u} \otimes \gamma^ {\prime}) \otimes 1 _ {t} \\ \quad (u \otimes s ^ {\prime}) \otimes t \end{array} \xrightarrow {u \otimes (s \otimes t)} \begin{array}{c} \underset {1 _ {u} \otimes (\gamma^ {\prime} \otimes 1 _ {t})} {\longrightarrow} \\ \quad \longrightarrow \\ u \otimes (s ^ {\prime} \otimes t) \\ \quad \longrightarrow \\ \underset {u, s ^ {\prime}, t} {\alpha_ {u, s ^ {\prime}, t}} \end{array}
$$

Naturality ensures the trapezoid at right in the following diagram commutes, which is identical to the desired diamond.

![](images/7ac15541685911ec7b0da93f5185fd8041308672ca2cba801f96ea42734e0e86.jpg)

(Case 4) Let  $\nu = u\otimes (s\otimes (p\otimes q))$ . Let  $\beta = \alpha_{u\otimes s,p,q}$  and  $\gamma = 1_u\otimes \alpha_{s,p,q}$ . We have the following diagram:

![](images/22c6a96ee5796be3905c36926ffcc74baca1bcb607cbcea3275fb395573dd99b.jpg)

The pentagon coherence assures that this diagram commutes. So, arrows  $\beta$  and  $\gamma$  can be forwardly extended to join at the bottom vertex.

We can omit other cases considering symmetries among them.

Now, we proceed to one of our main results. The reader might want to revisit Definition 8.5 beforehand.

Lemma 8.8 The graph  $G_{n,X}$  commutes. In other words, for any binary words  $v$  and  $w$  in  $G_{n,X}$ , any paths from  $v$  to  $w$  are identical.

Proof Along the path from  $\nu$  to  $w$ , forward subpaths and backward ones appear alternately. The following diagram illustrates the situation:

![](images/0a1b73b73142ec29330623af7c9bdd36bdb7f874f116be5491ea3e7930fe86e4.jpg)

It does not matter whether the path starts with a forward subpath or not. The argument will be completely the same. In any case, all the triangles commute due to

Lemma 8.6. This means we can collapse these triangles one by one to obtain the following equation:

![](images/60f0c4a4ead52b9e1b8dcb6f7c11729f7cb9c30375449a5ca5a613ee6ae0bdee.jpg)

The RHS is determined solely by  $\nu$  and  $w$ , which means that all the paths from  $\nu$  to  $w$  are identical.

We have shown that given a monoidal category  $\mathcal{C}$  the correspondence of arrows from  $\mathcal{W}_0$  to  $\mathcal{C}$  can be consistently defined. However Theorem 8.1 claims the unique existence of a strict monoidal functor  $\mathcal{W} \to \mathcal{C}$ . So, we have to additionally consider all words possibly containing the symbol  $e$ .

Definition 8.7 Let  $\bar{G}_{n,X}$  be the graph whose vertices are all words in  $\mathcal{W}$  of length  $n$ . Edges are constructed recursively as follows:

- All basic arrows defined for  $G_{n,X}$ .  
- Previously constructed arrows tensored from left or right by  $\lambda$  and  $\rho$ .

The graph  $G_{n,X}$  is a subgraph of  $\bar{G}_{n,X}$ . Arbitrary number of  $e$  can be embedded in a word without affecting the length of the word. Therefore, the graph  $\bar{G}_{n,X}$  infinite.

Lemma 8.9 The graph  $\bar{G}_{n,X}$  commutes. In other words, for any binary words  $v$  and  $w$  in  $\bar{G}_{n,X}$ , any paths from  $v$  to  $w$  are identical.

We will reduce the problem to  $G_{n,X}$ . If we observe the fact that elimination of  $e$  from a word by the unitors can be safely done without affecting other parts of the word. Let  $v = u \otimes (e \otimes w)$ . The unitor coherence

![](images/e75ad35ed868a83960c86c92623e40cad3e0774f04df7d345744907ea05ef811.jpg)

means that elimination of  $e$  can be done before or after the action of the associator  $\alpha$ , yielding the same result. With the help of Lemma 8.1, we can eliminate  $e$ 's at an arbitrary step without affecting associator operations. Thus, we can simply suppose that there are no  $e$ 's in the word.

After a long way of discussing series of lemmas, we got to the complete proof of Theorem 8.1.

We nearly get to the final stage.

Definition 8.8 Let  $\mathcal{C}$  be a monoidal category. For any binary word  $w\in \mathrm{Obj}(\mathcal{W})$  of length  $n$ , we define a functor  $w_{\mathcal{C}}:\mathcal{C}^n\to \mathcal{C}$  by replacing all "a"s by the identity functor of  $\mathcal{C}$ .

- If the length of  $w$  is 0, namely  $w = e$ , then  $e_{\mathcal{C}}: \mathcal{C}^0 = \mathbf{1} \to \mathcal{C}$  is the constant functor  $\mathrm{Const}_{\mathbb{1}}: \bullet \mapsto \mathrm{Id}_{\mathcal{C}}$ , where  $\bullet$  is the only object of 1 and  $\mathrm{Id}_{\mathcal{C}}: \mathcal{C} \to \mathcal{C}$  is the identity functor.  
- Let  $w$  and  $w'$  are words of length  $n$  and  $n'$ , respectively. If  $w_{\mathcal{C}}$  and  $w_{\mathcal{C}}'$  are already defined, then  $(w \otimes w')_{\mathcal{C}}$  is given by

$$
\mathcal {C} ^ {n + n ^ {\prime}} = \mathcal {C} ^ {n} \times \mathcal {C} ^ {n ^ {\prime}} \xrightarrow {w _ {\mathcal {C}} \times w _ {\mathcal {C}} ^ {\prime}} \mathcal {C} \times \mathcal {C} \xrightarrow {\otimes} \mathcal {C}
$$

Example 8.5 Let  $w = ((a \otimes a) \otimes a) \otimes (a \otimes a)$ . The corresponding functor is given by

$$
w _ {\mathcal {C}} = \left(\left(\operatorname {I d} _ {\mathcal {C}} \otimes \operatorname {I d} _ {\mathcal {C}}\right) \otimes \operatorname {I d} _ {\mathcal {C}}\right) \otimes \left(\operatorname {I d} _ {\mathcal {C}} \otimes \operatorname {I d} _ {\mathcal {C}}\right).
$$

Let  $(X_{1},X_{2},X_{3},X_{4},X_{5})\in \mathrm{Obj}(\mathcal{C}^{5})$  . Applying the functor  $w_{\mathcal{C}}$  , we get

$$
\left(\left(X _ {1} \otimes X _ {2}\right) \otimes X _ {3}\right) \otimes \left(X _ {4} \otimes X _ {5}\right).
$$

Definition 8.9 Let  $\mathcal{C}$  be a monoidal category. We construct another monoidal category  $\operatorname{It}(\mathcal{C})$ . Its objects are all pairs  $(n, T)$ , where  $T: \mathcal{C}^n \to \mathcal{C}$  is a functor. Its morphisms from  $(n, T)$  to  $(n', T')$ , if  $n = n'$ , are all natural transformations  $\gamma: T \to T'$ . There is no morphism from  $(n, T)$  to  $(n, T')$  if  $n \neq n'$ . We often write  $(n, T)$  as  $T$  for short when there can be no confusion.

The tensor product on objects is defined as  $(n, T) \otimes (n', T') = (n + n', T \otimes T')$ , where

$$
T \otimes T ^ {\prime}: \mathcal {C} ^ {m + n} \simeq \mathcal {C} ^ {m} \times \mathcal {C} ^ {n} \xrightarrow {T \times T ^ {\prime}} \mathcal {C} \times \mathcal {C} \xrightarrow {\otimes} \mathcal {C}.
$$

Note that we can safely identify  $\mathcal{C}^{m + n} = \mathcal{C}^m\times \mathcal{C}^n$ . The unit  $\mathbb{1}_{\mathrm{It}(\mathcal{C})}$  is the constant functor

$$
\begin{array}{l} \mathcal {C} ^ {0} \to \mathcal {C}: \bullet \mapsto \mathbb {1} _ {\mathcal {C}} \\ 1 _ {\bullet} \mapsto 1 _ {\mathbb {I}}, \\ \end{array}
$$

where  $\mathcal{C}^0 = \mathbf{1}$  is the category with one object  $\bullet$  and no morphisms other than the identity. We denote this unit  $\mathbb{1}_{\mathrm{It}(\mathcal{C})}$  by  $I$  in what follows.

We need the associator  $\alpha : -\otimes (-\otimes -) \to (-\otimes -)\otimes -$ . For any  $(n, T), (n', T'), (n'', T'')$ ,

$$
\alpha_ {T, T ^ {\prime}, T ^ {\prime \prime}}: T \otimes (T ^ {\prime} \otimes T ^ {\prime \prime}) \to (T \otimes T ^ {\prime}) \otimes T ^ {\prime \prime},
$$

is defined componentwise as

$$
\left(\alpha_ {T, T ^ {\prime}, T ^ {\prime \prime}}\right) _ {X, X ^ {\prime}, X ^ {\prime \prime}} = \alpha_ {T X, T ^ {\prime} X ^ {\prime}, T ^ {\prime \prime} X ^ {\prime \prime}},
$$

where  $X, X'$ , and  $X''$  denote

$$
X = \left(X _ {1}, X _ {2}, \dots , X _ {n}\right) \in \operatorname {O b j} \left(\mathscr {C} ^ {n}\right),
$$

$$
X ^ {\prime} = \left(X _ {1} ^ {\prime}, X _ {2} ^ {\prime}, \dots , X _ {n ^ {\prime}} ^ {\prime}\right) \in \operatorname {O b j} \left(\mathcal {C} ^ {n ^ {\prime}}\right), \text {a n d}
$$

$$
X ^ {\prime \prime} = \left(X _ {1} ^ {\prime \prime}, X _ {2} ^ {\prime \prime}, \dots , X _ {n ^ {\prime \prime}} ^ {\prime \prime}\right) \in \operatorname {O b j} \left(\mathcal {C} ^ {n ^ {\prime \prime}}\right),
$$

respectively.

The left unitor  $\lambda_T: I \otimes T \to T$  is given as follows. For any  $T: \mathcal{C}^n \to \mathcal{C}$  and  $X = (X_1, X_2, \ldots, X_n) \in \mathrm{Obj}(\mathcal{C}^n)$ , using the left unitor of  $\mathcal{C}$ , we set

$\lambda_{TX}:\mathbb{1}_{\mathcal{C}}\otimes TX\to TX$  . Likewise the right unitor  $\rho_T:T\otimes I\to T$  is given by  $\rho_{TX}:TX\otimes \mathbb{1}_{\mathcal{C}}\to TX$

Naturality will be shown later by Lemma 8.10. The pentagon coherence and unitor coherence are consequences of componentwise definitions.

Lemma 8.10 The associator  $\alpha$ , unitors  $\lambda$  and  $\rho$  in Definition 8.9 are a natural transformation, in fact a natural isomorphism.

Proof Let us begin with the associator  $\alpha$ . For any triplet of natural transformations  $\gamma : T \to S$ ,  $\gamma' : T' \to S'$ ,  $\gamma'' : T'' \to S''$ , we have to show the trapezoid at right in the following diagram commute:

![](images/76c315e24f214097ff118c9863002900579135a7301270d5266dade2526ff846.jpg)

To prove this, we just have to confirm commutativity of the component at an arbitrary object  $(X,X^{\prime},X^{\prime \prime})$ , where  $X$ ,  $X^{\prime}$ , and  $X^{\prime \prime}$  denote

$$
X = \left(X _ {1}, X _ {2}, \dots , X _ {n}\right) \in \operatorname {O b j} \left(\mathcal {C} ^ {n}\right),
$$

$$
X ^ {\prime} = \left(X _ {1} ^ {\prime}, X _ {2} ^ {\prime}, \dots , X _ {n ^ {\prime}} ^ {\prime}\right) \in \operatorname {O b j} \left(\mathcal {C} ^ {n ^ {\prime}}\right), \text {a n d}
$$

$$
X ^ {\prime \prime} = \left(X _ {1} ^ {\prime \prime}, X _ {2} ^ {\prime \prime}, \dots , X _ {n ^ {\prime \prime}} ^ {\prime \prime}\right) \in \operatorname {O b j} \left(\mathcal {C} ^ {n ^ {\prime \prime}}\right),
$$

respectively. The diagram at this component is as follows:

![](images/dacb54d49504d19c803fc391034077cf2ad4bf67004618070a3d1785aca8dc7c.jpg)

The associator appearing in this diagram is that of the category  $\mathcal{C}$ , which guarantees that the trapezoid at right commutes. Note that all the involved natural transformations are isomorphisms.

The naturality of the unitor  $\lambda$  requires that, for any  $(n,T),(n,S)$ , and a natural transformation  $\gamma :T\to S$ , the trapezoid at right in the diagram below commutes:

![](images/1999b3c101c86c995fe53954c03ddcf69dad3ae05f83dfc066e1fd0bd5d9e9c4.jpg)

To prove this, we just have to confirm commutativity of the component at an arbitrary object

$$
X = \left(X _ {1}, X _ {2}, \dots , X _ {n}\right) \in \operatorname {O b j} \left(\mathcal {C} ^ {n}\right).
$$

Namely,

![](images/c69dc44986101e73862893b03e8ca826c8ed50a9b408b0c92061daadd6722dbc.jpg)

The unitor  $\lambda$  appearing in this diagram is that of the category  $\mathcal{C}$ , which guarantees that the trapezoid at right commutes. All the morphisms in this diagram are isomorphisms.

The discussion on the unitor  $\rho$  goes completely in the same way.

Using the above construction  $\operatorname{It}(\mathcal{C})$ , we conclude the discussion on coherence. We give the last theorem.

We need the notion of canonical maps.

Definition 8.10 Let  $\mathcal{C}$  be a monoidal category. Let  $v$  and  $w$  be binary words of the same length. We construct natural isomorphisms from  $v_{\mathcal{C}} \to w_{\mathcal{C}}$  called a canonical map recursively as follows:

- If  $v = w = e$ , namely, both are empty word, we defined  $\nu_{\mathcal{C}} = w_{\mathcal{C}} = \mathrm{Const}_{1}$ . The identity natural isomorphism of from the constant functor to itself

$$
\mathcal {C} ^ {0} = \overbrace {\mathbf {1} \xrightarrow {\begin{array}{c} \operatorname {C o n s t} _ {1} \\ \Downarrow \operatorname {I d} _ {0} \\ \operatorname {C o n s t} _ {1} \end{array} }} ^ {\operatorname {C o n s t} _ {1}} \mathcal {C}
$$

is canonical.

- If  $\nu = w = a$ , then both  $\nu_{\mathcal{C}}$  and  $w_{\mathcal{C}}$  equal the identity functor  $1_{\mathcal{C}}$ . The identity isomorphism of from the identity functor to itself

$$
\mathcal {C} \xrightarrow {\begin{array}{c} 1 _ {\mathcal {C}} \\ \Downarrow \operatorname {I d} \\ 1 _ {\mathcal {C}} \end{array} } \mathcal {C}
$$

is canonical.

- The associator, unitors, and their inverses, namely,  $\alpha$ ,  $\alpha^{-1}$ ,  $\lambda$ ,  $\lambda^{-1}$ ,  $\rho$ , and  $\rho^{-1}$  are canonical. For example, if  $\nu = a \otimes (a \otimes a)$  and  $w = (a \otimes a) \otimes a$ , then  $v_{\mathcal{C}} = -\otimes (-\otimes -)$  and  $w_{\mathcal{C}} = (-\otimes -) \otimes -$ .

$$
\mathcal {C} ^ {3} \xrightarrow [ (- \otimes -) \otimes - ]{\stackrel {- \otimes (- \otimes -)} {\downarrow}} \mathcal {C}
$$

For another example, if  $\nu = e\otimes a$  and  $w = a$ , then  $\nu_{\mathcal{C}} = \mathbb{1}\otimes -$  and  $w_{\mathcal{C}} = -$ . Recall that  $\nu$  and  $w$  have the same length.

![](images/f5cb512e08f0bbba65c8481d5f39978999fbdcfae9d12e6458ad451faea4e09d.jpg)

is canonical. Note that  $\mathcal{C}$  and  $\mathbf{1} \times \mathcal{C}$  can be safely identified.

- The composites and  $\otimes$  products of all items above are canonical. For example, if

$$
v = a \otimes ((a \underline {{\otimes}} (a \underline {{\otimes}} a)) \otimes e)
$$

$$
w = a \otimes ((\underline {{(a \otimes a) \otimes a}}) \otimes e)
$$

then

![](images/83561547b23a8e43956925baad165951f4e9124c97f667ae248eb4c7bd2e3b39.jpg)

where we can safely identify  $\mathcal{C}^4$  with  $\mathcal{C}^4\times 1$

The following theorem is a corollary of Theorem 8.1.

Theorem 8.2 Let  $\mathcal{C}$  be a monoidal category. There is a function that assigns to each pair of words  $v$  and  $w$  of the same length  $n$  a unique natural isomorphism

![](images/5c48e10447f3114d0e5bb84a48d4898e687c0dc00e2281e4b358076dc0a4e207.jpg)

from the functor  $\nu_{\mathcal{C}}$  to the functor  $w_{\mathcal{C}}$ . We call this a canonical map.

Just write down the  $(X_{1},X_{2},\ldots ,X_{n})$  component of  $\mathrm{can}_{\mathcal{C}}(\nu ,w)$ , then you will see that this theorem says all about coherence.

# References

1. Coecke B, Kissinger A (2017) Picturing quantum processes. Cambridge University Press  
2. Turaev V, Virelizier A (2017) Monoidal categories and topological field theory. Birkhäuser  
3. Heunen C, Sadrzadeh M, Grefenstette E (eds) (2013) Quantum physics and linguistics. Oxford University Press  
4. Mac Lane S (1998) Categories for the working mathematician, Graduate texts in mathematics, vol 5, 2nd edn. Springer

# Epilogue

I wonder if the readers enjoyed a long journey to Yoneda's lemma or the coherence problem in monoidal categories. It was possible to take a shortcut to these goals. However, since this book is intended as an introductory book on category theory, readers are supposed to experience various examples of naturality and universality to really appreciate the beauty of these concepts.

Introducing Moggi's ideas with sample code became too lengthy, so I moved most of the correctness proofs to an appendix.

Most of the diagrams in this book were scribbled on my notebooks while I was seated on the commuter train over the past 10 years or so. I drew thousands of diagrams on the notebooks, but I discarded most of them. I selected some of the surviving diagrams that looked good to include in a publication. Criticism from the readers is welcome.

The Haskell code has been used in class on category theory. The code pieces are far from systematically designed. Rather, each piece of code is designed as independently as possible, so the reader can read and test it on the spot.

I had a plan to include the following topics.

- Kan extension  
- Ends and coends  
Enriched categories

However, I gave up the original plan because of the objectives of this book as I stated above. In addition, I found the quality of the code for these topics is not good enough for publication. I am looking forward to including these in the near future.

I would like to thank all the readers who have read this book.

# Appendix A Sets and Universe

The descriptions in this appendix are based on the literature [1], but with less rigor to suit the purpose of this book.

A famous paradox in set theory arises from the construction of sets using the comprehension principle. In the Naive set theory, given a property  $\varphi(x)$  of  $x$ , we can create a set  $\{x \mid \varphi(x)\}$  consisting of all  $x$  that satisfies this property. We know that this cannot be done freely without restrictions. Here, when we say the property  $\varphi(x)$  of  $x$ , we are referring to the function  $\varphi$  that returns true or false for  $x$ . The restricted comprehension principle allows us to use comprehension only in the form as follows:

$$
\{x \mid x \in u, \varphi (x) \},
$$

where  $u$  is already known to be a set. This proves to give us a good theoretical and practical framework for working in standard mathematics if it observes conditions described below.

In order to handle sets without contradiction, the rules for constructing new sets should be clearly defined. The construction of sets that deviate from the rules should be prohibited. We use a tool called a universe to handle "the set of all sets" or "a set of all sets with a given property" without contradiction. It was invented by Grothendieck to handle large categories with a minimum theoretical setting.

We assume the existence of a universe. A universe is a set  $U$  with the following properties:

1.  $x\in y$  and  $y\in U$  implies  $x\in U$  
2.  $x\in U$  and  $y\in U$  imply  $\{x,y\} ,\langle x,y\rangle$  , and  $u\times v\in U$  
3.  $x\in U$  implies  $\mathcal{P}x\in U$  and  $\cup x\in U$  
4.  $\omega = \{0,1,2,\ldots \} \in U$  
5. if  $f: a \to b$  is surjective with  $a \in U$  and  $b \subset U$ , then  $b \in U$ .

These properties ensure that  $U$  is closed under all standard operations in set theory.

A universe may not be unique (recall that we assumed its existence). So, we take one of them, and fix the universe  $U$ , and call any set  $u \in U$  a small set. Therefore, we may say that the universe  $U$  is the set of all small sets.

We say function  $f: a \to b$  is small if  $a$  and  $b$  are small sets. In fact, function  $f$  can be identified with its graph  $\{\langle x, y \rangle \mid \langle x, y \rangle \in a \times b, \langle x, y \rangle \in f\}$ . So, by the rules above with the limited comprehension principle, we know that  $f$  is a small set.

Given small sets  $a$  and  $b$ , we can form the small set of functions from  $a$  to  $b$ . Let

$$
\varphi (f) \stackrel {{\text {d e f}}} {{=}} \forall x \in a. \exists ! y. (x, y) \in f,
$$

which is the requirement for a correspondence  $f$  to be a function. We set

$$
\operatorname {H o m} (a, b) = \{f \mid f \in a \times b, \varphi (f) \},
$$

which is also a small set.

Now, we can define the category Set. Its set of objects is  $U$  and its set of morphisms from  $a$  to  $b$  is  $\operatorname{Hom}(a, b)$  as defined above.

# Appendix B Calculations with Output

In this appendix, we will prove all the equations that are required to establish instances of Functor, Applicative, and Monad type classes in the sample code 6.7 CalcWith-Output2.hs.

# B.1 Functor Instance

We prove equations for Fctor instances.

Proposition B.1 The following equality holds.

fmap id = id

Proof We rewrite the LHS step by step.

```txt
fmap id x -- apply the definition of fmap  $= \mathrm{T}$  (\s -> let (a,s2)  $=$  (unT x)s in (a,s2)) -- evaluate the let expression   
 $= \mathrm{T}$  (\s -> unTx s) -- eta conversion   
 $= \mathrm{T}$  (unTx) -- cancel the T/unT pair   
 $= \mathbf{x}$
```

□

Proposition B.2 The following equality holds.

fmap (g.f) = fmap g.fmap f

Proof We rewrite the RHS step by step.

```txt
fmap g (fmap f ta) -- evaluate (fmap f)  $=$  fmap g (T  $\backslash s$  -> let (a,s2)=unT ta s in (f a,s2)) -- evaluate (fmap g)  $=$  T (\t->let  $(\mathtt{b},\mathtt{t}2) = \mathtt{unT}$  (T  $\backslash s$  ->let (a,s2)=unT ta s in (f a,s2)) ） t in (g b,t2)) -- cancel the T/unT pair  $=$  T (\t->let  $(\mathtt{b},\mathtt{t}2) = (\backslash \mathtt{s}\rightarrow$  let (a,s2)=unT ta s in (f a,s2)) ） t in (g b,t2)) -- beta reduction  $=$  T (\t->let  $(\mathtt{b},\mathtt{t}2) = (\mathtt{let}$ $(\mathtt{a},\mathtt{s}2) = \mathtt{unT}$  ta t in (f a,s2)) in (g b,t2)) -- combine two let-expressions:  $\mathtt{b} = \mathtt{f}$  a, t2 = s2  $=$  T (\t->let  $(\mathtt{a},\mathtt{s}2) = \mathtt{unT}$  ta t  $(\mathtt{b},\mathtt{t}2) = (\mathtt{f}$  a,s2) in (g b,t2)) -- combine substitutions  $=$  T (\t->let  $(\mathtt{a},\mathtt{t}2) = \mathtt{unT}$  ta t in ((g.f) a),t2)) -- definition of (fmap)  $=$  fmap (g.f) ta
```

□

# B.2 Applicative Instance

Proposition B.3 (Identity) The following equality holds.

pure id  $<  * >$  ta  $\equiv$  ta

Proof We rewrite the LHS step by step.

```txt
pure id  $\text{<  >}$  ta -- by definition of pure and  $\text{<  >}$ $= T$  (\s -> let  $(\mathrm{h},\mathrm{s}2) = \mathrm{unT}$  (T  $\left(\backslash \mathrm{s} - > (\mathrm{id},\mathrm{s})\right)$  s  $(\mathbf{a},\mathbf{s}3) = \mathbf{unT}$  ta s2 in (ha,s3)) -- cancel the T/unT pair  $= T$  (\s -> let  $(\mathrm{h},\mathrm{s}2) = (\backslash \mathrm{s} - > (\mathrm{id},\mathrm{s}))$  s  $(\mathbf{a},\mathbf{s}3) = \mathbf{unT}$  ta s2 in (ha,s3)) -- beta reduction   
 $= T$  (\s -> let  $(\mathrm{h},\mathrm{s}2) = (\mathrm{id},\mathrm{s})$ $(\mathbf{a},\mathbf{s}3) = \mathbf{unT}$  ta s2 in (ha,s3)) -- do part of the let expression   
 $= T$  (\s -> let  $(\mathrm{a},\mathrm{s}3) = \mathrm{unT}$  ta s in (a,s3)) -- do another part of the let expression   
 $= T$  (\s -> unT ta s) -- eta conversion   
 $= T$  (unT ta) -- cancel the T/unT pair   
 $= \text{ta}$
```

Proposition B.4 (Composition) The following equality holds.

pure (.)< $\gg$  tu  $<\gg$  tv  $<\gg$  tw = tu  $<\gg$  (tv  $<\gg$  tw)

```txt
Proof We rewrite the LHS from left. pure (. -- definition of pure  $= T(\backslash s\rightarrow ((.)s)$  -- Recall that (.u v w = (u.v) w = u (v w).  $= T(\backslash s\rightarrow ((\backslash g\rightarrow \backslash f\rightarrow \backslash x\rightarrow g(fx)),s))$
```

```txt
shift to right pure  $(.)\ll >$  tu  $= T(\backslash s\rightarrow ((\backslash g\rightarrow \backslash f\rightarrow \backslash x\rightarrow g(f x)),s)) <  >$  tu -- definition of  $<  >$ $= T$  (\ss->let (h,s2)  $=$  unT (T(\s->((\\g->f->x->g(f x)),s)) ss  $(u,s3) =$  unT tu s2 in (h u,s3)) -- cancel the T/unT pair   
 $= T$  (\ss->let (h,s2)  $=$  (\s->((\\g->f->x->g(f x)),s) ss  $(u,s3) =$  unT tu s2 in (h u,s3)) -- beta reduction   
 $= T$  (\ss->let (h,s2)  $=$  ((\\g->f->x->g(f x)),ss)  $(u,s3) =$  unT tu s2 in (h a,s3)) -- streamline the let expression   
 $= T$  (\ss->let h=(\\g->f->x->g(f x))  $(u,s3) =$  unT tu ss in (h u,s3)) -- further streamline the let expression   
 $= T$  (\s-> let (u,s3)  $=$  unT tu s in ((\\g->f->x->g(f x)) u, s3)) -- beta reduction in the "in" clause   
 $= T$  (\s-> let (u,s3)  $=$  unT tu s in ((\\f->\\x->u(f x)), s3)) -- rename local a variable   
 $= T$  (\s-> let (u,s2)  $=$  unT tu s in ((\\f->\\x->u(f x)), s2))   
shift further right pure  $(.)\ll >$  tu  $<  >$  tv -- apply the definition of  $<  >$  to the second instance  $= T$  (\ss->let (h,s3)  $=$  unT (T (\s-> let (u,s2)  $=$  unT tu s in ((\\f->\\x->u(f x)), s2)) ) ss  $(v,s4) =$  unT tv s3 in (h v,s4) -- cancel the T/unT pair   
 $= T$  (\ss->let (h,s3)  $=$  (\s-> let (u,s2)  $=$  unT tu s in ((\\f->\\x->u(f x)), s2)) ) ss  $(v,s4) =$  unT tv s3 in (h v,s4) -- beta reduction   
 $= T$  (\ss->let (h,s3)  $=$  let (u,s2)  $=$  unT tu s
```

```txt
in  $(\backslash f->\backslash x->u(f x))$  , s2)  $\begin{array}{rl} & {\mathrm{(v,s4)} = \mathrm{unT}\mathrm{tv}\mathrm{s3}}\\ & {\mathrm{in}\quad (\mathrm{h}\mathrm{v},\mathrm{s4})} \end{array}$  -- let s3=s2 and h  $=$ $\backslash \mathbf{f} - >\backslash \mathbf{x} - >\mathbf{u}(\mathbf{f}\mathbf{x}))$  -- beautify  $= T$  (ss->let  $\left(\mathbf{u},\mathbf{s}2\right) = \mathbf{unT}$  tu ss  $\mathrm{(v,s3)} = \mathrm{unT}$  tv s2 in  $((\backslash f->\backslash x->u(f x))v,s3)$  -- beta reduction in the left part on the (in) expression  $= T$  (ss->let  $\left(\mathbf{u},\mathbf{s}2\right) = \mathbf{unT}$  tu ss  $\mathrm{(v,s3)} = \mathrm{unT}$  tv s2 in ((x->u(v x)),s3) Complete the calculation of the LHS to the rightmost pure (.)<\*>tu <\*\*>tv <\*\*>tw -- definition of the rightmost <\*\*>  $= T$  (s->let  $\left(\mathrm{h},\mathrm{s}4\right) = \mathrm{unT}$  T (T (ss->let  $\left(\mathbf{u},\mathbf{s}2\right) = \mathbf{unT}$  tu ss  $(\mathrm{v},\mathrm{s}3) = \mathrm{unT}$  tv s2 in ((x->u(v x)),s3) )s (w,s5)=unT tw s4 in (h w,s5) -- cancel the T/unT pair  $= T$  (s->let  $\left(\mathrm{h},\mathrm{s}4\right) = (\backslash \mathrm{s}s - >1$  let  $\left(\mathbf{u},\mathbf{s}2\right) = \mathbf{unT}$  tu ss  $(\mathrm{v},\mathrm{s}3) = \mathrm{unT}$  tv s2 in ((x->u(v x)),s3) )s (w,s5)=unT tw s4 in (h w,s5) -- beta reduction  $= T$  (s->let  $\left(\mathrm{h},\mathrm{s}4\right) = \mathrm{let}\quad (\mathrm{u},\mathrm{s}2)\quad = \mathrm{unT}$  tu s  $(\mathrm{v},\mathrm{s}3) = \mathrm{unT}$  tv s2 in ((x->u(v x)),s3) (w,s5)=unT tw s4 in (h w,s5) -- knowing that s4  $= \mathfrak{s}3$  and h  $=$  (x->u(v x))  $= T$  (s->let  $\left(\mathbf{u},\mathbf{s}2\right) = \mathbf{unT}$  tu s  $(\mathrm{v},\mathrm{s}3) = \mathrm{unT}$  tv s2  $(\mathrm{w},\mathrm{s}4) = \mathrm{unT}$  tw s3 in ((x->u(v x)) w,s4) -- beta reduction in the (in) expression  $= T$  (s->let  $\left(\mathbf{u},\mathbf{s}2\right) = \mathbf{unT}$  tu s
```

```txt
(v,s3) = unT tv s2  
(w,s4) = unT tw s3  
in (u(v w),s4)  
We compute the RHS from the innermost of parentheses.  
tv <> tw  
-- definition of <>  
= T (\s -> let (v,s2)=unT tv s  
(w,s3)=unT tw s2  
in (v w,s3)  
go one level up  
tu <> (tv <> tw)  
= T (\t -> let (u,s4)=unT tu  
(x,s5)=unT (T (\s -> let (v,s2)=unT tv s  
(w,s3)=unT tw s2  
in (v w,s3))  
) s4  
in (u x,s5)  
-- rename s4 to s1  
= T (\t -> let (u,s1)=unT tu t  
(x,s5)=(\s -> let (v,s2)=unT tv s  
(w,s3)=unT tw s2  
in (v w,s3)  
) s1  
in (u x,s5)  
)  
-- beta reduction  
= T (\t -> let (u,s1)=unT tu t  
(x,s5)=let (v,s2)=unT tv s1  
(w,s3)=unT tw s2  
in (v w,s3)  
)  
-- streamline the let expression  
= T (\t -> let (u,s1)=unT tu t  
(v,s2)=unT tv s1  
(w,s3)=unT tw s2  
(x,s5)=(v w,s3)  
in (u x,s5)  
)  
-- collect  
= T (\s -> let (u,s1)=unT tu s  
(v,s2)=unT tv s1  
(w,s3)=unT tw s2  
in (u (v w),s3)  
)  
-- rename local variables
```

```latex
$\begin{array}{rl} & = \mathrm{T}(\backslash \mathrm{s}\rightarrow \mathrm{let}(\mathrm{u},\mathrm{s2}) = \mathrm{unTtu}\mathrm{s}\\ & \qquad (\mathrm{v},\mathrm{s3}) = \mathrm{unTtv}\mathrm{s2}\\ & \qquad (\mathrm{w},\mathrm{s4}) = \mathrm{unTtw}\mathrm{s3}\\ & \qquad \mathrm{in}(\mathrm{u}(\mathrm{v}\mathrm{w}),\mathrm{s4})\\ & \qquad \end{array}$  The LHS and RHS gives the same result.
```

Proposition B.5 (Homomorphism) The following equality holds.

```lisp
pure  $f < *$  pure  $x =$  pure (f x)
```

Proof We rewrite the LHS step by step.

```haskell
pure f  $<  *>$  pure x -- definition of  $<  *>$ $\begin{array}{rl} & = T(s\rightarrow let(ff,s2) = unT(T(\backslash t\rightarrow (f,t))s\\ & \qquad (xx,s3) = unT(T(\backslash t\rightarrow (x,t))s2\\ & \qquad in(ff xx,s3))\\ & \qquad -- cancel the T/unT pair \\ & = T(s\rightarrow let(ff,s2) = (\backslash t\rightarrow (f,t))s\\ & \qquad (xx,s3) = (\backslash t\rightarrow (x,t))s2\\ & \qquad in(ff xx,s3))\\ & \qquad -- beta reduction at two places \\ & = T(s\rightarrow let(ff,s2) = (f,s)\\ & \qquad (xx,s3) = (x,s2)\\ & \qquad in(ff xx,s3))\\ & \qquad -- streamline the let expression \\ & = T(s\rightarrow ((f x),s))\\ & \qquad -- definition of pure \\ & = pure(f x) \end{array}$
```

Proposition B.6 (Commutativity) The following equality holds.

```perl
u <> pure y = pure ($ y) <> u
```

Proof We rewrite the LHS step by step.

```txt
u  $<  >$  pure y -- definitions of  $<  >$  and pure  $\mathbf{\sigma} = \mathbf{T}$  (s -> let (uu,s2)  $=$  unT u s (yy,s3)  $=$  unT (T (\t-> (y,t))）s2 in (uu yy,s3)） -- cancel the T/unT pair
```

```txt
$= T$  (s -> let (uu,s2) = unT u s  
 $(yy,s3) = (\backslash t -> (y,t))$  s2  
in (uu yy,s3) -- beta reduction  
 $= T$  (s -> let (uu,s2) = unT u s  
 $(yy,s3) = (y,s2)$  in (uu yy,s3) -- streamline substitutions  
 $= T$  (s -> let (uu,s2) = unT u s  
in (uu y,s2) -- simplify local variables  
 $= T$  (s -> let (f,s2) = unT u s  
in (f y,s2)
```

```txt
We compute the RHS. pure (\( y) \) <> u -- eta conversion (\( y) = \)f -> f y \( = \) pure (\( f \) -> f y) <> u -- definition of pure \( = \) T (\( s \) -> ((\( f \) -> f y),s)) <> u -- definition of <> \( = \) T (\( t \) -> let (\( g, t2) = \) unT (\( T \) (\( s \) -> ((\( f \) -> f y),s)) t (\( a, t3) = \) unT u t2 in (\( g \) a, t3)) -- cancel the T/unT pair \( = \) T (\( t \) -> let (\( g, t2) = \) (\( s \) -> ((\( f \) -> f y),s)) t (\( a, t3) = \) unT u t2 in (\( g \) a, t3)) -- beta reduction \( = \) T (\( t \) -> let (\( g, t2) = \) ((\( f \) -> f y),t) (\( a, t3) = \) unT u t2 in (\( g \) a, t3)) -- streamline the let expression \( = \) T (\( t \) -> let (\( a, t3) = \) unT u t in ((\( f \) -> f y) a, t3)) -- beta reduction \( = \) T (\( t \) -> let (\( a, t3) = \) unT u t in (\( a, t3)) -- rename local variables \( = \) T (\( s \) -> let (\( f, s2) = \) unT u s in (\( f \) y, s2))
```

□

# B.3 Monad Instance

We prove equations for functor instances.

Proposition B.7 (left unit) The following equality holds.

```txt
return  $\mathbf{x} > > = \mathbf{f} = \mathbf{f}$  x
```

Proof We rewrite the LHS step by step.

```haskell
return x >= f
-- definition of return
= T (\s -> (x,s)) >= f
-- definition of (++=)
= sharp f $ T (\s -> (x,s))
= T (\st1 -> let (y,st2) = unT T (\s -> (x,s)) s
in unT (f y) st2 )
-- cancel the T/unT pair
= T (\st1 -> let (y,st2) = (\s -> (x,s)) st1
in unT (f y) st2 )
-- beta reduction
= T (\st1 -> let (y,st2) = (x,st1)
in unT (f y) st2 )
-- streamline the let expression
= T (\st1 -> unT (f x) st1 )
-- eta conversion
= T (unT (f x))
-- cancel the T/unT pair
= f x
```

![](images/a8634ab68424b6e5ccf3e5067b2a955bd4ca57325dcb2836fb4b34148c9a12d5.jpg)

Proposition B.8 (right unit) The following equality holds.

```txt
$\mathbf{m} > > =$  return  $\equiv$  m
```

```txt
Proof m  $>> =$  return -- definition of  $(\gg =)$ $= \mathrm{sharp}$  return m  $= T$  (\st1 -> let (y,st2)  $=$  unT m st1 in unT (return y) st2) -- definition of return  $= T$  (\st1 -> let (y,st2)  $=$  unT m st1 in unT (T (\s->y,s)) st2) -- cancel the T/unT pair  $= T$  (\st1 -> let (y,st2)  $=$  unT m st1
```

```txt
in  $\mathbf{\Pi}(\mathbf{s}\rightarrow (\mathbf{y},\mathbf{s}))$  st2) --beta reduction   
 $= T$  (st1 -> let  $(\mathrm{y},\mathrm{st2}) =$  unT m st1 in  $\mathbf{(y,st2)}$  ） -- streamline the let expression   
 $= T$  (st1 -> unT m st1) -- eta conversion   
 $= T$  (unT m) -- cancel the T/unT pair   
 $= \mathfrak{m}$
```

![](images/08205d84220c186138db6227c644857e4e499e990b08996ef98185b48faefc87.jpg)

Proposition B.9 (associativity) The following equality holds.

```latex
$(\mathfrak{m} > > = \mathfrak{f}) > > = \mathfrak{g} = \mathfrak{m} > > = (\backslash \mathbf{x}\Rightarrow \mathbf{f}\quad \mathbf{x} > > = \mathbf{g})$
```

Proof We first calculate a subexpression of the LHS.

```haskell
m  $>> = \mathrm{f}$  -- definition of  $(\gg =)$ $=$  sharp f m   
 $= T$  (\st1 -> let (y,st2)  $=$  unT m st1 in unT (f y) st2)   
Next, we calculate the whole LHS.   
(m  $>> = \mathrm{f}) >> = \mathrm{g}$  -- replace  $(\gg = \mathrm{g})$  with sharp   
 $=$  sharp g $T(\st1 -> let (y,st2)  $=$  unT m st1 in (f y) st2) -- definition of sharp   
 $= T$  (\s1 -> let (p,s2)  $=$  unT (T (\st1 -> let (y,st2)  $=$  unT m st1 in unT (f y) st2)) s1 in unT (g p) s2) -- cancel the T/unT pair   
 $= T$  (\s1 -> let (p,s2)  $=$  (\st1 -> let (y,st2)  $=$  unT m st1 in unT (f y) st2) s1 in unT (g p) s2) -- beta reduction   
 $= T$  (\s1 -> let (p,s2)  $=$  let (y,st2)  $=$  unT m s1 in unT (f y) st2 in unT (g p) s2) -- streamline the let expression   
 $= T$  (\s1 -> let (y,st2)  $=$  unT m s1  $(z,\mathrm{st}3)=\mathrm{unT}(f,y)\mathrm{st}2$  in unT (g z) st3) -- rename local variables   
 $= T$  (\s1 -> let (v2,s2)  $=$  unT m s1
```

```latex
$\begin{array}{l}\mathrm{(v3,s3) = unT(f v2)s2}\\ \mathrm{in~unT(g v3)s3)}\\ \mathrm{in~unT(g v3)s3)} \end{array}$    
We calculate a subexpression of the RHS.   
f x >= g -- replace  $(\gg = \mathbf{g})$  with sharp  $=$  sharp g (f x)  $= T$  (\st1 -> let (y,st2)  $=$  unT (f x) st1 in unT (g y) st2)   
We calculate a subexpression that contains this.   
 $\backslash \mathbf{x} - > (\mathbf{f}\mathbf{x} > > = \mathbf{g})$  -- use the result above  $=\backslash \mathbf{x}\rightarrow \mathbf{T}\backslash \mathbf{s}\mathbf{t}\mathbf{1}\rightarrow$  let (y,st2)  $=$  unT (f x) st1 in unT (g y) st2)   
We calculate the whole RHS.   
m  $> = (\backslash x - > f x > > = g)$  -- replace  $(\gg =)$  with sharp  $=$  sharp (\x -> T (\st1 -> let (y,st2)  $=$  unT (f x) st1 in unT (g y) st2)) m -- definition of sharp  $= T$  (\s1 -> let (p,s2)  $=$  unT m s1 in unT ((x -> T (\st1 -> let (y,st2)  $=$  unT (f x) st1 in unT (g y) st2)) p) s2 -- beta reduction  $= T$  (\s1 -> let (p,s2)  $=$  unT m s1 in unT (T (\st1 -> let (y,st2)  $=$  unT (f p) st1 in unT (g y) st2)) s2 -- cancel the T/unT pair  $= T$  (\s1 -> let (p,s2)  $=$  unT m s1 in (\st1 -> let (y,st2)  $=$  unT (f p) st1 in unT (g y) st2) s2 -- beta reduction  $= T$  (\s1 -> let (p,s2)  $=$  unT m s1 in let (y,st2)  $=$  unT (f p) s2 in unT (g y) st2 ) -- streamline the let expression  $= T$  (\s1 -> let (p,s2)  $=$  unT m s1 (y,st2)  $=$  unT (f p) s2 in unT (g y) st2 ) -- change the names of local variables  $= T$  (\s1 -> let (v2,s2)  $=$  unT m s1 (v3,s3)  $=$  unT (f v2) s2 in unT (g v3)s3
```

□

Proposition B.10 (compatibility of Applicative and Monad) The following equality holds.

```latex
$\mathrm{mf} <   * > \mathrm{mx} = \mathrm{mf} > > = \backslash \mathrm{f}\Rightarrow \mathrm{mx} > > = \backslash \mathrm{x}\Rightarrow$  return (f x)
```

Proof We rewrite the LHS step by step.

```txt
mf  $<  * >$  mx -- definition of  $<  * >$ $\begin{array}{rl} & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T(\backslash s1\rightarrow)\\ & = T\left(\backslash s1\rightarrow\right)\end{array}$  let (f,s2)  $= \mathrm{unT}$  mf s1  $(x,s3) = \mathrm{unT}$  mx s2 in (f x,s3))   
We calculate subexpressions of the RHS from the innermost. return (f x)  $= T(\backslash s\rightarrow)(f\times ,s))$    
mx  $> = \backslash x - >$  return (f x) -- replace  $(> = )$  with sharp  $=$  sharp ( $x\rightarrow$  T ( $s\rightarrow$  (f x,s))) mx -- definition of sharp  $= T(\backslash t1\rightarrow$  let (y,t2)  $= \mathrm{unT}$  mx t1 in unT ((x->T ( $s\rightarrow$  (f x,s))) y) t2) -- beta reduction  $= T(\backslash t1\rightarrow$  let (y,t2)  $= \mathrm{unT}$  mx t1 in unT (T ( $s\rightarrow$  (f y,s))) t2) -- cancel the T/unT pair  $= T(\backslash t1\rightarrow$  let (y,t2)  $= \mathrm{unT}$  mx t1 in ( $s\rightarrow$  (f y,s)) t2) -- beta reduction  $= T(\backslash t1\rightarrow$  let (y,t2)  $= \mathrm{unT}$  mx t1 in (f y,t2))   
mf  $> = \backslash f\rightarrow$  mx  $>> = \backslash x - >$  return (f x)  $= \mathrm{mf} >> = \backslash f\rightarrow$  T ( $t1\rightarrow$  let (y,t2)  $= \mathrm{unT}$  mx t1 in (f y,t2)) -- replace  $(> = )$  with sharp  $= \mathrm{sharp}$  ( $f\rightarrow$  T (\ $t1\rightarrow$  let (y,t2)  $= \mathrm{unT}$  mx t1 in (f y,t2)) mlf -- definition of sharp  $= T(\backslash s1\rightarrow$  let (v1,s2)  $= \mathrm{unT}$  mf s1 in unT ((f->T (\ $t1\rightarrow$  let (y,t2)  $= \mathrm{unT}$  mx t1 in (f y,t2)) v1
```

```txt
s2) --beta reduction   
 $= \mathrm{T}$  (\s1-> let (v1,s2)  $=$  unT mf s1 in unT (T (\t1 -> let (y,t2)  $=$  unT mx t1 in (v1 y,t2)) s2) --cancel the T/unT pair   
 $= \mathrm{T}$  (\s1-> let (v1,s2)  $=$  unT mf s1 in (\t1-> let (y,t2)  $=$  unT mx t1 in (v1 y,t2)) s2) --beta reduction   
 $= \mathrm{T}$  (\s1-> let (v1,s2)  $=$  unT mf s1 let (y,t2)  $=$  unT mx s2 in (v1 y,t2)) -- streamline the let expression   
 $= \mathrm{T}$  (\s1-> let (v1,s2)  $=$  unT mf s1 (y,t2)  $=$  unT mx s2 in (v1 y,t2)) -- change the names of local variables   
 $= \mathrm{T}$  (\s1-> let (f,s2)  $=$  unT mf s1  $(\mathbf{x},\mathbf{s}3)$ $=$  unT mx s2 in (f x,s3))
```

□

# Appendix C Continuation Passing

In this appendix, we will prove all the equations that are required to establish instances of Functor, Applicative, and Monad type classes in the sample code 6.10 Continuation2.hs.

# C.1 Functor Instance

Proposition C.1 The following equality holds.

fmap id = id

```perl
Proof We will show that the LHS and RHS produce the same result when applied to any h. -- definition of fmap T (\b' -> unT h (b'.id)) -- omit id = T (\b' -> unT h b') -- eta conversion = T $ unT h -- cancel the T/unT pair = h
```

Proposition C.2 The following equality holds.

fmap (g.f) = fmap g . fmap f

```txt
Proof We will show that the LHS and RHS produce the same result when applied to any h. Applying the LHS to h gives the following. fmap  $(\mathbf{g}.f)$ $\mathtt{h} = \mathtt{T}$ $\backslash c^{\prime}\rightarrow$  unT h  $(c^{\prime}.g.f))$  Applying the RHS to h gives the following. fmap g (fmap f h) -- apply definition to the inner fmap  $= \mathrm{fmap~g~(T~(\backslash b^{\prime}\to u n T~h~(b^{\prime}.f))}}$  -- apply definition to the remaining fmap  $= \mathrm{T}$ $\backslash c^{\prime}\rightarrow$  unT  $\mathrm{T}$ $\backslash b^{\prime}\rightarrow$  unT h  $(b^{\prime}.f))$ $(c^{\prime}.g))$  -- cancel the T/unT pair  $= \mathrm{T}$ $\backslash c^{\prime}\rightarrow$ $\backslash b^{\prime}\rightarrow$  unT h  $(b^{\prime}.f))$ $(c^{\prime}.g))$  -- beta reduction  $= \mathrm{T}$ $\backslash c^{\prime}\rightarrow$  unT h  $(c^{\prime}.g.f))$
```

□

# C.2 Applicative Instance

Proposition C.3 The following equality holds.  
```haskell
pure id < $\succ$ > ta = ta Proof We rewrite the LHS step by step. pure id < $\succ$ > ta -- replace pure by eta = eta id < $\succ$ > ta -- definition of eta = T (\aa' -> aa' id) < $\succ$ > ta -- definition of < $\succ$ > = T (\b' -> unT (T (\aa' -> aa' id)) $ \f -> unT ta (b'.f)) -- cancel the T/unT pair = T (\b' -> (\aa' -> aa' id) $ \f -> unT ta (b'.f)) -- beta reduction = T (\b' -> (\f -> unT ta (b'.f)) id) -- beta reduction = T (\b' -> unT ta (b'.id)) -- omit id = T (\b' -> unT ta b') -- eta conversion = T (unT ta) -- cancel the T/unT pair = ta
```

□

Proposition C.4 The following equality holds.

pure (.)< $\gg$  tu  $<\gg$  tv  $<\gg$  tw = tu  $<\gg$  (tv  $<\gg$  tw)

Proof We give general useful remarks.

Remark 1. Function composition operator (. can be defined as follows.

（.）:: (b->c) -> (a->b) -> (a->c)

（.）  $= \backslash \mathrm{g} - > \backslash \mathrm{f} - > \backslash \mathrm{x} - > \mathrm{g}(\mathrm{f}\quad \mathrm{x})$

Remark 2. Function composition sometimes takes the form as follows.

f.  $\left(\backslash x \rightarrow y\right) = \backslash x \rightarrow f y$

We calculate the LHS.

Use a local variable bcabac'.

-- bcabac' : ((b->c) -> (a->b) -> (a->c)) -> v

-- pure (.):: T v ((b->c) -> (a->b) -> (a->c))

We get the following.

pure (.）  $=$  T（\bcbac’  $\rightarrow$  bcbac’(.))

Use local variables tu and abac'.

```txt
-- tu :: T v (b->c)  
-- unT tu :: ((b->c) -> v) -> v  
-- pure (.)< $\ast$ > tu :: T v ((a->b) -> (a->c))  
-- abac' :: ((a->b) -> (a->c)) -> v  
-- abac'.z :: (b->c) -> v  
-- z :: (b->c) -> ((a->b) -> (a->c))
```

We get the following.

```txt
pure (.）  $\text{<  } * >$  tu  $= T$  （bcabac’->bcabac'（.））  $\text{<  } * >$  tu -- definition of  $\text{<  } * >$ $= T$  （abac’  $\rightarrow$  unT（T（bcabac’  $\rightarrow$  bcabac'(..))  $\backslash z\rightarrow$  unTu (abac'.z) -- cancel the T/unT pair   
 $= T$  （abac’  $\rightarrow$  （bcabac’  $\rightarrow$  bcabac'(..))  $\backslash z\rightarrow$  unTu abac'.z) -- beta reduction   
 $= T$  （abac’  $\rightarrow$  （z  $\rightarrow$  unTu abac'.z) (.） -- beta reduction   
 $= T$  （abac’  $\rightarrow$  unTu abac'.(.）） --Remark1   
 $= T$  （abac’  $\rightarrow$  unTu (abac'.(u  $\rightarrow$  v  $\rightarrow$  x  $\rightarrow$  u(vx))） --Remark2
```

```haskell
= T (\abac' -> unT tu
\u -> abac'
\v -> \x -> u (v x) )
Use local variables tu, tv, and g.
-- tv :: T v (a->b)
-- unT tv :: ((a->b)->v) -> v
-- pure (.) <=> tu <=> tv :: T v (a->c)
-- g :: b->c
We get the following.
pure (.) <=> tu <=> tv
= T (\abac' -> unT tu
\u -> abac'
\v -> \x -> u (v x) )
<=> tv
= T (\ac' -> (\abac' -> unT tu
\u -> abac'
\v -> \x -> u (v x) )
\g -> unT tv (ac'. g) )
-- beta reduction
= T (\ac' -> unT tu
\u -> (\g -> unT tv (ac'. g))
\v -> \x -> u (v x) )
-- beta reduction
= T (\ac' -> unT tu
\u -> unT tv
ac'. (\v -> \x -> u (v x)) )
Use local variables tu, tv, and tw.
-- tw :: T v a
-- pure (.) <=> tu <=> tv <=> tw :: T v c
We get the following.
pure (.) <=> tu <=> tv <=> tw
= T (c' -> \ac' -> unT tu
\u -> unT tv
ac'. (\v -> \x -> u (v x)) )
f -> unT tw (c'. f)
-- beta reduction
= T (c' -> unT tu
\u -> unT tv
(f -> unT tw (c'.f)) . (\v -> \x -> u (v x)) )
-- Remark 2
= T (c' -> unT tu
\u -> unT tv
\v -> unT tw $ c'. (\x -> u (v x)) )
-- Remark 2
= T (c' -> unT tu
\u -> unT tv
\v -> unT tw
```

```latex
$\mathrm{x}\rightarrow \mathrm{c}^{\prime}$  u（v x） --beta reduction   
 $= T$  （c’  $\rightharpoondown$  unTtu  $\backslash \mathbf{u}\rightarrow$  unT tv V  $\rightharpoonup$  unT tw c'.u.v)
```

We calculate the RHS.

```txt
Use local variables tv, tw, b', and v. -- tv :: T v (a->b) -- unT tv :: ((a->b)->v) -> v -- tw :: T v a -- unT tw :: (a->v) -> v -- tv < $\ast$ >tw :: T v b -- b' :: b -> v -- v :: a -> b
```

```txt
We get the following tv  $<  * >$  tw  $\equiv$  T  $\backslash \mathsf{b}^{\prime}$  -> unT tv V-> unT tw (b'.v))
```

```txt
Use local variables tu, tv, tw, c', b', and u. -- tu  $<  * >$  (tv  $<  * >$  tw) :: T v c --c' :: c -> v --b' :: b->v --u :: b->c
```

```txt
We get the following.  
tu  $<\ast>$  (tv  $<\ast>$  tw)  
 $= T \backslash c' \rightarrow$  unT tu  
 $\backslash u \rightarrow$  unT (T (\b') -> unT tv  
 $\backslash v \rightarrow$  unT tw  
(c'.u))  
-- cancel the T/unT pair  
 $= T \backslash c' \rightarrow$  unT tu  
 $\backslash u \rightarrow$  (\b') -> unT tv  
 $\backslash v \rightarrow$  unT tw (b'.v)  
(c'.u))  
-- beta reduction  
 $= T \backslash c' \rightarrow$  unT tu  
 $\backslash u \rightarrow$  unT tv  
 $\backslash v \rightarrow$  unT tw  
(c'.u.v))
```

Proposition C.5 (homomorphism) The following equality holds.

pure f  $<  * >$  pure x  $= =$  pure (f x)

Proof Use local variables  $f, x, ab', b', a'$ , and  $g$ .

--f ::a->b  
--x ：：a  
-- pure f :: T v (a->b)  
-- pure x :: T v a  
-- pure (f x) :: T v b  
--ab’  $\because (a - > b)\rightarrow v$  
--b’ ：b->v  
--a' ::a->v  
--g ::a->b

We get the following.

pure f  $<  * >$  pure x  
-- definition of pure  
= T (\ab' -> ab' f) < $\Rightarrow$  T (\a' -> a' x)  
-- definition of  $\langle * \rangle$  
= T (b' -> unT (T (\ab' -> ab' f))  
$\backslash \mathrm{g}\rightarrow$  unT（T（a’->a’x))  
(b'.g)  
-- cancel the T/unT pair  
= T (b' -> (\ab' -> ab' f)  
$\backslash \mathrm{g}\rightarrow (\backslash \mathrm{a}^{\prime} - > \mathrm{a}^{\prime}\quad \mathrm{x})$  
(b'.g)  
-- beta reduction  
= T (b' -> (\ab' -> ab' f)  
$\backslash \mathrm{g}\rightarrow (\mathrm{b}^{\prime}. \mathrm{g})$  
-- beta reduction  
= T (b' -> (\g -> (b'.g) x) f)  
-- beta reduction  
= T (b' -> (b'.f) x)  
= T (b' -> b' (f x))  
-- definition of pure  
= pure (f x)

Proposition C.6 (commutativity) The following equality holds.

u<>pure y \(= =\) pure \((\\) y)\( <>u

Proof Use local variables u, y, a', b', and g.

--u :Tv(a->b)  
--y ：：a  
-- pure y :: T v a  
-- u < $\ast$ > pure y::Tv b  
--a' ::a->v  
--b’ ：：b->v

![](images/8a176bfb4aae76ca2cebe70e9b26da5854e3901a5d354678397be17d7f2e783c.jpg)

--g :a->b

We calculate the LHS.

u  $<  >$  pure y -- definition of pure  $\begin{array}{rl} & = u <   * > T (\backslash a^{\prime}\rightarrow a^{\prime}y)\\ & = T (\backslash b^{\prime}\rightarrow unT u \\ & \qquad \backslash g\rightarrow unT (T (\backslash a^{\prime}\rightarrow a^{\prime}y)) \\ & \qquad \qquad (b^{\prime}.g) \end{array}$  -- definition of  $<  >$  -- cancel the T/unT pair   
 $= T (\backslash b^{\prime}\rightarrow unT u$ $\backslash g\rightarrow (\backslash a^{\prime}\rightarrow a^{\prime}y)$ $(b^{\prime}.g)$  -- beta reduction   
 $= T (\backslash b^{\prime}\rightarrow unT u$ $\backslash g\rightarrow (b^{\prime}.g)y)$ $= T (\backslash b^{\prime}\rightarrow unT u$ $\backslash g\rightarrow b^{\prime}(g y)$

We calculate the RHS.

pure (\( y) < \) u
-- recall (\( y) = \) f -> f y
= pure (\( f -> f y) < \) u
-- definition of pure
= T (\( g -> g (\) f -> f y)) < \) u
-- definition of \( < \) \)
= T (\( b' -> unT (T (\) g -> g (\( f -> f y))) \)
\h -> unT u
(b'.h) )
-- cancel the T/unT pair
= T (\( b' -> (\) g -> g (\( f -> f y)) \)
\h -> unT u (b'.h) )
-- beta reduction
= T (\( b' -> (\) h -> unT u (b'.h)) (\) f -> f y) )
-- beta reduction
= T (\( b' -> unT u \)
b'. (\) f -> f y) )
-- recall Remark 2 on composition b'. (\( f -> f y)
= T (\) b' -> unT u
\h -> b' (f y) )
-- change the name of local variable
= T (\( b' -> unT u
\)g -> b' (g y) )

□

# C.3 Monad Instance

Proposition C.7 (left unit) The following equality holds.

```txt
return  $\mathbf{x} > > = \mathbf{f} = \mathbf{f}$  x
```

```txt
Proof Use local variables f and b'.  
f :: a -> T v b  
b' :: b -> v
```

```haskell
We calculate the LHS.  
return x >= f  
-- definition of return  
= T (\a' -> a' x) >= f  
-- replace (++=) with sharp  
= sharp f $ T (\a' -> a' x)  
-- definition of sharp  
= T (\b' -> unT (T (\a' -> a' x))  
\a -> unT (f a) b')  
-- cancel the T/unT pair  
= T (\b' -> (\a' -> a' x)  
\a -> unT (f a) b')  
-- beta reduction  
= T (\b' -> unT (f x) b')  
-- eta conversion  
= T $ unT (f x)  
= f x
```

Proposition C.8 (right unit) The following equality holds.

```txt
m  $>> =$  return  $\equiv$  m
```

```haskell
Proof Use a local variable m.  
m :: T v a  
return :: a -> T v a  
We calculate the LHS.  
m >= return  
-- replace (\>=) with sharp  
= sharp return m  
-- definition of sharp  
= T (\a' -> unT m  
\a -> unT (return a) a')  
-- definition of return  
= T (\a' -> unT m
```

```latex
$\texttt{a}\rightarrow$  unT (T (\f->f a)) a') -- cancel the T/unT pair   
 $= \mathrm{T}(\backslash \mathrm{a})\rightarrow$  unT m  $\begin{array}{rl} & {\backslash \mathrm{a}\rightarrow (\backslash \mathrm{f}\rightarrow \mathrm{f}\mathrm{a})}\\ & {\qquad \mathrm{a}^{\prime}}) \end{array}$  -- beta reduction   
 $= \mathrm{T}(\backslash \mathrm{a})\rightarrow$  unT m  $\backslash \mathbf{a}\rightarrow \mathbf{a}^{\prime}\mathbf{a})$  -- eta conversion   
 $= \mathrm{T}(\backslash \mathrm{a})\rightarrow$  unT m a') -- eta conversion   
 $= \mathrm{T}$  (unT m) -- cancel the T/unT pair   
 $= \mathrm{m}$
```

Proposition C.9 (associativity) The following equality holds.

```latex
$(\mathfrak{m} > > = \mathfrak{f}) > > = \mathfrak{g} = \mathfrak{m} > > = (\backslash \mathbf{x}\Rightarrow \mathbf{f}\quad \mathbf{x} > > = \mathbf{g})$
```

Proof Use local variables m, f, and g.

```txt
m :: T v a  
f :: a -> T v b  
g :: b -> T v c
```

```haskell
We calculate the LHS.  
(m >> = f) >> = g  
-- replace the first (>>=) with sharp  
= (sharp f m) >> = g  
-- replace the remaining (>>=) with sharp  
= sharp g (sharp f m)  
-- apply the definition to the second appearance of sharp  
= sharp g (T (\b' -> unT m  
\a -> unT (f a) b'))  
-- definition of sharp  
= T (\c' -> (unT (T (\b' -> unT m  
\a -> unT (f a)  
b'))  
\b -> unT (g b) c')  
-- cancel the T/unT pair  
= T (\c' -> (\b' -> unT m  
\a -> unT (f a)  
b')  
\b -> unT (g b) c')  
-- beta reduction  
= T (\c' -> unT m  
\a -> unT (f a)
```

$$
\backslash b \rightarrow \text {u n T} (\text {g} b) c ^ {\prime})
$$

We calculate the RHS. Use local variables  $x$  and  $g$ .

```txt
--x ::a   
--f x::Tvb   
--g ::b->Tvc
```

Begin with the subexpression in the parentheses.

```txt
f x >> = g
    -- replace (>>=) with sharp
    = sharp g(f x)
    -- definition of sharp
    = T(\c' -> unT(f x)
        (\b -> unT(g b) c'))
```

We calculate the whole RHS. Use local variables  $m$ ,  $c'$ , and  $d'$ .

```txt
--  $\backslash x\rightarrow f x > > = g)$  ::a->Tvc   
--m ::Tva   
--c'，d' ::c->v   
m>>=(x->f x>>=g) -- replace  $(\gg =)$  with sharp  $=$  sharp  $\backslash x\rightarrow T$  （c’  $\twoheadrightarrow$  unT(fx) (b  $\twoheadrightarrow$  unT(gb)c））
```

```txt
m -- definition of sharp
```

```txt
= T (\d' -> unT m
    \a -> unT (T (\c' -> unT (f a)
        (\b -> unT (g b)
        c') )
    d')
    -- cancel the T/unT pair
= T (\d' -> unT m
    \a -> (\c' -> unT (f a)
        (\b -> unT (g b)
        c') )
```

```txt
d') --beta reduction   
 $= T(\backslash d^{\prime}\rightarrow \mathrm{unT~m}}$  a -> (unT (fa) (\b -> unT (gb) d')） --change the name of a local variable   
 $= T(\backslash c^{\prime}\rightarrow \mathrm{unT~m}}$  a -> unT (fa) \b -> unT (gb) c')
```

□

# Reference

1. Mac Lane S (1998) Categories for the working mathematician, Graduate texts in mathematics, vol 5, 2nd edn. Springer

# Index

# A

Ab, 9

$\mathcal{A}^{\mathrm{op}}$  ,10

$[\mathcal{A},\mathcal{B}]$  ,35

$\varepsilon_{A}$  ，122

$F\vdash U$  ,120

Grp, 9

$H^{A}$  ,197

Hask, 10

$H_{A}$  ,202

$H^{-}$  ,201

1,9

Set, 9

Top, 9

2, 10

$\eta_{X}$  , 122

$\mathrm{Vect}_k$  ,9

0,9

adjoint equivalence, 141

adjunct, 120

apex, 54, 61

Applicative, 175, 183

arrow, 7

associator, 227

# B

backward path, 253

bifunctor, 229

# C

canonical map, 263

category, 7

category of all monoids, 192

category with coproducts, 59

category with products, 55

characteristic function, 203

class, 7

cocone, 69

codomain, 7

coequalizer, 77

colimit, 70

colimits in Set, 101

composite, 7

computation that may fail, 163

cone, 61

Cones, 62

constant functor, 25

continuation passing, 159

contravariant functor, 16

coones, 70

coproduct, 59, 79

coprojection, 58, 69

cospan, 58

counit, 122

covariant functor, 16

# D

diagonal functor, 148

diagram of shape J, 61

direct product, 67

direct sum, 57, 79

discrete category, 67

disjointunion,57,101

disjoint union with gluing, 73

domain, 7

# E

endofunctor, 152

epimorphism, 138

equalizer, 66

equivalence of categories, 39

essentially surjective, 42

evaluation functor, 207

# F

faithful functor, 18

fiber product, 63

forward path, 253

free monoid, 192

free object, 135

full and faithful functor, 18

full functor, 18

function, 1

function on morphisms, 13

function on objects, 13

Functor, 175

functor category, 35

# G

generator, 11

graph of a relation, 1

# H

havecolimits,80

have limits, 80

# I

identity morphism, 8

index category, 61

initial object, 51

isomorphism, 8

isomorphism of categories, 39

# K

Kleisli triple, 152

# L

large category, 8

left adjoint, 120

limit, 62

limitingcocone,70

limiting cone, 62

limits in Set, 91

List functor, 14

locally small category, 8

# M

mapping, 1

Maybe functor, 14

mediating morphism, 62, 70

Monad, 165, 175

monoid, 192

monoid homomorphism, 192

monoidal category, 227

monoidal functor, 246

monomorphsim, 138

morphism, 7

# N

natural, 120

natural isomorphism, 36

natural transformation, 21

non-deterministic, 154

# 0

opposite category, 10

# P

partial function, 2

pentagoncoherence,228

poset, 10

preserve colimits, 104

preserve limits, 104

principle of duality, 10

product, 55, 67

product category, 12

projection, 61

pullback, 63

pushout, 71

# R

representable, 198, 203

Representation of contravariant functors, 202

Representation of covariant functors, 197

retract, 139

retraction, 139

right adjoint, 120

# S

section, 139

small category, 8

small set, 7, 268

span, 54

split epimorphism, 139

split monomorphism, 139

strict monoidal functor, 246

system of generators, 12

# T

tagged union, 101

terminal object, 51

transposition, 120

Tree functor, 15

trianglecoherence,228

# U

underlying set, 9, 192

unique up to isomorphisms, 56

unit, 122

unit of monoid, 192

unitality constraint, 228

unitor, 228

universalcocone,70

universal cone, 62

universe, 7, 267

# V

vertical composition, 27

# W

with output, 156

# Y

The Yoneda Lemma, 204

Yoneda embedding, 204