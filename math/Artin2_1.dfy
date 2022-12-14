
//!A signifies type invariance
datatype Group<!A> = Group(elements: set<A>, identity: A, compose: (A,A) -> A)

predicate isIdentity<A>(g: Group<A>) {
    forall a :: a in g.elements ==> g.compose(a,g.identity) == a && g.compose(g.identity, a) == a
}

predicate closedComposition<A>(g: Group<A>) {
    forall x,y :: x in g.elements && y in g.elements ==> g.compose(x,y) in g.elements
}

predicate associativeComposition<A>(g: Group<A>) {
    forall a,b,c :: a in g.elements && b in g.elements && c in g.elements ==> g.compose(g.compose(a,b),c) == g.compose(a, g.compose(b,c))
}

predicate commutativeComposition<A>(g: Group<A>) {
    forall a,b :: a in g.elements && b in g.elements ==> g.compose(a,b) == g.compose(b,a)
}

predicate containsInverses<A>(g: Group<A>) {
    forall x :: x in g.elements ==> exists xbar :: xbar in g.elements && g.compose(x,xbar) == g.identity
}

predicate ValidGroup<A>(g: Group<A>) {
    g.identity in g.elements &&
    isIdentity(g) &&
    closedComposition(g) &&
    associativeComposition(g) && 
    containsInverses(g)
}

predicate AbelianGroup<A>(g: Group<A>) {
    ValidGroup(g) && commutativeComposition(g)
}

lemma groupCompositionInverse<A>(g: Group<A>, a: A, b: A, abar: A, bbar: A, abbar: A) 
    requires ValidGroup(g)
    requires a in g.elements
    requires b in g.elements
    requires abar in g.elements
    requires bbar in g.elements
    requires abbar in g.elements
    requires g.compose(a, abar) == g.identity
    requires g.compose(b, bbar) == g.identity
    requires g.compose(g.compose(a, b), abbar) == g.identity
    ensures abbar == g.compose(bbar, abar)
{
    calc {
        g.compose(g.compose(a, b), g.compose(bbar, abar));
        == 
        g.compose(a, g.compose(g.compose(b, bbar),abar));
        ==
        g.compose(a, g.compose(g.identity,abar));
        ==
        g.compose(a, abar);
        ==
        g.identity;
    }
}