
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
    associativeComposition(g) //&&
    // containsInverses(g)
}

predicate ValidSubGroup<A>(g: Group<A>, h: Group<A>) {
    h.elements <= g.elements &&
    g.identity in h.elements &&
    g.identity == h.identity &&
    g.compose == h.compose &&
    closedComposition(h) &&
    containsInverses(h)
}

predicate AbelianGroup<A>(g: Group<A>) {
    ValidGroup(g) && commutativeComposition(g)
}

lemma {:verify true} groupCompositionInverse<A>(g: Group<A>, a: A, b: A, abar: A, bbar: A, abbar: A)
    requires ValidGroup(g)
    requires containsInverses(g)
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

function apow<A>(g: Group, elem: A, n: nat): A
    requires elem in g.elements
{
    if n == 0 then g.identity else g.compose(elem, apow(g, elem, n-1))
}

lemma onePower<A>(g: Group, elem: A)
    requires elem in g.elements
    requires isIdentity(g)
    ensures apow(g, elem, 1) == elem;
{
    calc {
        apow(g, elem, 1);
        g.compose(elem, apow(g, elem, 0));
        g.compose(elem, g.identity);
        elem;
    }
}

lemma apowClosed<A>(g: Group, elem: A, n: nat)
    requires elem in g.elements
    requires g.identity in g.elements
    requires isIdentity(g)
    requires closedComposition(g)
    ensures apow(g,elem, n) in g.elements
{

}

lemma {:verify true} apowAddition<A>(g: Group<A>, elem: A, n: nat, k: nat)
    requires elem in g.elements
    requires ValidGroup(g)
    ensures g.compose(apow(g, elem, n), apow(g, elem, k)) == apow(g, elem, n+k)
{
    apowClosed(g, elem, n);
    apowClosed(g, elem, k);
    if k == 0 {
        assert apow(g, elem, k) == g.identity;
        assert g.compose(apow(g, elem, n), g.identity) == apow(g, elem, n+0);
    }else if n == 0 {
        assert apow(g, elem, n) == g.identity;
        assert g.compose(g.identity, apow(g, elem, k)) == apow(g, elem, k+0);
    }else{
        apowClosed(g, elem, n-1);
        calc {
            g.compose(apow(g, elem, n), apow(g, elem, k));
            g.compose(g.compose(elem, apow(g, elem, n-1)), apow(g, elem, k));
            g.compose(elem, g.compose(apow(g, elem, n-1), apow(g, elem, k)));
            == {apowAddition(g,elem, n-1,k);}
            g.compose(elem, apow(g, elem, n-1+k));
            apow(g, elem, n+k);
        }
    }
}

predicate CyclicGroupGeneratedBy<A(!new)>(g: Group, elem: A)
    requires elem in g.elements
{
    exists n :: n == |g.elements| &&
        apow(g, elem, n) == g.identity &&
        (forall ns :: ns != n && apow(g, elem, ns) == g.identity ==> n < ns) &&
        n != 0 && |g.elements| == n &&
        forall x :: x in g.elements && exists n :: apow(g, elem, n) == x
}

lemma {:verify false} AllSubgroupsOfCyclicSubgroupsAreCyclic<A(!new)>(g: Group, elem: A, h:Group)
    requires elem in g.elements
    requires CyclicGroupGeneratedBy(g, elem)
    requires ValidGroup(g)
    requires h.elements < g.elements
    requires ValidGroup(h)
    requires ValidSubGroup(g, h)
    ensures exists hx: A :: hx in h.elements && CyclicGroupGeneratedBy(h, hx)
{

}