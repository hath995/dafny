include "./gcd.dfy"



module Artin {
    import Math

    function sub(x: int, y: int): int {
        x - y
    }

    lemma prodDistributesSub(a: int, b: int, c: int)
        ensures  Math.prod(a,b) + Math.prod(a,sub(c,b)) == Math.prod(a, c)
    {
        reveal Math.prod();
    }

    lemma prodDistributesMinus(a: int, b: int, c: int)
        ensures Math.prod(a, b - c) == Math.prod(a,b) - Math.prod(a,c)
    {
        reveal Math.prod();
    }

    lemma prodNegative(a: int, b: int)
        ensures -Math.prod(a,b) == Math.prod(-1, Math.prod(a,b))
    {
        reveal Math.prod();
    }

    lemma prodZero(a: int, b: int)
        requires b == 0
        ensures Math.prod(a, b) == 0
    {
        reveal Math.prod();
    }
    //!A signifies type invariance
    datatype Group<!A> = Group(elements: set<A>, identity: A, compose: (A,A) -> A, inverse: (A) -> A)

    ghost predicate isIdentity<A(!new)>(g: Group<A>) {
        forall a :: inGroup(g,a) ==> g.compose(a,g.identity) == a && g.compose(g.identity, a) == a
    }

    lemma GroupIdentity<A>(g: Group<A>, a: A) 
        requires inGroup(g, a)
        ensures g.compose(a,g.identity) == a && g.compose(g.identity, a) == a
    

    ghost predicate closedComposition<A(!new)>(g: Group<A>) {
        // forall x,y :: x in g.elements && y in g.elements ==> g.compose(x,y) in g.elements
        forall x: A, y: A :: inGroup(g,x) && inGroup(g,y) ==> inGroup(g, g.compose(x,y))
    }

    lemma GroupClosedComposition<A>(g: Group<A>, a: A, b: A)
        requires inGroup(g, a)
        requires inGroup(g, b)
        ensures inGroup(g, g.compose(a, b))

    ghost predicate associativeComposition<A(!new)>(g: Group<A>) {
        forall a,b,c :: inGroup(g, a) && inGroup(g, a) && inGroup(g,a) ==> g.compose(g.compose(a,b),c) == g.compose(a, g.compose(b,c))
    }

    lemma GroupAssociativeComposition<A>(g: Group<A>, a: A, b: A, c: A)
        requires inGroup(g, a)
        requires inGroup(g, b)
        requires inGroup(g, c)
        ensures g.compose(g.compose(a,b),c) == g.compose(a, g.compose(b,c))


    ghost predicate commutativeComposition<A(!new)>(g: Group<A>) {
        forall a,b :: inGroup(g, a) && inGroup(g, a) ==> g.compose(a,b) == g.compose(b,a)
    }

    //problematic, aka recursive trigger, it generates new patterns that match the trigger
    ghost predicate containsInverses<A(!new)>(g: Group<A>) {
        forall x :: inGroup(g, x) ==> exists xbar :: inGroup(g, xbar) && g.compose(x,xbar) == g.identity
    }

    lemma GroupContainsInverse<A>(g: Group<A>, x: A)
        requires inGroup(g, x)
        ensures inGroup(g, g.inverse(x))

    predicate PleaseInstantiateMe<A>(x: A) {
        true
    }

    //no longer blocks apowAddition, but doesn't help groupCompositionInverse
    // predicate containsInverses<A>(g: Group<A>) {
    //   forall x {:trigger PleaseInstantiateMe(x)} :: 
    //     PleaseInstantiateMe(x) && x in g.elements ==> 
    //     exists xbar :: 
    //       xbar in g.elements && g.compose(x,xbar) == g.identity
    // }
    ghost predicate closedInverse<A(!new)>(g: Group<A>) {
        // forall x {:trigger g.inverse(x)} :: x in g.elements ==> g.inverse(x) in g.elements
        forall x {:trigger g.inverse(x)} :: inGroup(g,x) ==> inGroup(g,g.inverse(x))
    }

    ghost predicate isInverse<A(!new)>(g: Group<A>) {
        // forall x {:trigger g.inverse(x)} :: x in g.elements ==> g.compose(x,g.inverse(x)) == g.identity && g.compose(g.inverse(x),x) == g.identity
        forall x {:trigger g.inverse(x)} :: inGroup(g,x) ==> g.compose(x,g.inverse(x)) == g.identity && g.compose(g.inverse(x),x) == g.identity
    }
    
    lemma GroupInverse<A>(g: Group<A>, x: A)
        requires inGroup(g, x)
        ensures g.compose(x,g.inverse(x)) == g.identity && g.compose(g.inverse(x),x) == g.identity


    lemma areInverses<A>(g: Group<A>, a: A,  b: A)
        requires ValidGroup(g)
        requires a in g.elements && b in g.elements
        requires inGroup(g,a) && inGroup(g,b)
        requires g.compose(a, b) == g.identity && g.compose(b,a) == g.identity
        ensures g.inverse(a) == b && g.inverse(b) == a
    {
        var x := g.inverse(b);
        calc {
            g.compose(g.compose(a,b), x);
            g.compose(a, g.compose(b,x));
        }
    }

    ghost predicate ValidGroup<A(!new)>(g: Group<A>) {
        // g.identity in g.elements &&
        inGroup(g, g.identity) &&
        isIdentity(g) &&
        closedComposition(g) &&
        associativeComposition(g) &&
        closedInverse(g) &&
        isInverse(g)
        // containsInverses(g)
    }

    ghost predicate ValidSubGroup<A(!new)>(g: Group<A>, h: Group<A>) {
        h.elements <= g.elements &&
        g.identity in h.elements &&
        g.identity == h.identity &&
        g.compose == h.compose &&
        closedComposition(h) //&&
        // containsInverses(h)
    }

    ghost predicate AbelianGroup<A(!new)>(g: Group<A>) {
        ValidGroup(g) && commutativeComposition(g)
    }

    lemma {:verify true} groupCompositionInverse<A>(g: Group<A>, a: A, b: A, abar: A, bbar: A, abbar: A)
        requires ValidGroup(g)
        requires inGroup(g, a)
        requires inGroup(g,b)
        requires g.inverse(a) == abar
        requires g.inverse(b) == bbar
        requires g.inverse(g.compose(a,b)) == abbar
        ensures abbar == g.compose(bbar, abar)
    {
        // calc {
        //     g.compose(g.compose(a, b), g.compose(bbar, abar));
        //     ==
        //     g.compose(a, g.compose(g.compose(b, bbar),abar));
        //     ==
        //     g.compose(a, g.compose(g.identity,abar));
        //     ==
        //     g.compose(a, abar);
        //     ==
        //     g.identity;
        // }
    }
    /*
function realExp(r: real, e: int): real decreases if e > 0 then e else -e {
  if e == 0 then r
  else if e < 0 then realExp(r/10.0, e+1)
  else realExp(r*10.0, e-1)
}
    */

    //apow is short for abstract power
    function apow<A>(g: Group, elem: A, n: int): A
        decreases if n > 0 then n else -n
        ensures n == 0 ==> apow(g,elem,n) == g.identity
    {
        if n == 0 then g.identity else if n > 0 then g.compose(elem, apow(g, elem, n-1)) else if n < 0 then g.compose(g.inverse(elem), apow(g, elem, n+1)) else g.identity
    }

    lemma apowPos<A>(g: Group, elem: A, n: int)
        requires n > 0
        ensures n > 0 ==> apow(g,elem,n) == g.compose(elem, apow(g, elem, n-1))
    {}

    lemma apowNegative<A>(g: Group, elem: A, n: int)
        requires !(n > 0)
        ensures n < 0 ==> apow(g,elem,n) == g.compose(g.inverse(elem), apow(g, elem, n+1))
    {}


    lemma onePower<A>(g: Group, elem: A)
        requires elem in g.elements
        requires isIdentity(g)
        ensures apow(g, elem, 1) == elem
    {
        calc {
            apow(g, elem, 1);
            g.compose(elem, apow(g, elem, 0));
            g.compose(elem, g.identity);
            elem;
        }
    }

    lemma oneMinusPower<A>(g: Group, elem: A)
        // requires elem in g.elements
        requires inGroup(g, elem)
        // requires isIdentity(g)
        // requires closedInverse(g) && isInverse(g)
        ensures apow(g, elem, -1) == g.inverse(elem)
    {
        GroupContainsInverse(g, elem);
        calc {
            apow(g, elem, -1);
            g.compose(g.inverse(elem), apow(g, elem, 0));
            g.compose(g.inverse(elem), g.identity);
            == {GroupIdentity(g, g.inverse(elem));}
            g.inverse(elem);
        }
    }

    lemma {:verify true} apowClosed<A>(g: Group, elem: A, n: int)
        // requires elem in g.elements
        // requires g.identity in g.elements
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        // requires isIdentity(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires isInverse(g)
        // requires n >= 0
        decreases n*n
        ensures inGroup(g, apow(g, elem, n))
    {
        if n == 0 {
            assert apow(g, elem, 0) in g.elements;
        } else if n > 0 {
            apowPos(g, elem, n);
            apowClosed(g, elem, n-1);
            GroupClosedComposition(g, elem, apow(g, elem, n-1));
        }else {
            apowNegative(g,elem, n);
            apowClosed(g, elem, n+1);
            assert apow(g, elem, n+1) in g.elements;
            assert elem in g.elements;
            GroupContainsInverse(g, elem);
            GroupClosedComposition(g, g.inverse(elem), apow(g, elem, n+1));
            // calc {
            //     apow(g, elem, n);
            //     g.compose(g.inverse(elem), )
            // }
            assert apow(g, elem, n) in g.elements;
        }
}

    predicate inGroup<A>(g: Group, elem: A) {
        elem in g.elements
    }

    lemma {:verify true} allApowClosed<A>(g: Group, elem: A) 
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires g.identity in g.elements
        // requires elem in g.elements
        requires inGroup(g, g.identity)
        requires inGroup(g, elem)
        ensures forall x: int :: inGroup(g, apow(g, elem, x))
    {
        forall x: int | true 
        {
            apowClosed(g, elem, x);
        }
    }

    // method {:verify true} apowSubtract<A>(g: Group<A>, elem: A, n: int)
    lemma {:verify } {:induction false} apowSubtract<A(!new)>(g: Group<A>, elem: A, n: int)
        // requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires associativeComposition(g)
        // requires isIdentity(g)
        // requires isInverse(g)
        // requires g.identity in g.elements
        // requires elem in g.elements
        requires inGroup(g, g.identity)
        requires inGroup(g, elem)
        requires n >= 0
        // ensures g.compose(apow(g, elem, n), apow(g, elem, -1)) == apow(g, elem, n-1)
        ensures g.compose(apow(g, elem, -1), apow(g, elem, n)) == apow(g, elem, n-1)
    {
        allApowClosed(g, elem);
        assert inGroup(g, apow(g, elem, -1));
        assert inGroup(g, apow(g, elem, n));
        assert inGroup(g, apow(g, elem, n-1));
        assert inGroup(g, g.identity);
        if n > 0 {
            calc {
                g.compose(apow(g, elem, -1), apow(g, elem, n));
                == {apowPos(g,elem, n);}
                g.compose(apow(g, elem, -1), g.compose(elem, apow(g, elem, n-1)));
                == {GroupAssociativeComposition(g,apow(g, elem, -1), elem, apow(g, elem, n-1));}
                g.compose(g.compose(apow(g, elem, -1), elem), apow(g, elem, n-1));
                == {oneMinusPower(g, elem);}
                g.compose(g.compose(g.inverse(elem), elem), apow(g, elem, n-1));
                == {GroupInverse(g, elem);}
                g.compose(g.identity, apow(g, elem, n-1));
                == {GroupIdentity(g, apow(g, elem, n-1));}
                apow(g, elem, n-1);
            }
        }else if n == 0 {
            calc {
                g.compose(apow(g, elem, -1), apow(g, elem, 0));
                g.compose(apow(g, elem, -1), g.identity);
                == {GroupIdentity(g, apow(g, elem, -1));}
                apow(g, elem, -1);
            }
        }else{
            assert n < 0;
            assert (n-1)+1 == n;
            calc {
                g.compose(apow(g, elem, -1), apow(g, elem, n));
                == {oneMinusPower(g, elem);}
                g.compose(g.inverse(elem), apow(g, elem, n));
                apow(g, elem, n-1);
            }
        }
    }

    lemma apowAdditionAxiom<A>(g: Group<A>, elem: A, n: int, k: int)
        ensures g.compose(apow(g, elem, n), apow(g, elem, k)) == apow(g, elem, n+k)

    lemma apowAdditionAxiomNeg<A>(g: Group<A>, elem: A, n: int, k: int)
        ensures g.compose(apow(g, elem, -n), apow(g, elem, -k)) == apow(g, elem, -n-k)

    lemma {:verify true} apowAddition<A>(g: Group<A>, elem: A, n: nat, k: nat)
        // requires elem in g.elements
        // requires g.identity in g.elements
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        // requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires inGroup(g, g.identity)
        // requires isIdentity(g)
        // requires associativeComposition(g)
        ensures g.compose(apow(g, elem, n), apow(g, elem, k)) == apow(g, elem, n+k)
    {
        allApowClosed(g, elem);
        if k == 0 {
            assert apow(g, elem, k) == g.identity;
            calc {
                apow(g, elem, n+k);
                apow(g, elem, n);
            }
            GroupIdentity(g, apow(g, elem, n));
            assert g.compose(apow(g, elem, n), g.identity) == apow(g, elem, n+k);
        }else if n == 0 {
            assert apow(g, elem, n) == g.identity;
            GroupIdentity(g, apow(g, elem, k));
            assert g.compose(g.identity, apow(g, elem, k)) == apow(g, elem, n+k);
        }else if n > 0 {
            apowPos(g,elem, n);
            calc {
                g.compose(apow(g, elem, n), apow(g, elem, k));
                g.compose(g.compose(elem, apow(g, elem, n-1)), apow(g, elem, k));
                == {GroupAssociativeComposition(g, elem, apow(g, elem, n-1), apow(g, elem, k));}
                g.compose(elem, g.compose(apow(g, elem, n-1), apow(g, elem, k)));
                == {apowAddition(g,elem, n-1,k);}
                g.compose(elem, apow(g, elem, n-1+k));
                apow(g, elem, n+k);
            }
        }
    }

    lemma apowInverse<A>(g: Group<A>, elem: A, n: int)
        requires elem in g.elements
        requires n >= 0
        requires ValidGroup(g)
        // ensures g.inverse(apow(g,elem, n)) == apow(g, elem, -n)
    {
        if n == 0 {
            assert apow(g, elem, n) == g.identity;
            assert apow(g, elem, -n) == g.identity;
            assert g.inverse(g.identity) == g.identity;
        }else if n == 1 {
            apowNegative(g, elem, -1);
            // calc {
            //     apow(g, elem, -n);
            //     apow(g, elem, -1);
            //     g.compose(g.inverse(elem), apow(g, elem, 0));
            // }
            assert g.inverse(apow(g,elem, n)) == apow(g, elem, -n);
        }else{
            calc {
                g.inverse(apow(g, elem, n));
                g.inverse(g.compose(elem, apow(g, elem, n-1)));
            }
        }
    }

    lemma {:verify false} apowAdditionInt<A>(g: Group<A>, elem: A, n: int, k: int)
        requires elem in g.elements
        // requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        requires g.identity in g.elements
        requires isIdentity(g)
        requires associativeComposition(g)
        // ensures g.compose(apow(g, elem, n), apow(g, elem, k)) == apow(g, elem, n+k)
    {
        // allApowClosed(g, elem);
        if k == 0 {
            assert apow(g, elem, k) == g.identity;
            // assert g.compose(apow(g, elem, n), g.identity) == apow(g, elem, n+k);
        }else if n == 0 {
            assert apow(g, elem, n) == g.identity;
            // assert g.compose(g.identity, apow(g, elem, k)) == apow(g, elem, n+k);
        }else if n > 0 && k > 0 {
            apowPos(g, elem, n);
            apowPos(g, elem, n+k);
            assert apow(g, elem, n-1) in g.elements;
            assert apow(g, elem, k) in g.elements;
            assert apow(g, elem, n+k) in g.elements;
            assume g.compose(elem, g.compose(apow(g, elem, n-1), apow(g, elem, k))) == g.compose(elem, apow(g, elem, n-1+k));
            calc {
                g.compose(apow(g, elem, n), apow(g, elem, k));
                g.compose(g.compose(elem, apow(g, elem, n-1)), apow(g, elem, k));
                g.compose(elem, g.compose(apow(g, elem, n-1), apow(g, elem, k)));
                // == {apowAdditionInt(g,elem, n-1,k);}
                g.compose(elem, apow(g, elem, n-1+k));
                apow(g, elem, n+k);
            }
        // }else{

        }else if n > 0  && k < 0 {
            var q := n+k;
            if n+k >= 0 {

            }else if n+k < 0 {
                var z :| 0 - z == q;
                assert k == -n-z;
                assert z > 0;
                calc {
                    g.compose(apow(g, elem, n), apow(g, elem, k));
                    g.compose(apow(g, elem, n), apow(g, elem, -n-z));
                    == {apowAdditionAxiomNeg(g, elem, n, z);}
                    g.compose(apow(g, elem, n), g.compose(apow(g, elem, -n), apow(g, elem, -z)));
                    g.compose(g.compose(apow(g, elem, n), apow(g, elem, -n)), apow(g, elem, -z));
                    == {apowAdditionAxiom(g, elem, n,-n);}
                    g.compose(apow(g, elem, n-n), apow(g, elem, -z));
                    g.compose(apow(g, elem, 0), apow(g, elem, -z));
                    g.compose(g.identity, apow(g, elem, -z));
                    apow(g, elem, -z);
                }
            }
        }else if n < 0 && k > 0 {
            var q := n+k;

        }else if n < 0 && k < 0 {

        }
    }

    lemma positiveNumbersArePositive(k: nat, s: nat)
        requires k >= 0
        requires s >= 0
        ensures Math.prod(k , s) >= 0
    {
        reveal Math.prod();
    }

    lemma positiveNumbersAreStilPositive(k: nat, s: nat, x: nat, y: nat)
        requires k >= 0
        requires s >= 0
        requires x >= 0
        requires y >= 0
        ensures Math.prod(k , s) + Math.prod(x,y) >= 0
    {
        positiveNumbersArePositive(k,s);
        positiveNumbersArePositive(x,y);
        // reveal Math.prod();
    }

    lemma apowSub<A>(g: Group, elem: A, x: int, y: int)
        requires x - y == sub(x,y)
        ensures apow(g, elem, x-y) == apow(g, elem, sub(x,y))
    {

    }

    lemma apowAdd<A>(g: Group, elem: A, k: int, x: int, y: int)
        ensures apow(g, elem, k+Math.prod(x,y)) == apow(g, elem, Math.prod(k,1) + Math.prod(x,y))
    {
        Math.prodIdentity(k);
    }

    lemma apowReduce<A>(g: Group, elem: A, k: nat, s: nat) 
        requires s >= 1
        ensures apow(g, elem, k+Math.prod(k,sub(s,1))) == apow(g, elem, Math.prod(k,s))
    {
        Math.prodIdentity(k);
        assert k + Math.prod(k, sub(s,1)) == Math.prod(k,1) + Math.prod(k, sub(s,1));
        calc {
            apow(g, elem, k+Math.prod(k,sub(s,1)));
            apow(g, elem, Math.prod(k,1) + Math.prod(k, sub(s,1)));
            == {prodDistributesSub(k, 1, s);}
            apow(g, elem, Math.prod(k, s));
        }

    }

    lemma {:verify }  something<A>(g: Group<A>, elem: A, k: nat, s: nat)
        requires elem in g.elements
        // requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        requires g.identity in g.elements
        // requires isIdentity(g)
        // requires associativeComposition(g)
        requires s >= 1
        // ensures g.compose(apow(g, elem, k), apow(g, elem, k*(s-1))) == apow(g, elem, k + k*(s-1))
         ensures g.compose(apow(g, elem, k), apow(g, elem, Math.prod(k,(s-1)))) == apow(g, elem, k+Math.prod(k,(s-1)))
    {
        reveal Math.prod();
        assert Math.prod(k, (s-1)) >= 0;
        apowAddition(g, elem, k, Math.prod(k,(s-1)));
    }

    lemma something2<A>(g: Group<A>, elem: A, k: nat, s: nat)
        requires s >= 1
        ensures apow(g, elem, k*s) == apow(g, elem, k + k*(s-1))
    {
        // assert k+k*(s-1) == k * s;
    }

    lemma {:verify false}  apowExponentNat<A>(g: Group<A>, elem: A, k: nat, s: nat)
        requires elem in g.elements
        // requires ValidGroup(g)
        requires closedComposition(g)
        requires closedInverse(g)
        requires g.identity in g.elements
        requires isIdentity(g)
        requires associativeComposition(g)
        ensures apow(g, apow(g, elem, k), s) == apow(g, elem, k*s)
    {
        if s == 0 {
            // assert k * s == 0;
            // assert s == 0;
            // assert apow(g,apow(g,elem,k),s) == g.identity;
        }else if s > 0 {
            // assume apow(g, apow(g, elem, k), s-1) == apow(g, elem, k*(s-1));
            calc {
                apow(g, apow(g, elem, k), s);
                g.compose(apow(g, elem, k), apow(g, apow(g, elem, k), s-1));
                == {apowExponentNat(g, elem, k, (s-1));}
                g.compose(apow(g, elem, k), apow(g, elem, k*(s-1)));
                == {something(g,elem, k, s);}
                // == {apowAddition(g, elem, k, k*(s-1));}
                apow(g, elem, k+k*(s-1));
                == {something2(g, elem,k,s);} //will verify without this but will do it slower
                apow(g, elem, k*s);
            }
        }
    }

    lemma {:verify }  apowExponent<A>(g: Group<A>, elem: A, k: nat, s: nat)
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        // requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires inGroup(g, g.identity)
        // requires isIdentity(g)
        // requires associativeComposition(g)
        // ensures apow(g, apow(g, elem, k), s) == apow(g, elem, k*s);
        ensures apow(g, apow(g, elem, k), s) == apow(g, elem, Math.prod(k,s))
    {
        allApowClosed(g,elem);
        allApowClosed(g,apow(g,elem, k));
        if s == 0 {
            assert k * s == 0;
            assert s == 0;
            assert apow(g,apow(g,elem,k),s) == g.identity;
            prodZero(k,s);
            assert Math.prod(k,s) == 0;
        }else if s > 0 {
            positiveNumbersArePositive(k, s);
            positiveNumbersArePositive(k, sub(s,1));
            positiveNumbersAreStilPositive(k,1,k,sub(s,1));
            assert Math.prod(k,1)+Math.prod(k,sub(s,1)) >= 0;
            // // assume apow(g, apow(g, elem, k), sub(s,1)) == apow(g, elem, Math.prod(k,sub(s,1)));
            assert k + Math.prod(k,sub(s,1)) >=0;
            calc {
                apow(g, apow(g, elem, k), s);
                g.compose(apow(g, elem, k), apow(g, apow(g, elem, k), s-1));
                == {apowSub(g, apow(g, elem, k), s, 1);}
                g.compose(apow(g, elem, k), apow(g, apow(g, elem, k), sub(s,1)));
                == {apowExponent(g, elem, k, sub(s,1));}
                g.compose(apow(g, elem, k), apow(g, elem, Math.prod(k,sub(s,1))));
                == {apowAddition(g,elem, k, Math.prod(k,sub(s,1)));}
                apow(g, elem, k+Math.prod(k,sub(s,1)));
                 == {apowReduce(g, elem, k, s);}
                apow(g, elem, Math.prod(k,s));
            }
        }
    }
    /**
            // assert k >= 0;
            // assert s > 0;
            // assert s >= 0;
            // assert s-1 >= 0;
            // var one: nat := 1;
            // positiveNumbersArePositive(k, one);
            // assert Math.prod(k,s-1) >= 0;
            // assert Math.prod(k,s) >= 0;
            // assert Math.prod(k,1) + Math.prod(k,s-1) >= 0;
            // assert k + Math.prod(k,s-1) >= 0;
            // assert apow(g, elem, k) in g.elements;
            // assert apow(g, elem, Math.prod(k,s-1)) in g.elements;
            // assert apow(g, elem, k+Math.prod(k,s-1)) in g.elements;
            // assert apow(g, elem, Math.prod(k,1)+Math.prod(k, s-1)) in g.elements;
            // positiveNumbersArePositive(k, s-1);
            // assume sub(s,1) >= 0;
            // assert sub(s,1) == s-1;
                // apow(g, elem, k+Math.prod(k, s-1));
                // == {apowAdd(g, elem, k,k,sub(s,1));}
                // apow(g, elem, Math.prod(k,1)+Math.prod(k,sub(s,1)));
                // apow(g, elem, Math.prod(k,1)+Math.prod(k, s-1));
                // == {Math.prodDistributes(k, 1, s-1);}
                // apow(g, elem, Math.prod(k,1+s-1));
                // apow(g, elem, Math.prod(k, s));
            //     apow(g, elem, k+k*s-k);
            //     apow(g, elem, k+k*s-k);
            //     apow(g, elem, k*s);
            // var bz:nat := Math.prod(k, sub(s,1));
            // calc {
            //     k+bz;
            //     k+Math.prod(k, sub(s,1));
            //     == {Math.prodIdentity(k);}
            //     Math.prod(k,1)+Math.prod(k, sub(s,1));
            //     // Math.prod(k,1)+Math.prod(k, sub(s,1));
            //     == {prodDistributesSub(k, 1, s);}
            //     Math.prod(k, s);
            // }
     */

    ghost predicate CyclicGroupGeneratedBy<A(!new)>(g: Group, elem: A)
        requires elem in g.elements
    {
        exists n :: n == |g.elements| &&
            apow(g, elem, n) == g.identity &&
            (forall ns :: ns != n && apow(g, elem, ns) == g.identity ==> n < ns) &&
            n != 0 &&
            forall x :: x in g.elements && exists n :: apow(g, elem, n) == x
    }

    ghost predicate isIsomorphism<A,B>(g: Group<A>, g': Group<B>, phi: A -> B)
        requires ValidGroup(g)
        requires ValidGroup(g')
    {
        phi(g.identity) == g'.identity &&
        forall x :: x in g.elements ==> (phi(x) in g'.elements &&
        forall x,y :: x in g.elements && y in g.elements ==> phi(g.compose(x,y)) == g'.compose(phi(x), phi(y)))
    }

    lemma Artin2_3_b<A,B>(g: Group<A>, g': Group<B>, phi: A -> B, x: A, y: A) 
        requires ValidGroup(g)
        requires ValidGroup(g')
        requires isIsomorphism(g, g', phi)
        requires x in g.elements && y in g.elements
        requires g.compose(x, g.compose(y,x)) == g.compose(y, g.compose(x, y))
        ensures g'.compose(phi(x), g'.compose(phi(y), phi(x))) == g'.compose(phi(y), g'.compose(phi(x), phi(y)))
    {

    }

    lemma Artin2_3_c<A,B>(g: Group<A>, g': Group<B>, phi: A -> B, x: A) 
        requires ValidGroup(g)
        requires ValidGroup(g')
        requires isIsomorphism(g, g', phi)
        requires x in g.elements
        ensures g'.inverse(phi(x)) == phi(g.inverse(x))
    {

        assert g.compose(x, g.inverse(x)) == g.identity;
        assert g'.compose(phi(x), phi(g.inverse(x))) == phi(g.identity) == g'.identity;
        assert g.compose(g.inverse(x), x) == g.identity;
        assert g'.compose(phi(g.inverse(x)), phi(x)) == phi(g.identity) == g'.identity;
        areInverses(g',phi(g.inverse(x)), phi(x));
    }

    lemma {:verify false} AllSubgroupsOfCyclicSubgroupsAreCyclic<A(!new)>(g: Group, elem: A, h:Group)
        requires elem in g.elements
        requires CyclicGroupGeneratedBy(g, elem)
        requires ValidGroup(g)
        requires h.elements <= g.elements
        requires ValidGroup(h)
        requires ValidSubGroup(g, h)
        ensures exists hx: A :: hx in h.elements && CyclicGroupGeneratedBy(h, hx)
    {

    }

    export reveals *
}