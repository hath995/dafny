

function Range<T, U>(f: T -> U, A: set<T>): set<U> {
    set x | x in A :: f(x)
}
ghost predicate Injective<A(!new), B>(f: A -> B)
{
    forall x, y :: x != y ==> f(x) != f(y)
}
ghost predicate isTotal<G(!new), B(!new)>(f:G -> B)
    reads f.reads;
{
     forall g:G :: f.requires(g)
}

ghost predicate Surjective<A(!new), B(!new)>(f: A -> B) 
    reads f.reads;
    // requires isTotal(f)
{
    forall b: B :: exists a: A :: f(a) == b 
}

lemma exercise1_5<T>(A: set<T>, B: set<T>)
    requires A + B == A
    ensures B <= A
{

}

ghost predicate Bijective<A(!new), B(!new)>(f: A -> B) 
{
    Injective(f) && Surjective(f)
}

lemma exercise1_6<T,U>(f: T  -> U, f_inv: U -> T, B: set<U>)
    requires forall u: U :: f(f_inv(u)) == u
    ensures Range(f, Range(f_inv, B)) <= B
{

}

lemma exercise1_6c<T,U>(f: T  -> U, f_inv: U -> T, A: set<T>)
    // requires forall u: U :: f(f_inv(u)) == u
    requires forall a: T :: a in A ==> f_inv(f(a)) == a
    ensures A <= Range(f_inv, Range(f, A))
{

}

lemma exercise1_7<X(!new), Y(!new)>(f: X -> Y, g: Y -> X)
    requires forall x: X :: g(f(x)) == x
    ensures Injective(f) && Surjective(g)
{
    if !Injective(f) {
        var x,y: X :| x != y && f(x) == f(y);
        assert g(f(x)) == g(f(y));
        assert false;
    } else if !Surjective(g) {
        // assert exists b: Y :: !(exists a: X :: f(a) == b);
        // assert !(forall b: X :: exists a: Y :: g(a) == b);
        // var b: X :| !(exists a: Y :: g(a) == b);
        var b: X :| forall a: Y :: g(a) != b;
        assert g(f(b)) != b;
        assert false;
    }
}

function sub(a: real, b: real): real {
    a - b
}

function add(a: real, b: real): real {
    a+b
}

function prod(a: real, b: real): real {
    a * b
}

ghost predicate upperBound(A: iset<real>, a: real) {
    forall x :: x in A ==> x <= a    
}

ghost predicate lowerBound(A: iset<real>, b: real) {
    forall x :: x in A ==> x >= b
}

ghost predicate leastUpperBound(A: iset<real>, a: real) 
{
    forall epsilon: real :: epsilon > 0.0 ==> !upperBound(A, sub(a, epsilon))  
}

ghost predicate greatestLeastBound(A: iset<real>, b: real) {
    forall epsilon: real :: epsilon > 0.0 ==> !lowerBound(A, add(b , epsilon))  
}

ghost predicate sup(A: iset<real>, a: real) {
    upperBound(A, a) && leastUpperBound(A, a)
}

ghost predicate inf(A: iset<real>, b: real) {
    lowerBound(A, b) && greatestLeastBound(A, b)
}

ghost predicate minimalElement(A: iset<real>, a: real) {
    a in A && lowerBound(A, a)
}

ghost predicate maximalElement(A: iset<real>, a: real) {
    a in A && upperBound(A, a)
}

lemma example1_25(A: iset<real>)
    requires A == iset x: real | x < 0.0
    ensures sup(A, 0.0)
{
    assert forall x: real :: x in A ==> x < 0.0;
    assert upperBound(A, 0.0);
    forall epsilon: real | epsilon > 0.0
        ensures !upperBound(A, sub(0.0,epsilon))
    {
        calc ==> {
            epsilon > 0.0;
            - epsilon > -2.0 * epsilon;
            (- epsilon)/2.0 > -epsilon;
        }
        assert (-epsilon)/2.0 in A;
        assert (-epsilon)/2.0 > sub(0.0,epsilon);
        // assert !upperBound(A, )
    }
    assert leastUpperBound(A, 0.0);
}

lemma CompletenessAxiomUpper(A: iset<real>, a: real)
    requires exists p: real :: p in A 
    requires upperBound(A, a)
    // ensures exists k: real :: leastUpperBound(A, k) && upperBound(A, k)
    ensures exists k: real :: sup(A, k)

lemma CompletenessAxiomLower(A: iset<real>, a: real)
    requires exists p: real :: p in A 
    requires lowerBound(A, a)
    // ensures exists k: real :: greatestLeastBound(A, k) && lowerBound(A, k)
    ensures exists k: real :: inf(A, k)

predicate greaterThan(n: nat, x: real) {
    n as real > x
}

predicate lessThan(n: nat, x: real) {
    n as real < x
}

predicate lessThanEqual(n: nat, x: real) {
    n as real <= x
}

lemma stillInt(x: real) 
    requires x.Floor as real == x;
    ensures sub(x, 1.0).Floor as real == sub(x, 1.0)
{
    var m: int := x.Floor;
    assert (m-1) as real == sub(x, 1.0);
}

lemma stillIntPlus(x: real) 
    requires x.Floor as real == x;
    ensures add(x, 1.0).Floor as real == add(x, 1.0)
{
    var m: int := x.Floor;
    assert (m+1) as real == add(x, 1.0);
}

lemma floorNaturals(nats: iset<real>)
    requires forall x :: x in nats ==> exists k: nat :: k as real == x
    ensures forall x :: x in nats ==> x.Floor as real == x
{

}

type pos = x: nat | 1 <= x witness 1
lemma ArchProof(x: real, a: real, b: real)
    requires a > 0.0
    requires x == b/a
    ensures exists n: pos :: n as real > x
{
    if x < 0.0 {
        assert 1 as real > x;
    }else{
        assert b >= 0.0;
        if forall n: pos :: n as real <= x {
            var naturals: iset<real> := iset ns: nat | lessThanEqual(ns, x) :: ns as real;
            // assert upperBound(naturals, x);
            if x <= 1.0 {
                assert 2 as real > x;
                assert false;
            }else{
                assert lessThanEqual(1, x);
                assert 1.0 in naturals;
            }
            CompletenessAxiomUpper(naturals, x);
            var alpha: real :| leastUpperBound(naturals, alpha as real) && upperBound(naturals, alpha as real); 
            var mp: nat := add(alpha , 1.0).Floor;
            assert lessThanEqual(mp, x);
            assert mp as real in naturals;
            assert upperBound(naturals, mp as real);

            assert false;
        }
    }
}
/*
Alt formulation of the branch
    // var kk: nat := x.Floor + 1;
    // calc ==> {
    //     kk as real > x;
    //     (kk ) as real > b/a;
    //     {what(kk, a, b);}
    //     kk as real * a > b;
    // }
    // assert (kk ) as real > x;
    // assert (kk ) as real > b/a;
    // assert prod(kk  as real, a) > b;
*/

/**
extra bits
    // assert n >= 1;
    // assert 1 as real < x;
    // assume alpha in naturals;
    // assert alpha < x;
    // assert alpha.Floor as real == alpha ;
    // assert 1.0 > 0.0;
    // assert alpha in naturals;
    // var m := sub(alpha, 1.0);
    // assert m < x;
    // assert mp as real > alpha;
    // assert mp as real <= x;
    // assert m.Floor as real == m;
    // assert m in naturals;
    // assert !upperBound(naturals, m);
    // assert lessThanEqual(m.Floor, x);
    // assert lessThan(m.Floor+1, x);
    // assert m as real in naturals;
    // assert (m + 1) as real > alpha ;
    // assert m as real == sub(alpha, 1.0);
    assert upperBound(naturals, alpha as real);
    assert leastUpperBound(naturals, alpha as real);
    assert forall epsilon: real :: epsilon > 0.0 ==> !upperBound(naturals, sub(alpha as real, epsilon));
 */

lemma ArchimedeanPrinciple(epsilon: real)
    requires epsilon > 0.0
    ensures exists n: pos :: 1.0 / (n as real) < epsilon
{
    ArchProof(1.0 / epsilon, epsilon, 1.0);
    var n: pos :| n as real > 1.0 / epsilon;
    calc ==> {
        n as real > 1.0 / epsilon;
        {assert (n as real) *  epsilon > (1.0/epsilon)*epsilon;}
        (n as real) * epsilon > 1.0;
        epsilon > 1.0 / (n as real);
    }
}

lemma exercise1_23(A: iset<real>, B: iset<real>, abound: real, bbound: real, epsilon: real)
    requires A <= B
    requires sup(A, abound)
    requires sup(B, bbound)
    requires epsilon > 0.0
    ensures abound <= bbound
{
  if abound > bbound {
    var myepsilon := abound - bbound;
    assert bbound == sub(abound, myepsilon);
    assert upperBound(A, bbound);
    assert upperBound(A, sub(abound, myepsilon));
    assert  false;
  }
}

/*
    // var apoint := sub(abound, epsilon);
    // var bpoint := sub(bbound, epsilon);
    // assert !upperBound(A, apoint);
    // assert !upperBound(A, bpoint);
    // assert !upperBound(B, apoint);
    // assert !upperBound(B, bpoint);
    // assert apoint > bpoint;
    // var k: real :| k in A && k > apoint && k < abound;
    // assert upperBound(B, abound);
    // assert k in B;
*/

function e29(n: nat): real {
    (n as real)/(n as real + 1.0)
}

lemma exercise1_29a(A: iset<real>)
    requires A == iset n: pos :: e29(n)
    ensures sup(A, 1.0)
{
    assert upperBound(A, 1.0);
    forall epsilon: real | epsilon > 0.0 
        ensures !upperBound(A, sub(1.0, epsilon))
    {
        ArchimedeanPrinciple(epsilon);
        var n: pos :| 1.0 / (n as real) < epsilon; 
        assert (1.0 / (n as real + 1.0)) < 1.0 / (n as real);
        assert e29(n) in A;
        assert sub(1.0, 1.0 / (n as real + 1.0)) == e29(n); 
        // assert exists k :: k in A && k > sub(1.0, epsilon);
    }
}

lemma exercise1_29b(A: iset<real>)
    requires A == iset n: pos :: e29(n)
    ensures inf(A, 1.0/2.0)
{
    assert e29(1) in A;
    forall x | x in A 
        ensures x >= 1.0/2.0
    {
        var n: nat :| x == e29(n);
        if n == 1 {

        }
    }
    assert lowerBound(A, 1.0/2.0);
    assert greatestLeastBound(A, 1.0/2.0);
}

lemma exercise1_30(A: iset<real>, B: iset<real>, abound: real, bbound: real)
    requires sup(A, abound)
    requires sup(B, bbound)
    requires abound < bbound
    ensures exists b: real :: b in B && upperBound(A, b)
{
    // assert upperBound(A, bbound);
    // assert leastUpperBound(B, bbound);
    // assert forall epsilon: real :: epsilon > 0.0 ==> !upperBound(B, sub(bbound, epsilon));
    var epsilon := sub(bbound, abound);
    // assert abound + epsilon == bbound;
    // assert epsilon > 0.0;
    assert !upperBound(B, sub(bbound, epsilon));
}