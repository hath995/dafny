
datatype Forest = Node(alpha: string) | Context | Zero | Product(left: Forest, right: Forest) | Sum(left: Forest, right: Forest)


function method Remove(T: Forest, Q: Forest): Forest 

{
    match T {
        case Node(alpha) => if Q == T then Context else Node(alpha)
        case Context => Zero
        case Zero => Zero
        case Product(L, R) => if Q == L then Product(Context, Remove(R, Q)) else if Q == R then Product(Remove(L, Q), Context) else Product(Remove(L, Q), Remove(R, Q))
        case Sum(L, R) => if Q == L then Sum(Context, Remove(R, Q)) else if Q == R then Sum(Remove(L, Q), Context) else Sum(Remove(L, Q), Remove(R, Q))
    }
}

predicate nodeIn(forest: Forest, tree: Forest) {
    match forest {
        case Node(alpha) => tree == forest
        case Context => tree == forest
        case Zero => tree == Zero
        case Product(L, R) => if forest == tree then true else nodeIn(L, tree) || nodeIn(R, tree)
        case Sum(L, R) => if forest == tree then true else nodeIn(L, tree) || nodeIn(R, tree)
    }
}

function method concatenation(left: Forest, right: Forest): Forest

{
    if left == Zero then right else if right == Zero then left else Sum(left, right)
}

function method composition(left: Forest, right: Forest): Forest

{
    match left {
        case Node(alpha) => Node(alpha)
        case Zero => Zero
        case Context => right
        case Product(L, R) => Product(composition(L, right), composition(R, right))
        case Sum(L, R) => Sum(composition(L, right), composition(R, right))
    }
}

lemma sumEquality(a: Forest, b: Forest, c: Forest)
    ensures Sum(a, Sum(b,c)) == Sum(Sum(a,b), c)

lemma composititionAssociative(a: Forest, b: Forest, c: Forest)
    ensures composition(a, composition(b,c)) == composition(composition(a,b), c)
{

}

lemma concatenationAssociative(a: Forest, b: Forest, c: Forest)
    ensures concatenation(a, concatenation(b,c)) == concatenation(concatenation(a,b), c)
{
    sumEquality(a,b,c);

}

lemma compositionContextIdentity(a: Forest)
    ensures composition(a, Context) == a;
{

}

lemma concatenationZeroIdentity(a: Forest)
    ensures concatenation(Zero, a) == a
    ensures concatenation(a, Zero) == a
{

}

lemma compositionZeroAnnihilates(a: Forest)
    ensures composition(Zero, a) == Zero
{

}

lemma leftDistributive(q: Forest, p: Forest, r: Forest)
    ensures composition(concatenation(p, q), r) == concatenation(composition(p,r), composition(q,r))
{
    sumEquality(p,q,r);
}

lemma Inverses(P: Forest, Q: Forest)
    ensures composition(composition(Remove(P,Q),Q), Zero) == composition(P, Zero)
{

}

function method apply(mut: Mutation): Forest {
    match mut {
        case Addition(p,q) => composition(p, q)
        case Subtraction(p, q, c) => c
    }
}

predicate combinesTo(prev: Mutation, succ: Mutation) {
    match prev {
        case Addition(p, q) => nodeIn(p, Context) && !nodeIn(p,q) && composition(p,q) == succ.p && nodeIn(composition(p,q), q)
        case Subtraction(p, q, c) => nodeIn(p,q) && composition(c, Zero) == Remove(p,q) && c == succ.p && !nodeIn(c, q)
    }
}

datatype Mutation = Addition(p: Forest, q: Forest) | Subtraction(p: Forest, q: Forest, c: Forest)

method summarizeChange(start: Forest, end: Forest, mutations: seq<Mutation>)
    requires |mutations| > 1
    requires forall i :: 1 <= i < |mutations| ==> combinesTo(mutations[i-1], mutations[i])
    requires mutations[0].p == start;
    requires apply(mutations[|mutations|-1]) == end
{
    var i := 1;
    while i < |mutations| 
        invariant 1 <= i <= |mutations|
    {
        var mut := mutations[i-1];
        match mut {
            case Addition(p,q) => assert mutations[i].p == composition(p,q);
            case Subtraction(p, q, c) => assert mutations[i].p == c;
        }
        i := i + 1;
    }
}

method test() {
    var best := Sum(Node("a"), Context);
    var quest := Sum(Node("a"), Context);
    assert best == quest;

}