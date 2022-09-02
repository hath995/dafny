predicate sortedRec(list: seq<int>) {
    if list == [] then true else (forall y :: y in list[1..] ==> list[0] <= y) && sortedRec(list[1..])
}

function merge(xs: seq<int>, ys: seq<int>): seq<int>
    requires sortedRec(xs)
    requires sortedRec(ys)
    ensures sortedRec(merge(xs, ys))
    ensures multiset(merge(xs,ys)) == multiset(xs)+multiset(ys)
{
    if xs == [] then ys else
    if ys == [] then xs else
    if xs[0] <= ys[0] then 
        assert xs == [xs[0]] + xs[1..];
        assert ys == [ys[0]] + ys[1..];
        assert forall x :: x in merge(xs[1..], ys) ==> x in xs[1..] || x in ys ==> xs[0] <= x;
        // assert sortedRec(merge(xs[1..], ys));
        var result := [xs[0]] + merge(xs[1..], ys);
        assert forall x :: x in result[1..] ==> x in multiset(xs[1..])+multiset(ys);
        result
    else 
        assert xs == [xs[0]] + xs[1..];
        assert ys == [ys[0]] + ys[1..];
        assert forall x :: x in merge(xs, ys[1..]) ==> x in xs || x in ys[1..] ==> ys[0] <= x;
        var result := [ys[0]] + merge(xs, ys[1..]);
        assert forall x :: x in result[1..] ==>x in multiset(xs) + multiset(ys[1..]);
        result
}

function mergesort(xs: seq<int>): seq<int>
    ensures multiset(xs) == multiset(mergesort(xs))
    ensures sortedRec(mergesort(xs))
{
    var n := |xs|;
    if n <= 1 then xs else
        assert xs == xs[0..n/2] + xs[n/2..];
        merge(mergesort(xs[0..n/2]), mergesort(xs[n/2..]))
}

/*

        // assert result == [xs[0]] + result[1..];
        // assert result[1..] == merge(xs[1..], ys);
        // assert forall y :: y in ys[1..] ==> xs[0] <= ys[0] <= y;
        // assert forall y :: y in ys ==> xs[0] <= y;
        // assert forall y :: y in multiset(ys) ==> y in ys ==> xs[0] <= y;
        // assert forall x :: x in xs[1..] ==> xs[0] <= xs[0];
        // assert forall x :: x in multiset(xs[1..]) ==> xs[0] <= xs[0];
        assert forall x :: x in (multiset(xs[1..]) + multiset(ys)) ==> x in xs[1..] ||  x in ys ==> xs[0] <= x;
        assert multiset(xs) == multiset{xs[0]} + multiset(xs[1..]);
        assert multiset(ys) == multiset{ys[0]} + multiset(ys[1..]);
        assert multiset(xs)+multiset(ys) == multiset{xs[0]} + (multiset(xs[1..]) + multiset(ys));
        // assert sortedRec(result[1..]);
        // assert forall x :: x in result[1..] ==> x in xs[1..] || x in ys ==> result[0] <= x;
        // assert sortedRec(result);
        // assert sortedRec([xs[0]]+merge(xs[1..], ys));

// assert xs != [];
// assert ys != [];
// assert multiset(xs) == multiset{xs[0]} + multiset(xs[1..]);
// assert multiset(ys) == multiset{ys[0]} + multiset(ys[1..]);
// assert multiset(xs)+multiset(ys) == multiset{ys[0]} + (multiset(xs) + multiset(ys[1..]));
// assert sortedRec(merge(xs, ys[1..]));
// assert result[0] == ys[0];
// assert result[1..] == merge(xs, ys[1..]);
// assert multiset(merge(xs, ys[1..])) == multiset(xs) + multiset(ys[1..]);
// assert forall x :: x in result[1..] ==> (x in xs || x in ys[1..]) && result[0] <= x;
// assert sortedRec(result[1..]);
// assert sortedRec(result);
*/