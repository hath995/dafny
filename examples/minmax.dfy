// https://leetcode.com/problems/minimum-value-to-get-positive-step-by-step-sum/
method {:verify } DifferenceMinMax(a: seq<int>) returns (diff: int)
    requires |a| > 0 && |a| < 10
    ensures diff == (Max(a[..]) - Min(a[..]))
{
    var minVal := a[0];
    var maxVal := a[0];
    var i := 1;
    while i < |a|
        invariant 1 <= i <= |a|
        invariant minVal <= maxVal
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
        invariant forall k :: 0 <= k < i ==> minVal <= a[k] && a[k] <= maxVal
    {
        assert a == a[..i]+a[i..];
        assert a[i] in a[..(i+1)];
        assert maxVal == Max(a[..i]);
        assert minVal == Min(a[..i]);
        ghost var last := a[..i];
        ghost var next := a[..(i+1)];
        assert next == last + [a[i]];
        ghost var prevMaxVal := maxVal;
        ghost var prevMinVal := minVal;
        if i < |a| && a[i] < minVal {
            assert minVal == Min(a[..i]);
            assert forall n :: n in a[..i] ==> minVal <= n;
            minVal := a[i];
            assert minVal == Min(a[..(i+1)]);
        } else if i < |a| && a[i] > maxVal {
            assert maxVal == Max(a[..i]);
            maxVal := a[i];
            assert maxVal == Max(a[..(i+1)]);
        }
        /*else if i < |a| {
            assert a[i] >= minVal;
            assert a[i] <= maxVal;
            assert minVal == Min(a[..i]);
            assert maxVal == Max(a[..i]);
            assert a[..(i+1)] == a[..i] + [a[i]];
            assert forall n :: n in a[..i] ==> minVal <= n;
            assert forall n :: n in a[..(i+1)] ==> minVal <= n;
            assert minVal in a[..(i+1)];
            assert minVal == Min(a[..(i+1)]);
            assert maxVal in a[..(i+1)];
            assert maxVal == Max(a[..(i+1)]);
        }else{
            assert i == |a|;
            assert a == a[..i];
            assert maxVal == Max(a);
            assert minVal == Min(a);
        }*/

        // if i < |a| {
        //     assert a[..(i+1)] == last + [a[i]];
        //     assert prevMinVal == Min(last);
        //     assert prevMinVal in a[..i];
        //     assert prevMaxVal == Max(last);
        //     assert prevMaxVal in a[..i];
        //     if a[i] < prevMinVal {
        //         assert minVal == Min(a[..(i+1)]);
        //     }else{
        //         assert a[i] >= prevMinVal;
        //         assert minVal in a[..i] ==> minVal <= prevMinVal;
        //         assert minVal == Min(a[..(i+1)]);
        //     }
        //     if a[i] > prevMaxVal {
        //         assert maxVal == a[i];
        //         assert maxVal == Max(a[..i+1]);
        //     }else{
        //         assert a[i] <= prevMaxVal;
        //         assert maxVal == Max(a[..i+1]);
        //     }
        // }else{
        //     assert i == |a|;
        //     assert maxVal == Max(a[..i]);
        //     assert minVal == Min(a[..i]);
        // }
        // assert minVal == Min(a[..(i+1)]);
        // assert maxVal == Max(a[..(i+1)]);
        i := i + 1;
    }
    assert a == a[..|a|];
    assert maxVal == Max(a);
    assert minVal == Min(a);

    diff := maxVal - minVal;
}

function Min(a: seq<int>) : (m: int)
    requires |a| > 0
    ensures Min(a) in a
    // ensures forall n :: n in a ==> Min(a) <= n
{
    if |a| == 1 then a[0]
    else
      var minPrefix := Min(a[..|a|-1]);
      if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}

function Max(a: seq<int>) : (m: int)
    requires |a| > 0
    ensures Max(a) in a
{
    if |a| == 1 then a[0]
    else
      var maxPrefix := Max(a[..|a|-1]);
      if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}

lemma MaxIsMax(a: seq<int>)
    requires |a| > 0
    ensures forall n :: n in a ==> Max(a) >= n
{
    assert a == a[..|a|-1] + [a[|a|-1]];
}

// function Min(a: seq<int>) : int
//     requires |a| > 0
//     ensures forall n :: n in a ==> Min(a) <= n
//     ensures Min(a) in a
//     decreases |a|
// {
//     assert a == [a[0]] + a[1..];
//     if |a| == 1 then a[0]
//     else if a[0] <= Min(a[1..]) then
//         //var min := Min(a[1..]);
//         //assert forall n :: n in a[1..] ==> min in a && min <= n;
//         //assert forall n :: n in a ==> a[0] in a && a[0] <= n;
//     a[0] 
//     else
//         //var min := Min(a[1..]);
//         //assert min in a[1..];
//         //assert a[0] > min;
//         //assert a == [a[0]] + a[1..];
//         //assert forall n :: n in a[1..] ==> min in a && min <= n;
//         //assert forall n :: n in a ==> min in a;// && min <= n;
//     Min(a[1..])
// }

// lemma minIsMin(a: seq<int>, j: int) 
//     requires |a| > 0
//     requires j in a
//     requires forall n :: n in a ==> j <= n
//     ensures j == Min(a)
// {

// }

function MaxRest(a: seq<int>) : int
    requires |a| > 0
    ensures MaxRest(a) in a
    ensures forall n :: n in a ==> MaxRest(a) >= n
{
    assert a == [a[0]] + a[1..];
    if |a| == 1 then a[0]
    else if a[0] >= MaxRest(a[1..]) then a[0] else MaxRest(a[1..])
}

lemma MaxEqual(a: seq<int>)
    requires |a| > 0
    ensures Max(a) == MaxRest(a)
{
    MaxIsMax(a);     
    if |a| == 1 {
        assert Max(a) == MaxRest(a);

    }else{
        assert Max(a) == MaxRest(a);

    }
}

method DifferenceMinMaxCp(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{
    var minVal := Min(a[..]);
    var maxVal := Max(a[..]);

    diff := maxVal - minVal;
}

lemma mss(ms: multiset<nat>, head: nat, i: nat, c:nat)
    ensures multiset{head} + (ms-multiset{i}+multiset{c}) == multiset{head} + ms-multiset{i}+multiset{c}
{

}