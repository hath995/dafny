
module Seq {
    predicate substring1<A>(sub: seq<A>, super: seq<A>) {
        exists k :: 0 <= k < |super| && sub <= super[k..]
    }


    predicate isSubstringAlt<A(!new)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists xs: seq<A> :: IsSuffix(xs, super) && sub <= xs
    }

    predicate isSubstring<A>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists k,j :: 0 <= k < j <= |super| && sub == super[k..j]
    }

    lemma SliceOfSliceIsSlice<A>(xs: seq<A>, k: int, j: int, s: int, t: int)
        requires 0 <= k <= j <= |xs|
        requires 0 <= s <= t <= j-k
        ensures xs[k..j][s..t] == xs[(k+s)..(k+s+(t-s))]
    {
        // if k == 0 && j == 0 {
        //     assert xs[k..j] == [];
        //     assert xs[k..j][s..t] == [];
        // }else if k == 0 && j == |xs| {
        //     assert xs[k..j] == xs;
        //     assert xs[k..j][s..t] == xs[(k+s)..(k+s+t-s)];
        // }else if k == |xs| && j == |xs| {
        //     assert xs[k..j] == [];
        //     assert xs[k..j][s..t] == xs[(k+s)..(k+s+t-s)];
        // }else 
        if 0 <= k <= j <= |xs| {
            if j-k == 0 {

            }else if t-s == 0 {

            }else if t-s > 0 {
                SliceOfSliceIsSlice(xs, k, j, s,t-1);
                assert xs[k..j][s..t] == xs[k..j][s..(t-1)]+[xs[k..j][t-1]];
            }
        }else{
            assert false;
        }
    }

    lemma AllSubstringsAreSubstrings<A>(subsub: seq<A>, sub: seq<A>, super: seq<A>)
        requires isSubstring(sub, super)
        requires isSubstring(subsub, sub)
        ensures isSubstring(subsub, super)
    {
        assert |sub| <= |super|;
        assert |subsub| <= |super|;
        var k,j :| 0 <= k < j <= |super| && sub == super[k..j];
        var s,t :| 0 <= s < t <= |sub| && subsub == sub[s..t];
        assert t <= (j-k) <= j;
        //[3,4,5,6,7,8,9,10,11,12,13][2,7] //k,j
        //[5,6,7,8,9,10][1..3] //s,t
        //[5,7,8]
        // var example:= [3,4,5,6,7,8,9,10,11,12,13];
        // assert example[2..7] == [5,6,7,8,9];
        // assert example[2..7][1..3] == [6,7];
        // assert example[3..5] == [6,7];
        // assert k+s+(t-s)
        // assert 2+1+(3-1) == 5;
        /*
        assert s[..idx] == [s[0]] + s[1..idx];
        assert s[1..idx] == s[1..][..(idx-1)];
        assert s[1..][(idx-1)..] == s[idx..];
        */
        assert super[..j][..t] == super[..(t)];
        assert super[k..][s..] == super[(k+s)..];
        if t < j {
            calc {
                subsub;
                super[k..j][s..t];
                {SliceOfSliceIsSlice(super,k,j,s,t);}
                super[(k+s)..(k+s+(t-s))];
            }
        } else if t <= j {

        }
        var z,q :| 0 <= z <= q <= |super| && super[z..q] == super[k..j][s..t];
    }


    predicate IsSuffix<T>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && xs == ys[|ys| - |xs|..]
    }

    predicate IsSuffix2<T>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && exists K :: 0 <= K <= |ys|-|xs| && ys == ys[0..K] + xs + ys[(K+|xs|)..]
    }

    method Test() {
        var t1 := [4,5,6,1,2,3];
        // assert t1 == [4,5,6]+[1,2,3];
        var s1 := [1,2,3];
        assert IsSuffix(s1,t1);
        // assert isSubstring(s1,t1);
        assert substring1(s1, t1);

    }

}