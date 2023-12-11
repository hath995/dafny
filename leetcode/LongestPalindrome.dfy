include "../lib/seq.dfy"
include "LongestPalindromSupp.dfy"
import opened Palindrome
import opened Seq
/*
function toMultiset(s: string): Map<string, number> {
    const s_mset: Map<string, number> = new Map();
    for(let char of s) {
        if(s_mset.has(char)) {
            s_mset.set(char, s_mset.get(char)+1);
        }else{
            s_mset.set(char, 1);
        }
    }
    return s_mset;
}

function longestPalindrome(s: string): number {
    let smset = toMultiset(s);
    let length = 0;
    let odds = [];
    for(let count of smset.values()) {
        if(count % 2 == 0) {
            length += count;
        }else {
            odds.push(count);
        }
    }
    if(odds.length > 0) {
    odds.sort();
    length += odds.pop();
    length += odds.reduce((total, x) => total+x-1, 0);
    }

    return length;
}
*/
ghost function allStrings(ms: multiset<char>): iset<string> {
    iset ss: string | multiset(ss) <= ms
}

predicate IsPalindrome(s: string) {
    s == reverse(s)
}

function rep(c: char, count: nat): string 
    ensures |rep(c, count)| == count
    ensures forall i :: 0 <= i < count ==> rep(c, count)[i] == c
    ensures multiset(rep(c, count))[c] == count
{
    if count == 0 then "" else [c]+rep(c, count - 1)
}

lemma PalindromePlus(s: string, c: char) 
    requires IsPalindrome(s)
    ensures IsPalindrome([c]+s+[c])
{
    ReverseIndexAll(s);
    ReverseIndexAll([c]+s+[c]);
}

lemma PalindromePlusRep(s: string, c: char, count: nat) 
    requires IsPalindrome(s)
    ensures IsPalindrome(rep(c, count)+s+rep(c, count))
{
    ReverseIndexAll(s);
    ReverseIndexAll(rep(c, count)+s+rep(c, count));
}

lemma PalindromePlusRepOdd(s: string, c: char, count: nat) 
    requires count > 0 && count % 2 == 1
    requires IsPalindrome(s)
    requires |s| % 2 == 0
    ensures IsPalindrome(s[0..|s|/2]+rep(c, count)+s[|s|/2..])
{
    ReverseIndexAll(s);
    ReverseIndexAll(s[0..|s|/2]+rep(c, count)+s[|s|/2..]);
}

lemma allOnesDistinct<T>(ss: seq<T>) 
    requires forall key :: key in ss ==> multiset(ss)[key] == 1
    ensures distinct(ss)
{
    if |ss| > 0 {
        assert ss == [ss[0]] + ss[1..];
        assert distinct([ss[0]]);
        assert multiset(ss[1..]) == multiset(ss) - multiset{ss[0]};
        allOnesDistinct(ss[1..]);
    }
}

method longestPalindromePartial(s: string) returns (length: int, odds: seq<nat>, ghost oddKey: seq<char>, ghost pt: string, ghost ptMset: multiset<char>, ghost oddMset: multiset<char>) 
    ensures IsPalindrome(pt)
    ensures |pt| % 2 == 0
    ensures |pt| == length
    ensures multiset(pt) == ptMset
    ensures multiset(s) == ptMset + oddMset
    ensures ptMset !! oddMset
    ensures ptMset <= multiset(s)
    ensures forall key :: key in ptMset ==> ptMset[key] % 2 == 0
    ensures forall key :: key in oddMset ==> oddMset[key] % 2 == 1
    ensures forall count :: count in odds ==> count > 0 && count % 2 == 1
    ensures |oddKey| == |odds|
    ensures distinct(oddKey)
    ensures forall key :: key in oddKey ==> key in oddMset
    ensures forall i :: 0 <= i < |odds| ==> oddMset[oddKey[i]] == odds[i]
{

    var mset := multiset(s);
    oddKey := [];
    odds := [];
    length := 0;

    pt := "";
    ghost var removed: multiset<char> := multiset{};
    oddMset := multiset{};
    ptMset := multiset{};
    while mset != multiset{}
        invariant IsPalindrome(pt)
        invariant forall key :: key in ptMset ==> ptMset[key] % 2 == 0
        invariant forall key :: key in oddMset ==> oddMset[key] % 2 == 1
        invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
        // invariant mset !! removed
        invariant mset !! ptMset
        invariant mset !! oddMset
        invariant ptMset !! oddMset
        invariant multiset(s) == mset + removed
        invariant removed == ptMset + oddMset
        invariant multiset(s) == ptMset + oddMset + mset 
        invariant |pt| == length
        invariant |pt| % 2 == 0
        invariant multiset(pt) == ptMset
        invariant |oddKey| == |odds|
        invariant forall key :: key in oddKey ==> multiset(oddKey)[key] == 1
        // invariant distinct(oddKey)
        invariant forall key :: key in oddKey ==> key in oddMset
        invariant forall i :: 0 <= i < |odds| ==> oddMset[oddKey[i]] == odds[i]
        // invariant multiset(pt) == ptMset
    {
        var x :| x in mset;
        if mset[x] % 2 == 0 {
            length := length + mset[x];
            ghost var repchar := rep(x, mset[x]/2);
            assert multiset(repchar)[x] == mset[x]/2;
            PalindromePlusRep(pt, x, mset[x]/2);
            calc {
                multiset(repchar+repchar)+multiset(pt);
                multiset(repchar+pt+repchar);
            }
            assert multiset(repchar+repchar)[x] == mset[x];
            assert multiset(repchar+repchar)+multiset(pt) == ptMset[x := mset[x]];
            pt := repchar+pt+repchar;
            ptMset := ptMset[x := mset[x]];
        }else{
            oddKey := oddKey + [x];
            odds := odds + [mset[x]];
            oddMset := oddMset[x := mset[x]];            
            assert odds[|odds|-1] == oddMset[x];
        }
        removed := removed[x := mset[x]];
        mset := mset[x := 0];
    }
    allOnesDistinct(oddKey);
}

method  longestPalindromePieces(s: string) returns (length: int, ghost pt: string, ghost ptmset: multiset<char>) 
    ensures |pt| == length 
    ensures IsPalindrome(pt)
    ensures multiset(pt) <= multiset(s) 
    ensures multiset(pt) == ptmset
    //ensures forall x :: x in allStrings(multiset(s)) ==> |s| <= |pt|
{
    var plength, odds, oddKey, ppt, ptMset, oddMset :=longestPalindromePartial(s);
    ptmset := ptMset;
    length := plength;
    pt := ppt;

    if |odds| > 0 {
        assert odds[0] in odds;
        PalindromePlusRepOdd(pt, oddKey[0], odds[0]);
        assert pt == pt[0..|pt|/2] + pt[|pt|/2..];
        pt := pt[0..|pt|/2]+rep(oddKey[0], odds[0])+pt[|pt|/2..];
        assert IsPalindrome(pt);
        length := length + odds[0];
        assert forall i :: 1 <= i < |oddKey| ==> oddKey[i] !in ptMset;

        ptMset := ptMset[oddKey[0] := odds[0]];
        ptmset := ptmset[oddKey[0] := odds[0]];
        assert ptMset == multiset(pt);
        assert ptmset == multiset(pt);
        assert ptMset <= multiset(s);
        assert length == |pt|;
        // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
        // assert odds == [odds[0]]+odds[1..];
        assert forall count :: count in odds[1..] ==> count > 0 && count % 2 == 1 by {
            forall count | count in odds[1..] 
                ensures count in odds
            {
                assert count in odds;
            }
        }
        odds := odds[1..];
        // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
        for i := 0 to |odds| 
            invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
            invariant IsPalindrome(pt)
            invariant length == |pt|

            invariant forall k :: i < k < |oddKey| ==> oddKey[k] !in ptMset
            invariant ptMset == multiset(pt)
            invariant ptmset == multiset(pt)
            invariant ptMset <= multiset(s)
        {
            assert odds[i] in odds; 
            ghost var repchar := rep(oddKey[i+1], (odds[i]-1)/2);

            calc {
                multiset(repchar+repchar)+multiset(pt);
                multiset(repchar+pt+repchar);
            }
            assert multiset(repchar+repchar)[oddKey[i+1]] == odds[i]-1;
            // assume oddKey[i+1] !in ptMset;
            assert multiset(repchar+repchar)+multiset(pt) == ptMset[oddKey[i+1] := odds[i]-1];
            PalindromePlusRep(pt, oddKey[i+1], (odds[i]-1)/2);
            pt := repchar+pt+repchar;
            length := length + odds[i] - 1;
            ptMset := ptMset[oddKey[i+1] := odds[i]-1];
            ptmset := ptmset[oddKey[i+1] := odds[i]-1];
        }
    }
}

method {:verify false} longestPalindrome(s: string) returns (length: int, ghost pt: string, ptmset: multiset<char>) 
    ensures |pt| == length 
    ensures IsPalindrome(pt)
    ensures multiset(pt) <= multiset(s) 
    //ensures forall x :: x in allStrings(multiset(s)) ==> |s| <= |pt|
{
    var mset := multiset(s);
    ghost var oddKey: seq<char> := [];
    var odds: seq<nat> := [];
    length := 0;

    pt := "";
    ghost var removed: multiset<char> := multiset{};
    ghost var oddMset: multiset<char> := multiset{};
    ghost var ptMset: multiset<char> := multiset{};
    while mset != multiset{}
        invariant IsPalindrome(pt)
        invariant forall key :: key in ptMset ==> ptMset[key] % 2 == 0
        invariant forall key :: key in oddMset ==> oddMset[key] % 2 == 1
        invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
        // invariant mset !! removed
        invariant mset !! ptMset
        invariant mset !! oddMset
        // invariant ptMset !! oddMset
        invariant multiset(s) == mset + removed
        invariant removed == ptMset + oddMset
        invariant multiset(s) == ptMset + oddMset + mset 
        invariant |pt| == length
        invariant |pt| % 2 == 0
        invariant multiset(pt) == ptMset
        invariant |oddKey| == |odds|
        invariant forall key :: key in oddKey ==> key in oddMset
        invariant forall i :: 0 <= i < |odds| ==> oddMset[oddKey[i]] == odds[i]
        // invariant multiset(pt) == ptMset
    {
        var x :| x in mset;
        if mset[x] % 2 == 0 {
            length := length + mset[x];
            ghost var repchar := rep(x, mset[x]/2);
            assert multiset(repchar)[x] == mset[x]/2;
            PalindromePlusRep(pt, x, mset[x]/2);
            calc {
                multiset(repchar+repchar)+multiset(pt);
                multiset(repchar+pt+repchar);
            }
            assert multiset(repchar+repchar)[x] == mset[x];
            assert multiset(repchar+repchar)+multiset(pt) == ptMset[x := mset[x]];
            pt := repchar+pt+repchar;
            ptMset := ptMset[x := mset[x]];
        }else{
            oddKey := oddKey + [x];
            odds := odds + [mset[x]];
            oddMset := oddMset[x := mset[x]];            
            assert odds[|odds|-1] == oddMset[x];
        }
        removed := removed[x := mset[x]];
        mset := mset[x := 0];
    }
    if |odds| > 0 {
        assert odds[0] in odds;
        PalindromePlusRepOdd(pt, oddKey[0], odds[0]);
        pt := pt[0..|pt|/2]+rep(oddKey[0], odds[0])+pt[|pt|/2..];
        assert IsPalindrome(pt);
        length := length + odds[0];
        assert length == |pt|;
        // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
        // assert odds == [odds[0]]+odds[1..];
        assert forall count :: count in odds[1..] ==> count > 0 && count % 2 == 1 by {
            forall count | count in odds[1..] 
                ensures count in odds
            {
                assert count in odds;
            }
        }
        odds := odds[1..];
        // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
        for i := 0 to |odds| 
            invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
            invariant IsPalindrome(pt)
            invariant length == |pt|
        {
            assert odds[i] in odds; 
            ghost var repchar := rep(oddKey[i+1], (odds[i]-1)/2);
            PalindromePlusRep(pt, oddKey[i+1], (odds[i]-1)/2);
            pt := repchar+pt+repchar;
            length := length + odds[i] - 1;
        }
    }

}