
include "../lib/seq.dfy"
import opened Seq

ghost function allPermutations(str: string): iset<string> {
    iset ss: string | multiset(ss) == multiset(str)
}

lemma allPermutationsSameLength(str: string)
    ensures forall ss :: ss in allPermutations(str) ==> |ss| == |str|
{

}

lemma allPermutationsSameLengthOrLess(str: string)
    ensures forall ss :: ss in allSubStrings(str) ==> |ss| <= |str|
{
    forall ss | ss in allSubStrings(str) 
        ensures |ss| <= |str|
    {
        if multiset(ss) == multiset(str) {
            allPermutationsSameLength(str);
        }else {
            assert multiset(ss) < multiset(str);
            multisetSubsetSmaller(multiset(str), multiset(ss));
        }
    }
}

ghost function allSubStrings(str: string): iset<string> {
    iset ss: string | multiset(ss) <= multiset(str)
}

ghost function allPalindromSubStrings(str: string): iset<string> {
    iset ss: string | multiset(ss) <= multiset(str) && IsPalindrome(ss)
}

ghost function allStrings(ms: multiset<char>): iset<string> {
    iset ss: string | multiset(ss) <= ms
}

ghost function allPalindromeStrings(ms: multiset<char>): iset<string> {
    iset ss: string | multiset(ss) <= ms && IsPalindrome(ss)
}

predicate IsPalindrome(s: string) {
    s == reverse(s)
}

lemma msLength(s: string) 
    ensures |s| == |multiset(s)|
{}

lemma multSize<T(==)>(ms: multiset<T>, x: T)
    requires |ms| > 0 
    requires x in ms
    ensures |ms| >= ms[x] >= 1
{

}

lemma multisetSubsetSmaller<T(==)>(ms: multiset<T>, mss: multiset<T>)
    requires |ms| > 0
    requires mss < ms
    ensures |mss| < |ms|
{
    if |ms| == 1 {
        var x :| x in ms;
        assert ms[x] == 1;
        assert |multiset{x}| == 1;
        assert |ms-multiset{x}| == 0;
        assert ms-multiset{x} == multiset{};
        assert ms == multiset{x};
        assert mss[x] < 1;
        assert mss == multiset{};
    }else{
        var x :| x in ms;
        if mss[x] == ms[x] {
            multisetSubsetSmaller(ms[x:=0], mss[x:=0]);
        }else if mss[x] < ms[x] {
            if mss[x:=0] < ms[x:=0] {
                multisetSubsetSmaller(ms[x:=0], mss[x:=0]);
            }else{

            }
        }
    }
}

lemma allSubmultisetsShorter(s: string, mss: multiset<char>)
    requires |s| > 0
    requires mss < multiset(s)
    ensures forall xx :: xx in allStrings(mss) ==> |xx| < |s|
{
    msLength(s);
    var ms := multiset(s);
    assert |ms| == |s|;
    multisetSubsetSmaller(ms, mss);
    assert |mss| < |ms|;
    forall xx | xx in allStrings(mss)
        ensures |xx| < |s|
    {
        // if multiset(xx) == ms {
        // //     msLength(xx);
        // //  |xx| < |s|
        // assert false;
        // }else if multiset(xx) < ms {
            multisetSubsetSmaller(ms, multiset(xx));
        // }
    }
}

method Test() {
     var example := "abcqqqcba";
     assert IsPalindrome(example);
     var ms:= multiset(example);
     assert example in allPalindromeStrings(ms);
}

ghost function largestOdd(ms: multiset<char>) : multiset<char> 
    ensures largestOdd(ms) != multiset{} ==> forall x :: x in largestOdd(ms) ==> ms[x] % 2 == 1
{
    var candidates: set<char> := set x | x in ms && ms[x] % 2 == 1 && (forall y :: y in ms ==> ms[x] >= ms[y]);
    var stub: multiset<char> := multiset{};
    if |candidates| == 0 then 
        multiset{}
    else var x :| x in candidates; stub[x := ms[x]]
}

lemma largestExistsRev(ms: multiset<char>)
    requires exists y :: y in ms && ms[y] % 2 == 1 && forall x :: x in ms && ms[x] % 2 == 1 && ms[y] >= ms[x]
    ensures (set x | x in ms && ms[x] % 2 == 1) != {}
{
    var res := (set x | x in ms && ms[x] % 2 == 1);
    var y :| exists y :: y in ms && ms[y] % 2 == 1 && forall x :: x in ms && ms[x] % 2 == 1 && ms[y] >= ms[x];
    assert y in res;
}

lemma largestExists(ms: multiset<char>)
    requires (set x | x in ms && ms[x] % 2 == 1) != {}
    ensures exists y :: y in ms && ms[y] % 2 == 1 && forall x :: x in ms && ms[x] % 2 == 1 ==> ms[y] >= ms[x]
{
    var res := (set x | x in ms && ms[x] % 2 == 1);
    var stub:multiset<char> := multiset{};
    var y :| y in res;
    if res-{y} == {} {
        assert res == {y};
        var msy := stub[y := ms[y]];
        assert forall z :: z in ms && ms[z] % 2 == 1 ==> z in res && ms[y] >= ms[z];
        // assert y in ms && ms[y] % 2 == 1;
        // assert y in ms && ms[y] % 2 == 1 && forall z :: z in ms && ms[z] % 2 == 1 ==> ms[y] >= ms[z];
    }else{
        var res' := res-{y};
        var ms' := ms-stub[y := ms[y]];
        if forall x :: x in ms && ms[x] % 2 ==1 ==> ms[y] >= ms[x] {

        }else{
            largestExists(ms');
        }
        // largestExists(ms');
    }
    // var y :| exists y :: y in ms && ms[y] % 2 == 1 && forall x :: x in ms && ms[x] % 2 == 1 && ms[y] >= ms[x];
    // assert y in res;
}

lemma noLargestOddsNoOdds(ms: multiset<char>) 
    requires largestOdd(ms) == multiset{}
    ensures allEven(ms)
{
    if !allEven(ms) {
        var lo := largestOdd(ms);
        var allOdds := set x | x in ms && ms[x] % 2 == 1;
        var x :| x in ms && ms[x] % 2 == 1;
        assert x in allOdds;

        // assert x in largestOdd(ms);
    }
}

predicate allEven(ms: multiset<char>) {
    forall x :: x in ms ==> ms[x] % 2 ==0
}

ghost function evenPlusRectEvens(ms: multiset<char>): multiset<char> 
    // ensures forall x :: x in evenPlusRectEvens(ms) ==> evenPlusRectEvens(ms)[x] % 2 ==0
    ensures allEven(evenPlusRectEvens(ms))
    ensures evenPlusRectEvens(ms) <= ms
    ensures forall k :: k in ms && ms[k] % 2 == 0 ==> evenPlusRectEvens(ms)[k] == ms[k]
    ensures forall k :: k in ms && ms[k] % 2 == 1 ==> evenPlusRectEvens(ms)[k] == ms[k] - 1
{
    if |ms| == 0 then multiset{} else
    var x :| x in ms;
    var stub: multiset<char> := multiset{};
    if ms[x] % 2 == 0 then
        stub[x := ms[x]]+evenPlusRectEvens(ms[x := 0])
    else
        stub[x := ms[x]-1]+evenPlusRectEvens(ms[x :=0])
}

ghost function largePalindromeMultiset(str: string): multiset<char>
    ensures largestOdd(multiset(str)) == multiset{} ==> allEven(largePalindromeMultiset(str))
    ensures largestOdd(multiset(str)) != multiset{} ==> exists k :: k in largePalindromeMultiset(str) && 
        largePalindromeMultiset(str)[k] % 2 ==1 && 
        (forall y :: y in multiset(str) && multiset(str)[y] % 2 ==1 ==> largePalindromeMultiset(str)[k] >= multiset(str)[y] )
        && forall kk :: kk != k && kk in largePalindromeMultiset(str) ==> largePalindromeMultiset(str)[kk] % 2 == 0
    ensures largePalindromeMultiset(str) <= multiset(str)
    ensures forall zz :: zz in largePalindromeMultiset(str) && largePalindromeMultiset(str)[zz] % 2 == 0 ==> largePalindromeMultiset(str)[zz] <= multiset(str)[zz]
    ensures forall zz :: zz in largePalindromeMultiset(str) && multiset(str)[zz] % 2 == 0 ==> largePalindromeMultiset(str)[zz] == multiset(str)[zz]
    // ensures forall zz :: zz in largePalindromeMultiset(str) && multiset(str)[zz] % 2 == 1 ==> largePalindromeMultiset(str)[zz] == multiset(str)[zz] -1
{
    var ms := multiset(str);
    var largestOdds := largestOdd(ms);
    if largestOdds != multiset{} then 
        var x :| x in largestOdds;
        assert x !in ms-largestOdds;
        assert x !in evenPlusRectEvens(ms-largestOdds);
        assert ms[x] % 2 == 1;
        assert forall y :: y in ms && ms[y] % 2 == 1 ==> ms[x] >= ms[y];
        assert x in largestOdds+evenPlusRectEvens(ms-largestOdds);
        largestOdds+evenPlusRectEvens(ms-largestOdds)
    else evenPlusRectEvens(ms) 
}

lemma AllEvenOrOneOdd(substr: string, str: string) 
    requires substr in allPalindromSubStrings(str)
    ensures allEven(multiset(substr)) || exists k :: k in multiset(substr) && multiset(substr)[k] % 2 == 1 && forall y :: y != k && y in multiset(substr) ==> multiset(substr)[y] % 2 == 0



lemma {:verify false} lpmGreaterAllPalindromes(str: string)
    ensures forall ss :: ss in allPalindromSubStrings(str) ==> |ss| <= |largePalindromeMultiset(str)|
{
    var lpm := largePalindromeMultiset(str);
    assert lpm <= multiset(str);
    forall ss | ss in allPalindromSubStrings(str) 
        ensures |ss| <= |lpm|
    {
        AllEvenOrOneOdd(ss, str);
        if allEven(multiset(ss)) {
            assert multiset(ss) <= multiset(str);
            assert multiset(ss) <= lpm;
        }else{
            // assert multiset(ss) <= lpm;
            // assert |multiset(ss)| <= |lpm|;
            var largestOdds := largestOdd(multiset(str));
            var k :| k in multiset(ss) && multiset(ss)[k] % 2 == 1;
            var j :| j in lpm && 
        lpm[j] % 2 ==1 && 
        (forall y :: y in multiset(str) && multiset(str)[y] % 2 ==1 ==> lpm[j] >= multiset(str)[y] )
        && forall kk :: kk != j && kk in largePalindromeMultiset(str) ==> largePalindromeMultiset(str)[kk] % 2 == 0;
            assert multiset(ss)[k] <= lpm[j];

            var stub: multiset<char> := multiset{};
            var ssm := multiset(ss)-stub[k := multiset(ss)[k]];
            assert allEven(ssm);
            // assert ssm <= lpm;

        }
    }

}

// lemma largestAllEven(s: string)
//     ensures forall ss :: ss in allStrings(multiset(s)) && allEven(multiset(ss)) ==> |ss| <= |evenPlusRectEvens(multiset(s))|
//     // |evenPlusRectEvens(multiset(s))| 
// {

// }