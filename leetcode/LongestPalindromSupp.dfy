
include "../lib/seq.dfy"
module Palindrome {
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

    predicate IsPalindromeK(s: string) {
        forall i :: 0 <= i < |s| ==> s[i] == s[|s|-i-1]
    }

    lemma PalindromeLeft(s: string)
        requires IsPalindrome(s)
        ensures IsPalindromeK(s)
    {
        ReverseIndexAll(s);
    }

    lemma PalindromeRight(s: string)
        requires IsPalindromeK(s)
        ensures IsPalindrome(s)
    {
        ReverseIndexAll(s);
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

    lemma multisetSubsetSmallerEqual<T(==)>(ms: multiset<T>, mss: multiset<T>)
        requires mss <= ms
        ensures |mss| <= |ms|
    {
        if |ms| == 0 {

        }else{
            var x :| x in ms;
            if mss[x] == ms[x] {
                multisetSubsetSmallerEqual(ms[x:=0], mss[x:=0]);
            }else if mss[x] < ms[x] {
                if mss[x:=0] < ms[x:=0] {
                    multisetSubsetSmallerEqual(ms[x:=0], mss[x:=0]);
                }else{
                    assert mss[x:=0] == ms[x:=0];
                    assert |mss[x:=0]| == |ms[x:=0]|;
                    assert |mss| < |ms|;

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
                multisetSubsetSmaller(ms, multiset(xx));
        }
    }

    method Test() {
        var example := "abcqqqcba";
        assert IsPalindrome(example);
        var ms:= multiset(example);
        assert example in allPalindromeStrings(ms);
    }
    lemma LargestOddsEmpty(ms: multiset<char>)
        requires largestOdd(ms) == multiset{}
        ensures allEven(ms)
    {
        var candidates: set<char> := set x | charCountOdd(x,ms) && (forall y :: charCountOdd(y,ms) ==> ms[x] >= ms[y]);
        assert |candidates| == 0;
        var odds := set x | charCountOdd(x, ms);
        assert odds == {} by {
            if odds != {} {
                var zs := set z | z in odds :: ms[z];
                var z :| charCountOdd(z, ms);
                assert z in odds;
                assert ms[z] in zs;
                ThereIsAMaximum(zs);
                var max :| max in zs && forall y :: y in zs ==> max >= y;
                var q :| q in odds && ms[q] == max;
                assert charCountOdd(q, ms);
                forall y | charCountOdd(y, ms)
                    ensures max >= ms[y]
                {
                    assert y in odds;
                    assert ms[y] in zs;
                }
                assert q in candidates;
            }
        }
        if !(forall x :: ms[x] % 2 == 0) {
            var x :| ms[x]%2 ==1;
            assert x in odds;
        }
    }

    ghost function largestOdd(ms: multiset<char>) : multiset<char> 
        ensures largestOdd(ms) != multiset{} ==> forall x :: x in largestOdd(ms) ==> ms[x] % 2 == 1
        // ensures largestOdd(ms) == multiset{} ==> forall x :: ms[x] % 2 == 0
    {
        var candidates: set<char> := set x | charCountOdd(x,ms) && (forall y :: charCountOdd(y,ms) ==> ms[x] >= ms[y]);
        var stub: multiset<char> := multiset{};
        if |candidates| == 0 then 
            multiset{}
        else var x :| x in candidates; stub[x := ms[x]]
    }

    lemma noLargestNoOdds(ms: multiset<char>)
        requires (set x | charCountOdd(x, ms) && (forall y :: charCountOdd(y, ms) ==> ms[x] >= ms[y])) == {}
        ensures allEven(ms)
    {
        var largest := (set x | charCountOdd(x, ms) && (forall y :: charCountOdd(y, ms) ==> ms[x] >= ms[y]));
        assert largest == {};
        if !(forall x :: x in ms ==> ms[x] % 2 == 0) {
            var y :| y in ms && ms[y] % 2 == 1;
            var  odds := set x | charCountOdd(x, ms);
            assert y in odds;
            var sizes := set x | charCountOdd(x, ms) :: ms[x];
            assert ms[y] in sizes;
            ThereIsAMaximum(sizes);
            var max :| max in sizes && forall z :: z in sizes ==> max >= z;
            var q :| q in odds && ms[q] == max;
            assert charCountOdd(q, ms);
            forall x | charCountOdd(x, ms)
                ensures ms[q] >= ms[x]
            {
                assert x in odds;
                assert ms[x] in sizes;
            }
            assert q in largest;
        }
    }

    lemma largestExistsRev(ms: multiset<char>)
        requires exists y :: y in ms && ms[y] % 2 == 1 && forall x :: x in ms && ms[x] % 2 == 1 && ms[y] >= ms[x]
        ensures (set x | x in ms && ms[x] % 2 == 1) != {}
    {
        var res := (set x | x in ms && ms[x] % 2 == 1);
        var y :| exists y :: y in ms && ms[y] % 2 == 1 && forall x :: x in ms && ms[x] % 2 == 1 && ms[y] >= ms[x];
        assert y in res;
    }

    lemma ThereIsAMaximum(s: set<int>)
    requires s != {}
    ensures exists x :: x in s && forall y :: y in s ==> x >= y
    {
    var x :| x in s;
    if s == {x} {
    } else {
        var s' := s - {x};
        assert s == s' + {x};
        ThereIsAMaximum(s');
    }
    }

    predicate charCountOdd(x: char, ms: multiset<char>) {
        x in ms && ms[x] % 2 == 1
    }

    predicate charCountEven(x: char, ms: multiset<char>) {
        x in ms && ms[x] % 2 == 0
    }

    lemma LargestExists(ms: multiset<char>)
    requires (set x | charCountOdd(x, ms)) != {}
    ensures exists x :: charCountOdd(x, ms) && (forall y :: charCountOdd(y, ms) ==> ms[x] >= ms[y])
    {
    var odds := set x| charCountOdd(x, ms);
    assert odds != {};
    var counts := set x | charCountOdd(x, ms) :: ms[x];
    var x :| x in odds;
    assert ms[x] in counts;
    assert counts != {};
    ThereIsAMaximum(counts);
    var max :| max in counts && forall y :: y in counts ==> max >= y;
    var q :| q in odds && ms[q] == max;
    assert charCountOdd(q, ms);
    forall y | charCountOdd(y, ms)
        ensures max >= ms[y]
    {
        assert y in odds;
        assert ms[y] in counts;
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
        // ensures largestOdd(multiset(str)) != multiset{} ==> exists k :: k in largePalindromeMultiset(str) && largePalindromeMultiset(str)[k] % 2 ==1 && 
        ensures largestOdd(multiset(str)) != multiset{} ==> exists k :: charCountOdd(k,largePalindromeMultiset(str)) && 
            (forall y :: charCountOdd(y, multiset(str)) ==> largePalindromeMultiset(str)[k] >= multiset(str)[y] )
            && forall kk :: kk != k && kk in largePalindromeMultiset(str) ==> charCountEven(kk, largePalindromeMultiset(str))
        ensures largePalindromeMultiset(str) <= multiset(str)
        ensures forall zz :: zz in largePalindromeMultiset(str) && largePalindromeMultiset(str)[zz] % 2 == 0 ==> largePalindromeMultiset(str)[zz] <= multiset(str)[zz]
        ensures forall zz :: zz in largePalindromeMultiset(str) && largePalindromeMultiset(str)[zz] % 2 == 0 ==> largePalindromeMultiset(str)[zz] == multiset(str)[zz]||largePalindromeMultiset(str)[zz] == multiset(str)[zz]-1
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
        ensures allEven(multiset(substr)) || exists k :: charCountOdd(k, multiset(substr)) && forall y :: y != k && y in multiset(substr) ==>charCountEven(y,multiset(substr))


    lemma twoInMultisetGreaterThan1(s: string, i: int, j: int, c: char)
        requires i != j
        requires 0 <= i < |s|
        requires 0 <= j < |s|
        requires s[i] == c
        requires s[j] == c
        ensures multiset(s)[c] > 1
    {
        if i < j {
            assert s==s[..i]+[c]+s[(i+1)..j]+[c]+s[(j+1)..];
        }else{
            assert s==s[..j]+[c]+s[(j+1)..i]+[c]+s[(i+1)..];

        }
    }


    lemma PalindromeNotPalindrome(s: string, c: char)
        requires IsPalindrome(s)
        requires c in s && multiset(s)[c] == 1
        requires |s| % 2 == 0 || s[|s|/2] != c
        ensures !IsPalindrome(s)
    {
        PalindromeLeft(s);
        assert |s| > 0;
        if |s| % 2 == 0 {
            var i :| 0 <= i < |s| && s[i] == c;
            var j := |s|-i-1;
            assert j != i;
            if s[j] == c {
                twoInMultisetGreaterThan1(s,i,j,c);
                assert false;
            }
            assert s[|s|-i-1] != c;

        }else if s[|s|/2] != c {
            var i :| 0 <= i < |s| && s[i] == c;
            var j := |s|-i-1;
            assert j != i;
            if s[j] == c {
                twoInMultisetGreaterThan1(s,i,j,c);
                assert false;
            }
            assert s[|s|-i-1] != c;

        }
    }

    lemma {:verify false} PalindromeNotPalindromeAgain(s: string, c: char, n: nat)
        requires IsPalindrome(s)
        requires n %2 == 1
        requires c in s && multiset(s)[c] == n
        requires |s| % 2 == 0 || s[|s|/2] != c
        ensures !IsPalindrome(s)
    {
        PalindromeLeft(s);
        if multiset(s)[c] == 1 {
            PalindromeNotPalindrome(s,c);
        }else{
            var i :| 0 <= i < |s| && s[i] == c;
            if s[|s|-i-1] == c {
                PalindromeNotPalindromeAgain(s,c,n-2);
            }else{

            }
        }
    }


    lemma {:verify false} lpmGreaterAllPalindromes(str: string)
        ensures forall ss :: ss in allPalindromSubStrings(str) ==> |ss| <= |largePalindromeMultiset(str)|
    {
        var lpm := largePalindromeMultiset(str);
        assert lpm <= multiset(str);
        forall ss | ss in allPalindromSubStrings(str) 
            ensures |ss| <= |lpm|
        {
            assert |ss| == |multiset(ss)|;
            AllEvenOrOneOdd(ss, str);
            if allEven(multiset(ss)) {
                assert multiset(ss) <= multiset(str);
                assert multiset(ss) <= lpm;
            }else{
                assert !allEven(multiset(ss));
                assert multiset(ss) <= multiset(str);
                // assert multiset(ss) <= lpm;
                // assert |multiset(ss)| <= |lpm|;
                var largestOdds := largestOdd(multiset(str));
                if largestOdds == multiset{} {
                    LargestOddsEmpty(largestOdds);
                    /*
                    I assumed that if largestOdds was empty then the substring odds would be empty
                    but it could be the substring odd char was an even char in the original string
                    */
                    assert false;
                }else{
                var lo :| lo in largestOdds && lo in lpm;
                var k :| charCountOdd(k, multiset(ss)) && forall y :: y != k && y in multiset(ss) ==> charCountEven(y, multiset(ss));
                var j :| charCountOdd(j, lpm) && (forall y :: charCountOdd(y, multiset(str)) ==> lpm[j] >= multiset(str)[y] ) && forall kk :: kk != j && kk in lpm ==> charCountEven(kk, lpm);
                assert lo == j;
                // assert charCountOdd(k ,multiset(str));
                // if k in LargestExists
                // assert multiset(ss)[k] <= lpm[j];

                var stub: multiset<char> := multiset{};
                var ssm := multiset(ss)-stub[k := multiset(ss)[k]];
                assert allEven(ssm);
                assert ssm <= lpm;
                if charCountEven(k, multiset(str)) {
                    assert multiset(ss)[k] < lpm[k];
                    assert multiset(ss) <= lpm;
                    multisetSubsetSmallerEqual(lpm, multiset(ss));
                    assert |multiset(ss)| <= |lpm|;
                }else {
                    /**
                        "aaabbbxxzzq"
                        lpm == "aaabbxxzz"
                        j=="a"
                        k=="b"
                        ss == "bbbaaxxzz"
                    */
                    assert charCountOdd(k, multiset(str));
                    assert multiset(ss)[k] <= lpm[j];
                    if k in lpm {

                    assume |multiset(ss)| <= |lpm|;
                    }else{

                    assume |multiset(ss)| <= |lpm|;
                    }
                    // assert multiset(ss) <= lpm;
                    // multisetSubsetSmallerEqual(lpm, multiset(ss));
                }
                }
                // assert ssm <= lpm;

            }
        }

    }

    // lemma largestAllEven(s: string)
    //     ensures forall ss :: ss in allStrings(multiset(s)) && allEven(multiset(ss)) ==> |ss| <= |evenPlusRectEvens(multiset(s))|
    //     // |evenPlusRectEvens(multiset(s))| 
    // {

    // }
}