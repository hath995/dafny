
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    for i := 0 to |s| 
        invariant mset == multiset(s[0..i])
    {
        assert s == s[0..i] + [s[i]] + s[(i+1)..];
        // assert multiset(s) == multiset(s[0..i])+multiset{s[i]}+multiset(s[(i+1)..]);
        mset := mset + multiset{s[i]};
    }
    assert s == s[0..|s|];
    // assert mset == multiset(s[0..|s|]);
    return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    ghost var sremoved: multiset<char> := multiset{};
    var scopy := s;
    while scopy != multiset{} 
        invariant s - sremoved == scopy
        invariant sremoved !! scopy
        invariant sremoved <= s
        invariant forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x]
    {
        var x :| x in scopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{};
        // assert removed[x := s[x]] <= s;
        sremoved := sremoved + removed[x := s[x]];
        scopy := scopy - removed[x := s[x]];
    }
    // assert scopy == multiset{};
    // assert s - sremoved == scopy;
    // assert sremoved == s;
    // assert forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x];

    ghost var tremoved: multiset<char> := multiset{};
    var tcopy := t;
    while tcopy != multiset{} 
        invariant t - tremoved == tcopy
        invariant tremoved !! tcopy
        invariant tremoved <= t
        invariant forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x]
    {
        var x :| x in tcopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{};
        tremoved := tremoved + removed[x := s[x]];
        tcopy := tcopy - removed[x := s[x]];
    }
    // assert forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x];

    return true;
}

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
    var smset := toMultiset(s);
    var tmset := toMultiset(t);
    equal := msetEqual(smset, tmset);
}

method GroupAnagram(strs: seq<string>) returns (out: seq<seq<string>>) 
    ensures forall anagram :: anagram in out ==> forall i,j :: 0 <= i < j < |anagram| ==> multiset(anagram[i]) == multiset(anagram[j])
{
    out := [];
    var anamap: map<multiset<char>, seq<string>> := map[];
    for i := 0 to |strs| 
        invariant forall key :: key in anamap ==> forall i :: 0 <= i  < |anamap[key]| ==> key == multiset(anamap[key][i])
    {
        var ms := multiset(strs[i]);
        if ms in anamap {
            anamap := anamap[ms := anamap[ms]+[strs[i]]];
        }else{
            anamap := anamap[ms := [strs[i]]];
        }
    }
    var keys := anamap.Keys;
    while keys != {} 
        invariant forall anagram :: anagram in out ==> forall i,j :: 0 <= i < j < |anagram| ==> multiset(anagram[i]) == multiset(anagram[j])
    {
        var x :| x in keys;
        out := out + [anamap[x]];
        keys := keys - {x};
    }
}