

method recursiveActivitySelector(start: seq<nat>, finish: seq<nat>, k: nat, n: nat) returns (a: set<nat>)
    requires |start| == n
    requires |finish| == n
    requires 1 < k <= n
    requires forall i :: 0 <= i < n ==> start[i] < finish[i]
    requires forall i :: 0 <= i < n-1 ==> finish[i] <= finish[i+1]
    decreases n-k;
{
    var m := k+1;
    while m <= n && start[m-1] < finish[k-1] 
    {
        m := m + 1;
    }
    if m <= n {
        var res := recursiveActivitySelector(start, finish, k+1, n);
        return {m} + res;
    }else{
        return {};
    }
}

method activitySelector(start: seq<nat>, finish: seq<nat>) returns (A: set<nat>)
    requires |finish| >= 1
    requires |start| == |finish|
    requires forall i :: 0 <= i < |finish| ==> start[i] < finish[i]
    requires forall i :: 0 <= i < |finish|-1 ==> finish[i] <= finish[i+1]
    ensures forall x :: x in A ==> 1 <= x <= |finish|
    ensures forall x,y :: x in A && y in A && x < y ==> finish[x-1] < start[y-1]
{
    var n := |finish|;
    A := {1};
    var k := 1;
    var m := 2;
    while m <= n 
        invariant k < m
    {
        if start[m-1] >= finish[k-1] {
            A := A + {m};
            k := m;
        }
        m := m + 1;
    }
    return A;
}