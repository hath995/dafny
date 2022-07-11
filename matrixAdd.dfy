

method matrixAdd(left: array2<real>, right: array2<real>, m: nat, n: nat) returns (result: array2<real>)
    requires m > 0 && n > 0
    requires left.Length0 == right.Length0 && left.Length0 == m && left.Length1 == right.Length1 && left.Length1 == n
    ensures result.Length0 == left.Length0 && result.Length1 == left.Length1
    ensures forall i, j :: 0 <= i < m && 0 <= j < n ==> result[i,j] == left[i,j] + right[i,j]
{
    result := new real[m,n];
    // for i := 0 to m -1 
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall x, j :: 0 <= x < i && 0 <= j < n ==> result[x,j] == left[x,j] + right[x,j];
    {
        // for j := 0 to n - 1 
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant forall x, j :: 0 <= x < i && 0 <= j < n ==> result[x,j] == left[x,j] + right[x,j];
            invariant forall x :: 0 <= x < j  <= n ==> result[i,x] == left[i,x] + right[i,x]
        {
            result[i,j] := left[i,j] + right[i,j];
            j := j + 1;
        }
        i := i + 1;
    }
}