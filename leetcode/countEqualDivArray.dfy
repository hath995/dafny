// https://leetcode.com/problems/count-equal-and-divisible-pairs-in-an-array/
/*
function countPairs(nums: number[], k: number): number {
    let count = 0;
    for(let i = 0; i < nums.length-1; i++) {
        for(let j = i+1; j < nums.length; j++) {
            if(nums[i] == nums[j] && (i*j) % k == 0) {
                count++;
            }
        }
    }
    return count;
};
*/

function pairs(nums: seq<nat>, k: nat): set<(int, int)> 
    requires k > 0
{
    set x,y | 0 <= x < y < |nums| && satPairs(nums, k, x, y) :: (x,y)
}

function pairsI(nums: seq<nat>, k: nat, i: nat): set<(nat, nat)> 
    requires k > 0
    requires 0 <= i < |nums|
    // ensures forall x,y :: 0 <= x < i && x < y < |nums| && satPairs(nums, k, x, y) ==> (x,y) in pairsI(nums, k, i)
{
    set x: nat,y:nat | 0 <= x < i && x < y < |nums| && satPairs(nums, k, x, y) :: (x,y)
}


function pairsJ(nums: seq<nat>, k: nat, i: nat, j: nat): set<(nat, nat)> 
    requires 0 <= i < |nums|
    requires i < j
    requires k > 0
    // ensures forall x :: i < x < j < |nums| && satPairs(nums, k, i, x) ==> (i,x) in pairsJ(nums, k, i, j)
{
    set x: nat | i < x < j <= |nums| && satPairs(nums, k, i, x) :: (i,x)
}

lemma PairsIMaint(nums: seq<nat>, k: nat, i: nat) 
    requires k > 0
    requires 0 <= i <= |nums|-2
    ensures pairsI(nums, k, i+1) == pairsI(nums, k, i)+pairsJ(nums, k, i, |nums|)
{
}
    // forall pairs | pairs in pairsI(nums, k, i) 
    //     ensures pairs in pairsI(nums, k, i+1)
    // {

    // }
    // forall jpairs | jpairs in pairsJ(nums, k, i, |nums|)
    //     ensures jpairs in pairsI(nums,k,i+1)
    // {

    // }

    // forall pairs | pairs in pairsI(nums, k, i+1) 
    //     ensures pairs in (pairsI(nums, k, i)+pairsJ(nums, k, i, |nums|))
    // {
    //     if pairs in pairsI(nums, k,i) {

    //     }else if pairs in pairsJ(nums, k,i,|nums|) {

    //     }else{
    //         assert 0<= pairs.0 < i+1;
    //         assert pairs.0 < pairs.1 <= |nums|-1;
    //         if 0 <= pairs.0 < i {
    //             assert pairs in pairsI(nums,k,i);
    //         }

    //         if pairs.0 == i {
    //             assert pairs in pairsJ(nums,k,i, |nums|);
    //         }
    //         assert false;
    //     }
    // }

method Test2() {
    var test := [4,1,2,2,2,4,4];
    assert |test| == 7;
    var pairs := pairsI(test, 2, 0);
    assert pairs == {};
    var testpairs := pairsI(test, 2, |test|-2);
    assert (5,6) in pairsJ(test,2,|test|-2,|test|);
    assert (0,6) in testpairs;

}

function satPairs(nums: seq<nat>, k: nat, a: nat, b: nat): bool
    requires k > 0
    requires a < b < |nums| 
{
    nums[a] == nums[b] && (a*b) % k == 0
}

method countPairs(nums: seq<nat>, k: nat) returns (count: nat) 
    requires k > 0
    requires |nums| >= 2
    ensures count == |pairs(nums,k)|
{
    count := 0;
    ghost var cpairs: set<(nat, nat)> := {};
    for i : nat := 0 to |nums|-1 
        invariant cpairs == pairsI(nums, k, i)
        invariant count == |pairsI(nums, k, i)|
    {
        ghost var occount := count;
        ghost var increment := 0;
        ghost var pairset: set<(nat, nat)> := {};
        var j : nat := i+1;
        while j < |nums| 
            invariant i+1 <= j <= |nums|
            invariant pairset == pairsJ(nums,k, i,j)
            invariant increment == |pairsJ(nums,k,i,j)|
            invariant count == occount + increment
            // invariant cpairs !! pairset
        {
            if  i+1 <= j <= j && satPairs(nums, k, i, j) {
                increment := increment + 1;
                pairset := pairset+{(i,j)};
                count := count + 1;
            }
            j := j + 1;
        }
        // assert j==|nums|;
        PairsIMaint(nums,k,i);
        cpairs := cpairs + pairset;
    }
    assert pairsI(nums,k, |nums|-1) == pairs(nums,k);
}

// method Test() {
//     //                0 1 2 3 4 5 6
//     var something := [3,1,2,2,2,1,3];
//     var what := pairs(something, 2);
//     assert (0,6) in what;
//     assert (2,3) in what;
//     assert (2,4) in what;
//     assert (3,4) in what;

//     assert (0,4) !in what;
//     assert (0,0) !in what;
//     assert (0,1) !in what;
//     assert (0,2) !in what;
//     assert (0,3) !in what;
//     assert (0,5) !in what;
//     assert (2,6) !in what;
//     assert (1,0) !in what;
//     assert (1,1) !in what;
//     assert (1,2) !in what;
//     assert (1,3) !in what;
//     assert (1,4) !in what;
//     assert (1,5) !in what;
//     assert (1,6) !in what;
//     assert (2,1) !in what;
//     assert (2,2) !in what;
//     assert (2,5) !in what;
//     assert (2,6) !in what;

//     assert (3,0) !in what;
//     assert (3,1) !in what;
//     assert (3,2) !in what;
//     assert (3,3) !in what;
//     assert (3,5) !in what;
//     assert (3,6) !in what;

//     assert (4,0) !in what;
//     assert (4,1) !in what;
//     assert (4,2) !in what;
//     assert (4,3) !in what;
//     assert (4,4) !in what;
//     assert (4,5) !in what;
//     assert (4,6) !in what;

//     assert (5,0) !in what;
//     assert (5,1) !in what;
//     assert (5,2) !in what;
//     assert (5,3) !in what;
//     assert (5,4) !in what;
//     assert (5,5) !in what;
//     assert (5,6) !in what;

//     assert (6,0) !in what;
//     assert (6,1) !in what;
//     assert (6,2) !in what;
//     assert (6,3) !in what;
//     assert (6,4) !in what;
//     assert (6,5) !in what;
//     assert (6,6) !in what;
//     assert (7,0) !in what;
//     assert (7,1) !in what;
//     assert (7,2) !in what;
//     assert (7,3) !in what;
//     assert (7,4) !in what;
//     assert (7,5) !in what;
//     assert (7,6) !in what;
//     assert (7,7) !in what;

//     assert |what| == matchPairs(something,2);
//     // assert |what| == 4;
//     assert matchPairs(something, 2) == 4;
// }