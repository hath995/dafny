lemma selfDivision(a: int) 
    requires a != 0;
    ensures a % a == 0;
{
}

lemma modMultiplication(aone: int, bone: int, atwo: int, btwo: int, n: int)
    requires n != 0
    requires aone % n == bone
    requires atwo % n == btwo
    ensures (aone * atwo) % n == (bone * btwo) % n 


lemma selfAnnihilation(a: int, b: int) 
    requires a != 0
    ensures (b*a) % a == 0
{
    calc {
        (b * a) % a;
        {modMultiplication(a,0,b,b%a,a);}
        (0 * b%a) % a;
        0;
    }
}

// method Test() {
//     var q : int := 4;
//     var z : int :| assume z != 0;
//     // selfDivision(z);
//     assert z % z == 0;
// }

// lemma DivisionTheorem(a: int, b: int) returns (x: int)
//     requires a != 0
//     requires b % a == 0
//     ensures exists x :: x * a == b
// {
//    x := b / a;
//    assert x * a == b;
// }

lemma DivisionTheorem(a: int, b: int)
    requires a != 0
    requires b % a == 0
    ensures exists x :: x * a == b
{
   var x := b / a;
   assert x * a == b;
}

lemma divCancel(x: int, a: int) 
    requires a != 0
    requires x % a == 0
    ensures (x/a)*a == x;
// {
//     if a != 0 && x % a == 0 {
//         var q := x/a;
//         assert q*a == x;
//     }
// }

lemma remainderSubtract(x: int, a: int, c: int) 
    requires a != 0
    requires c == x % a
    ensures (x-c) % a == 0
// {
// }

function divAdd(b: int, a: int, c: int): int {
    b * a + c
}

lemma remainderTheorem(x: int, a: int, c: int)
    requires a != 0
    requires x % a == c;
    ensures exists q  :: divAdd(q,a,c) == x
{
   var q := (x-c) / a;
   remainderSubtract(x,a,c);
//    calc {
//        q * a + c;
//        ((x-c)/a) * a + c;
//        {divCancel(x-c, a);}
//        (x-c)+c;
//        x;
//    }
   assert divAdd(q,a,c) == x;
}

lemma dpOne(a: int, b: int, c: int) 
    requires a != 0
    requires b != 0
    requires b % a == 0
    requires c % b == 0
    ensures c % a == 0
{
    if b % a == 0 && c % b == 0 && b != 0 && a != 0 {
        DivisionTheorem(a,b);
        var x :| x * a == b;
        DivisionTheorem(b,c);
        var y :| y * b == c;
        calc {
            c % a ;
            (y*b) % a;
            (y*(x*a))%a;
            y*x*a % a;
            {selfAnnihilation(a, y*x);}
            0;
        }        
    }
}

lemma xsquaredminusOne(x: int)
    requires (x*x-1) % 3 != 0
    ensures x % 3 == 0
{
    if x % 3 == 0 {

    }
    if x % 3 == 1 {
        remainderTheorem(x, 3, 1);
        var q: int :| divAdd(q,3,1) == x;
        calc {
            x*x-1;
            (3*q+1)*(3*q+1)-1;
            (9*q*q + 6*q + 1)-1;
            9*q*q + 6*q;
            3*(3*q*q+2*q);
        }

    }

    if x % 3 == 2 {
        remainderTheorem(x, 3, 2);
        var p :| divAdd(p,3,2) == x;
        calc {
            x*x-1;
            (3*p+2)*(3*p+2)-1;
            (9*p*p+12*p+4)-1;
            9*p*p+12*p+3;
            3*(3*p*p+4*p+1);
        }
    }
}

lemma setUnionDifference<T>(a: set<T>, b: set<T>) 
    ensures (a+b)-(a*b) == (a-b)+(b-a)
{

}

lemma simplification<T>(a: set<T>, b: set<T>)
    ensures a+b == a <==> b <= a
{

}

function cartesianProduct<T>(A: set<T>, B: set<T>): set<(T,T)> 
{
    set a,b | a in A && b in B :: (a,b)
}

lemma cartestianSubsets<T>(A: set<T>, B: set<T>, C: set<T>, D: set<T>) 
    requires A <= C
    requires B <= D
    ensures cartesianProduct(A,B) <= cartesianProduct(C,D)
{

}

lemma cartestianUnion<T>(A: set<T>, B: set<T>, C: set<T>) 
    ensures cartesianProduct(A,B+C) == cartesianProduct(A,B)+cartesianProduct(A,C)
{

}
lemma cartestianDifference<T>(A: set<T>, B: set<T>, C: set<T>) 
    ensures cartesianProduct(A,B-C) == cartesianProduct(A,B)-cartesianProduct(A,C)
{

}

function integersc1mod2(): iset<int> {
    iset n: int | n % 2 == 1 :: n
}

function integersc3mod4(): iset<int> {
    iset n: int | n % 4 == 3 :: n
}

lemma smuh(A: iset<int>, B: iset<int>) 
    requires A == integersc1mod2()
    requires B == integersc3mod4()
    ensures B <= A
{
    // var n :| assume n in B;
    forall n | n in B 
        ensures n in A
    {
        assert n % 4 == 3;
        remainderTheorem(n,4,3);
        var q :| divAdd(q,4,3) == n;
        assert n == 2*(2*q+1)+1;
        // selfAnnihilation(2,2*q+1);
        assert 2*(2*q+1) % 2 == 0;
        assert n % 2 == 1;
        assert n in A;
    }
    
}

lemma modPlus(a: int, b: int, n: int)
    requires n != 0;
    ensures ((a % n) + (b % n)) % n == (a + b) % n
