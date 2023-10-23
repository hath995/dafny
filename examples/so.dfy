class Car {

}
class ParkingSpace {
    var SpaceID: int;
    var Occupied: int;
    var Reservation: string;
    var Location: string;
    var Car: Car?;
    ghost var repr: set<object>;
    
       constructor(id: int, filled: int, reservation: string, location: string) 
          requires id != 0
          requires filled == 0 || filled == 1
          requires (location == "Regular" || location == "Subscription") && location != ""
          requires (reservation == "None" || |reservation| == 7) && reservation != "" 
          requires forall i :: 0 <= i < |reservation| ==> ('a' <= reservation[i] <= 'z' || 'A' <= reservation[i] <= 'Z' || '0' <= reservation[i] <= '9')    {
          SpaceID := id;
          Occupied := filled;
          Reservation := reservation;
          Location := location;
          Car := null;
    
          this.repr := this.repr + {this};    }
    
       method setOccupied(count: int) 
            modifies this
            ensures this.Occupied == count;
        {
            this.Occupied := count;
        }
    
    }

method closeCarPark(Spaces: seq<ParkingSpace>) returns (newSpaces: seq<ParkingSpace>)
        requires forall i :: 0 <= i < |Spaces| ==> Spaces[i].Occupied != 0;
      modifies set space | space in Spaces
      ensures forall i :: 0 <= i < |Spaces| ==> Spaces[i].Occupied == 0
   {
      var i := 0;

      while i < |Spaces|
        invariant 0 <= i <= |Spaces|
        invariant forall k :: 0 <= k < i ==> Spaces[k].Occupied == 0
      {

         Spaces[i].setOccupied(0);

         i := i + 1;
      }

      return Spaces;
   }

predicate first_element_is_maximal(a: array<int>, m: int)
requires 1 <= m <= a.Length;
reads a
{
  forall k: int {:trigger a[(1)-1] >= a[(k)-1]} :: 1 <= k <= m ==> a[(1)-1] >= a[(k)-1]
}

predicate SortedDesc(a: array<int>) 
   reads a
{
   forall i,j :: 0 <= i < j < a.Length ==> a[i] >= a[j]
}

// predicate sortedRec(a: array<int>) {
//     if a.Length == 0 then true else (forall y :: y in a[1..] ==> a[0] <= y) && sortedRec(a[1..])
// }

function contains(xs: seq<int>, x: int): bool {
   exists k : nat | k < |xs| :: xs[k] == x
}

method find(xs:seq<int>, x: int) returns (r: nat)
   requires contains(xs, x)
   ensures 0 <= r < |xs| && xs[r] == x
{
   for i := 0 to |xs| 
      invariant contains(xs[i..], x) 
   {
      if xs[i] == x {return i;}
   }
   assert false;
}
// somehow Dafny infers that i > 0;
method indexOf(xs:seq<int>, x: int) returns (r: nat)
   // requires contains(xs, x)
   ensures r <= |xs|
   ensures (r < |xs|) ==> (xs[r] == x)
{
   var i: int := 0;
   while i < |xs|
      invariant i <= |xs|
   {
      if xs[i] == x { break; }
      i := i + 1;
   }
   return i;
}