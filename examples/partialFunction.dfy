//https://stackoverflow.com/questions/77533599/weakest-preconditions-for-higher-order-recursive-function
ghost predicate closedPartial<T(!new)>(f: T ~> T, ts: set<T>) 
    reads f.reads
{
    (forall tx :: tx in ts ==> f.requires(tx)) && forall tx :: tx in ts ==> f(tx) in ts
}

ghost predicate iterativePartial<T(!new)>(f: T ~> T, t: T, n: nat) 
    reads f.reads
{
    if n == 0 then f.requires(t) else f.requires(t) && iterativePartial(f, f(t), n-1)
} 

function funpow1<T(!new)>(n:nat, f: T ~> T,t: T): T
    requires f.requires(t)
    // requires iterativePartial(f, t, n)

    reads f.reads
    requires n <=5
    requires f.requires(t)
    requires f.requires(f(t))
    requires f.requires(f(f(t)))
    requires f.requires(f(f(f(t))))
    requires f.requires(f(f(f(f(t)))))
    requires f.requires(f(f(f(f(f(t))))))
    // // ensures funpow(n,f,t,ts) in ts
    ensures n == 0 ==> funpow1(n, f, t) == t
    ensures n == 1 ==> funpow1(n, f, t) == f(t)
    ensures n == 2 ==> funpow1(n, f, t) == f(f(t))
    ensures n == 3 ==> funpow1(n, f, t) == f(f(f(t)))
    decreases n
{
    if n == 0
    then t
    else f(funpow1(n-1,f,t))
}

function funpow2<T(!new)>(n:nat, f: T ~> T,t: T, ts: set<T>): T
    requires forall tx :: tx in ts ==> f.requires(tx)
    requires forall tx :: tx in ts ==> f(tx) in ts
    requires t in ts
    reads f.reads
    ensures funpow2(n,f,t,ts) in ts
    decreases n
{
  if n == 0
  then t
  else f(funpow2(n-1,f,t,ts))
}

ghost predicate funpow_pred<T(!new)>(n:nat, f: T ~> T,t: T,t':T)
    reads f.reads
{
  (n == 0 && t' == t) ||
  (n > 0 && exists t2 :: funpow_pred(n-1,f,t,t2) && f.requires(t2) && f(t2) == t')
}

// uniqueness
lemma funpow_pred_uniq<T(!new)>(n:nat,f: T ~> T, t:T, t1:T, t2:T)
    requires funpow_pred(n,f,t,t1)
    requires funpow_pred(n,f,t,t2)
    ensures t1 == t2
{
  if n == 0
  {
    assert t1 == t;
    assert t2 == t;
  }
  else
  {
    var t3 :| funpow_pred(n-1,f,t,t3);
    forall t4 | funpow_pred(n-1,f,t,t4)
        ensures funpow_pred(n-1,f,t,t4) ==> t4 == t3
    {
      funpow_pred_uniq(n-1,f,t,t3,t4);
    }
    assert t1 == f(t3);
    assert t2 == f(t3);
  }
}

// use the predicates to state the preconditions
function funpow<T(!new)>(n:nat,f:T~>T,t:T): T
    reads f.reads
    requires n > 0 ==> exists t'' :: funpow_pred(n-1,f,t,t'') && f.requires(t'')
    ensures funpow_pred(n,f,t,funpow(n,f,t))
    ensures forall t'' :: funpow_pred(n,f,t,t'') ==> t'' == funpow(n,f,t)
{
  if n == 0 then t
  else
    ghost var t'' :| funpow_pred(n-1,f,t,t'') && f.requires(t'');
    funpow_pred_uniq(n-1,f,t,funpow(n-1,f,t),t'');
    assert funpow(n-1,f,t) == t'';
    f(funpow(n-1,f,t))
}

// check that this is exactly what I want
lemma funpow_req_lem<T(!new)>(n:nat,f:T~>T,t:T)
ensures (n > 0 ==> funpow.requires(n-1,f,t) && f.requires(funpow(n-1,f,t))) == funpow.requires(n,f,t)
{
}

predicate inrange(i:nat,n:nat)
{
  0 <= i < n
}

ghost predicate exists_funpow_pred<T(!new)>(i:nat,f: T ~> T, t:T)
reads f.reads
{
  exists t' :: funpow_pred(i,f,t,t') && f.requires(t')
}

lemma funpow_pred_forall<T(!new)>(n:nat, f: T ~> T,t: T, t': T)
requires funpow_pred(n,f,t,t')
ensures forall i {:trigger inrange(i,n)} :: 0 <= i < n ==> exists_funpow_pred(i,f,t)
{
  if n == 0
  {
  }
  else
  {
    forall i | 0 <= i < n
    ensures exists_funpow_pred(i,f,t)
    {
      if i == n - 1
      {
        var t' :| funpow_pred(n-1,f,t,t') && f.requires(t');
        assert funpow_pred(i,f,t,t') && f.requires(t');
      }
      else
      {
        var t' :| funpow_pred(n-1,f,t,t') && f.requires(t');
        funpow_pred_forall(n-1,f,t,t');
        assert inrange(i,n-1);
        assert exists t'' :: funpow_pred(i,f,t,t'') && f.requires(t'');
      }
    }
  }
}

// Validate
function foo(n:int):int
requires n < 2
{
  n + 1
}

method Validator()
{
  assert funpow(0,foo,0) == 0;
  funpow_req_lem(1,foo,0);
  assert funpow(1,foo,0) == 1;
  funpow_req_lem(2,foo,0);
  assert funpow(2,foo,0) == 2;
  assert !foo.requires(2);
}

datatype option<T> = Some(t:T) | None

function funpowO<T(!new)>(n:nat,f:T ~> option<T>,t:T): option<T>
    reads f.reads
    requires forall x :: f.requires(x) // make it total
{
  if n == 0 then Some(t)
  else
    match funpowO(n-1,f,t)
      case Some(y) => f(y)
      case None => None
}