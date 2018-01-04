function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Seen(a : seq<bool>): bool
{
  if a == [] then false else (Seen(a[..|a|-1]) || a[|a|-1])
}

function R(a : seq<bool>): bool
{
  if a == [] then
    true
    else
    (((! a[|a|-1]) && Seen(a[..|a|-1])) || R(a[..|a|-1]))
}

function SeenJoin(leftSeen : bool, rightSeen : bool): bool
{
  (rightSeen || (leftSeen || false))
}

function RJoin(leftR : bool, leftSeen : bool, rightR : bool, rightSeen : bool): bool
{
  (((rightSeen || rightR) && (rightSeen || rightR)) || (rightSeen || rightR))
}


lemma BaseCaseSeen(a : seq<bool>)
  ensures Seen(a) == SeenJoin(Seen(a), Seen([]))
  {}

lemma HomSeen(a : seq<bool>, R_a : seq<bool>)
  ensures Seen(a + R_a) == SeenJoin(Seen(a), Seen(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseSeen(a);
    
     } else {
    calc{
    Seen(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    SeenJoin(Seen(a), Seen(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseR(a : seq<bool>)
  ensures R(a) == RJoin(R(a), Seen(a), R([]), Seen([]))
  {}

lemma HomR(a : seq<bool>, R_a : seq<bool>)
  ensures R(a + R_a) == RJoin(R(a), Seen(a), R(R_a), Seen(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseR(a);
    
     } else {
    calc{
    R(a + R_a);
    =={
      HomSeen(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    RJoin(R(a), Seen(a), R(R_a), Seen(R_a));
    } // End calc.
  } // End else.
} // End lemma.

