function DfMax(x: int, y: int): int { if x > y then x else y}

function M(a : seq<int>): int
{ if a == [] then  0 else  DfMax(M(a[..|a|-1]), a[|a|-1]) 
}

function MJoin(leftM : int, rightM : int): int
{
  DfMax((0 - rightM), DfMax(leftM, rightM))
}


lemma BaseCaseM(a : seq<int>)
  ensures M(a) == MJoin(M(a), M([]))
  {}

lemma HomM(a : seq<int>, R_a : seq<int>)
  ensures M(a + R_a) == MJoin(M(a), M(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseM(a);
    } else {
    calc{
    M(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    MJoin(M(a), M(R_a));
    } // End calc.
  } // End else.
} // End lemma.

