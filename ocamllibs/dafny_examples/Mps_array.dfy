function DfMax(x: int, y: int): int { if x > y then x else y}

function Mps(a : seq<int>): int
{ if a == [] then
    0
   else 
   DfMax((Sum(a[..|a|-1]) + a[|a|-1]), Mps(a[..|a|-1]))
   
}

function Sum(a : seq<int>): int
{ if a == [] then  0 else  (Sum(a[..|a|-1]) + a[|a|-1]) 
}

function MpsJoin(leftMps : int, leftSum : int, rightMps : int, rightSum : int): int
{
  DfMax((leftSum + rightMps), leftMps)
}

function SumJoin(leftSum : int, rightSum : int): int
{
  (rightSum + leftSum)
}


lemma BaseCaseMps(a : seq<int>)
  ensures Mps(a) == MpsJoin(Mps(a), Sum(a), Mps([]), Sum([]))
  {}

lemma HomMps(a : seq<int>, R_a : seq<int>)
  ensures Mps(a + R_a) == MpsJoin(Mps(a), Sum(a), Mps(R_a), Sum(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMps(a);
    } else {
    calc{
    Mps(a + R_a);
    =={
      HomSum(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MpsJoin(Mps(a), Sum(a), Mps(R_a), Sum(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseSum(a : seq<int>)
  ensures Sum(a) == SumJoin(Sum(a), Sum([]))
  {}

lemma HomSum(a : seq<int>, R_a : seq<int>)
  ensures Sum(a + R_a) == SumJoin(Sum(a), Sum(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseSum(a);
    } else {
    calc{
    Sum(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    SumJoin(Sum(a), Sum(R_a));
    } // End calc.
  } // End else.
} // End lemma.

