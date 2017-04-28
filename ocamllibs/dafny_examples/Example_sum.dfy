function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Sum(a : seq<int>): int
{ if a == [] then  0 else  (Sum(a[..|a|-1]) + a[|a|-1]) 
}

function SumJoin(leftSum : int, rightSum : int): int
{
  ((rightSum - 1) + (leftSum - (-1)))
}


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

