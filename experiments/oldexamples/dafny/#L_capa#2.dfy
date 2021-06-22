function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMin(x: int, y: int): int { if x > y then y else x}

function Sum(a : seq<int>): int
{
  if a == [] then 0 else (Sum(a[..|a|-1]) + a[|a|-1])
}

function C(a : seq<int>): int
{
  if a == [] then 0 else DfMin((C(a[..|a|-1]) - a[|a|-1]), a[|a|-1])
}

function SumJoin(leftSum : int, rightSum : int): int
{
  (rightSum + leftSum)
}

function CJoin(leftSum : int, leftC : int, rightSum : int, rightC : int): int
{
  DfMin(((leftC - (-8)) - (rightSum + 8)), rightC)
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

lemma BaseCaseC(a : seq<int>)
  ensures C(a) == CJoin(Sum(a), C(a), Sum([]), C([]))
  {}

lemma HomC(a : seq<int>, R_a : seq<int>)
  ensures C(a + R_a) == CJoin(Sum(a), C(a), Sum(R_a), C(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseC(a);
    
     } else {
    calc{
    C(a + R_a);
    =={
      HomSum(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    CJoin(Sum(a), C(a), Sum(R_a), C(R_a));
    } // End calc.
  } // End else.
} // End lemma.

