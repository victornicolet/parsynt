function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function M(a : seq<int>): int
{
  if a == [] then
    0
    else
    (if (M(a[..|a|-1]) < a[|a|-1]) then a[|a|-1] else M(a[..|a|-1]))
}

function MJoin(leftM : int, rightM : int): int
{
  (if (rightM == (1 + rightM)) then rightM else DfMax(rightM, leftM))
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

