function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function DfMin(x: int, y: int): int { if x > y then y else x}

function M(a : seq<int>): int
{
  if a == [] then 0 else DfMin(M(a[..|a|-1]), a[|a|-1])
}

function M2(a : seq<int>): int
{
  if a == [] then 0 else DfMin(M2(a[..|a|-1]), DfMax(M(a[..|a|-1]), a[|a|-1]))
}

function MJoin(leftM : int, rightM : int): int
{
  DfMin(rightM, leftM)
}

function M2Join(leftM2 : int, leftM : int, rightM2 : int, rightM : int): int
{
  DfMin(DfMax((rightM + DfMin(0, 0)), leftM), DfMin(rightM2, leftM2))
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

lemma BaseCaseM2(a : seq<int>)
  ensures M2(a) == M2Join(M2(a), M(a), M2([]), M([]))
  {}

lemma HomM2(a : seq<int>, R_a : seq<int>)
  ensures M2(a + R_a) == M2Join(M2(a), M(a), M2(R_a), M(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseM2(a);
    
     } else {
    calc{
    M2(a + R_a);
    =={
      HomM(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    M2Join(M2(a), M(a), M2(R_a), M(R_a));
    } // End calc.
  } // End else.
} // End lemma.

