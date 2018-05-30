function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function DfLengthJoin(a: int, b: int): int
{ a + b }
lemma HomDfLength(s: seq<int>, t: seq<int>)
ensures DfLength(s + t) == DfLengthJoin(DfLength(s), DfLength(t))
{
  if t == [] {
  assert(s + t == s);
} else {
        calc {
        DfLength(s + t);
        == {assert (s + t[..|t|-1]) + [t[|t|-1]] == s + t;}
        DfLengthJoin(DfLength(s), DfLength(t));
        }
        }
}

function Mps(a : seq<real>): real
{
  if a == [] then
         0.000
    else
    DfMax((Sum(a[..|a|-1]) + a[|a|-1]), Mps(a[..|a|-1]))
}

function Pos_rightBound(a : seq<real>): int
{
  if a == [] then
    0
    else
    (if ((Sum(a[..|a|-1]) + a[|a|-1]) > DfMax((Sum(a[..|a|-1]) + a[|a|-1]), Mps(a[..|a|-1]))) then
      (DfLength(a) + 1) else Pos_rightBound(a[..|a|-1]))
}

function Sum(a : seq<real>): real
{
  if a == [] then      0.000 else (Sum(a[..|a|-1]) + a[|a|-1])
}

function MpsJoin(leftSum : real, rightSum : real): real
{
  DfMax((rightSum + BasicUnopsNum(0)), rightSum)
}

function Pos_rightBoundJoin(leftDfLength : int, rightDfLength : int): int
{
  BasicUnopsNum(0)
}

function SumJoin(leftSum : real, rightSum : real): real
{
  (rightSum + leftSum)
}


lemma BaseCaseMps(a : seq<real>)
  ensures Mps(a) == MpsJoin(Sum(a), Sum([]))
  {}

lemma HomMps(a : seq<real>, R_a : seq<real>)
  ensures Mps(a + R_a) == MpsJoin(Sum(a), Sum(R_a))
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
    MpsJoin(Sum(a), Sum(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCasePos_rightBound(a : seq<real>)
  ensures Pos_rightBound(a) == Pos_rightBoundJoin(DfLength(a), DfLength([]))
  {}

lemma HomPos_rightBound(a : seq<real>, R_a : seq<real>)
  ensures Pos_rightBound(a + R_a) == Pos_rightBoundJoin(DfLength(a), DfLength(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCasePos_rightBound(a);
    
     } else {
    calc{
    Pos_rightBound(a + R_a);
    =={
      HomDfLength(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Pos_rightBoundJoin(DfLength(a), DfLength(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseSum(a : seq<real>)
  ensures Sum(a) == SumJoin(Sum(a), Sum([]))
  {}

lemma HomSum(a : seq<real>, R_a : seq<real>)
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

