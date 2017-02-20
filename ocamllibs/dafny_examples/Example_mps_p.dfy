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

function Mps(a : seq<int>): int
{ if a == [] then
    0
   else 
   DfMax(Mps(a[..|a|-1]), (Sum(a[..|a|-1]) + a[|a|-1]))
   
}

function Pos(a : seq<int>): int
{ if a == [] then
    0
   else 
   if ((Sum(a[..|a|-1]) + a[|a|-1]) > Mps(a[..|a|-1])) then DfLength(a) else
     Pos(a[..|a|-1])
   
}

function Sum(a : seq<int>): int
{ if a == [] then  0 else  (Sum(a[..|a|-1]) + a[|a|-1]) 
}

function MpsJoin(leftSum : int, leftMps : int, rightSum : int, rightMps : int): int
{
  DfMax((leftSum + rightMps), leftMps)
}

function PosJoin(leftSum : int, leftPos : int, leftMps : int, rightSum : int, rightPos : int, rightMps : int): int
{
  if ((leftSum - 1) >= (leftMps - rightMps)) then rightPos else leftPos
}

function SumJoin(leftSum : int, rightSum : int): int
{
  (rightSum + leftSum)
}


lemma BaseCaseMps(a : seq<int>)
  ensures Mps(a) == MpsJoin(Sum(a), Mps(a), Sum([]), Mps([]))
  {}

lemma HomMps(a : seq<int>, R_a : seq<int>)
  ensures Mps(a + R_a) == MpsJoin(Sum(a), Mps(a), Sum(R_a), Mps(R_a))
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
    MpsJoin(Sum(a), Mps(a), Sum(R_a), Mps(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCasePos(a : seq<int>)
  ensures Pos(a) == PosJoin(Sum(a), Pos(a), Mps(a), Sum([]), Pos([]), Mps([]))
  {}

lemma HomPos(a : seq<int>, R_a : seq<int>)
  ensures Pos(a + R_a) == PosJoin(Sum(a), Pos(a), Mps(a), Sum(R_a), Pos(R_a), Mps(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCasePos(a);
    
     } else {
    calc{
    Pos(a + R_a);
    =={
      HomSum(a, R_a[..|R_a| - 1]);
      HomMps(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    PosJoin(Sum(a), Pos(a), Mps(a), Sum(R_a), Pos(R_a), Mps(R_a));
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

