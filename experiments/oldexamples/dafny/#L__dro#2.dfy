function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

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

function First_pos(a : seq<int>): bool
{
  if a == [] then
    true
    else
    (if ((! (a[|a|-1] == 0)) && First_pos(a[..|a|-1])) then false else
      First_pos(a[..|a|-1]))
}

function Pos(a : seq<int>): int
{
  if a == [] then
    0
    else
    (if ((! (a[|a|-1] == 0)) && First_pos(a[..|a|-1])) then DfLength(a) else
      Pos(a[..|a|-1]))
}

function First_posJoin(leftFirst_pos : bool, leftPos : int, rightFirst_pos : bool, rightPos : int): bool
{
  (if (((-8405) >= rightPos) && (! true)) then true else
    (rightFirst_pos && leftFirst_pos))
}

function PosJoin(leftFirst_pos : bool, leftPos : int, leftDfLength : int, rightFirst_pos : bool, rightPos : int, rightDfLength : int): int
{
  (if (leftFirst_pos && (true || true)) then (rightPos + leftDfLength) else
    leftPos)
}


lemma BaseCaseFirst_pos(a : seq<int>)
  ensures First_pos(a) == First_posJoin(First_pos(a), Pos(a), First_pos([]), Pos([]))
  {}

lemma HomFirst_pos(a : seq<int>, R_a : seq<int>)
  ensures First_pos(a + R_a) == First_posJoin(First_pos(a), Pos(a), First_pos(R_a), Pos(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseFirst_pos(a);
    
     } else {
    calc{
    First_pos(a + R_a);
    =={
      HomPos(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    First_posJoin(First_pos(a), Pos(a), First_pos(R_a), Pos(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCasePos(a : seq<int>)
  ensures Pos(a) == PosJoin(First_pos(a), Pos(a), DfLength(a), First_pos([]), Pos([]), DfLength([]))
  {}

lemma HomPos(a : seq<int>, R_a : seq<int>)
  ensures Pos(a + R_a) == PosJoin(First_pos(a), Pos(a), DfLength(a), First_pos(R_a), Pos(R_a), DfLength(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCasePos(a);
    
     } else {
    calc{
    Pos(a + R_a);
    =={
      HomFirst_pos(a, R_a[..|R_a| - 1]);
      HomDfLength(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    PosJoin(First_pos(a), Pos(a), DfLength(a), First_pos(R_a), Pos(R_a), DfLength(R_a));
    } // End calc.
  } // End else.
} // End lemma.

