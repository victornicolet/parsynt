function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMin(x: int, y: int): int { if x > y then y else x}

function DfMinSeq(s : seq<int>) : int 
  requires |s| >= 1
{
  if |s| == 1 then s[0]
  else
  DfMin(DfMinSeq(s[..|s|-1]), s[|s|-1])
}
function Aux_0(a : seq<int>): int
requires |a| >= 1
{
  if |a| == 1 then a[0] else a[0]
}

function Iss(a : seq<int>): bool
requires |a| >= 1
{
  if |a| == 1 then
    true
    else
    (Iss(a[..|a|-1]) && (Prev(a[..|a|-1]) < a[|a|-1]))
}

function Prev(a : seq<int>): int
requires |a| >= 1
{
  if |a| == 1 then a[0] else a[|a|-1]
}

function Aux_0Join(leftAux_0 : int, rightAux_0 : int): int
{
  leftAux_0
}

function IssJoin(leftAux_0 : int, leftPrev : int, leftIss : bool, rightAux_0 : int, rightPrev : int, rightIss : bool): bool
{
  (((rightAux_0 - leftPrev) >= 1) && (leftIss && rightIss))
}

function PrevJoin(leftPrev : int, rightPrev : int): int
{
  rightPrev
}


lemma BaseCaseAux_0(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Aux_0(a + [R_a[0]]) == Aux_0Join(Aux_0(a), Aux_0([R_a[0]]))
  {}

lemma HomAux_0(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Aux_0(a + R_a) == Aux_0Join(Aux_0(a), Aux_0(R_a))
  {
    if |R_a| == 1 
    {
    assert(a + R_a == a + [R_a[0]]);
    BaseCaseAux_0(a, R_a);
    
     } else {
    calc{
    Aux_0(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_0Join(Aux_0(a), Aux_0(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseIss(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Iss(a + [R_a[0]]) == IssJoin(Aux_0(a), Prev(a), Iss(a), Aux_0([R_a[0]]), Prev([R_a[0]]), Iss([R_a[0]]))
  {}

lemma HomIss(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Iss(a + R_a) == IssJoin(Aux_0(a), Prev(a), Iss(a), Aux_0(R_a), Prev(R_a), Iss(R_a))
  {
    if |R_a| == 1 
    {
    assert(a + R_a == a + [R_a[0]]);
    BaseCaseIss(a, R_a);
    
     } else {
    calc{
    Iss(a + R_a);
    =={
      HomAux_0(a, R_a[..|R_a| - 1]);
      HomPrev(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    IssJoin(Aux_0(a), Prev(a), Iss(a), Aux_0(R_a), Prev(R_a), Iss(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCasePrev(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Prev(a + [R_a[0]]) == PrevJoin(Prev(a), Prev([R_a[0]]))
  {}

lemma HomPrev(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Prev(a + R_a) == PrevJoin(Prev(a), Prev(R_a))
  {
    if |R_a| == 1 
    {
    assert(a + R_a == a + [R_a[0]]);
    BaseCasePrev(a, R_a);
    
     } else {
    calc{
    Prev(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    PrevJoin(Prev(a), Prev(R_a));
    } // End calc.
  } // End else.
} // End lemma.

