function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Aux_0(a : seq<bool>): bool
requires |a| >= 1
{
  if |a| == 1 then a[0] else a[0]
}

function F(a : seq<bool>): bool
{
  if a == [] then false else a[|a|-1]
}

function Cnt(a : seq<bool>): int
{
  if a == [] then
    0
    else
    (Cnt(a[..|a|-1]) + (if (a[|a|-1] && (! F(a[..|a|-1]))) then 1 else 0))
}

function Aux_0Join(leftAux_0 : bool, rightAux_0 : bool): bool
{
  leftAux_0
}

function FJoin(leftF : bool, rightF : bool): bool
{
  rightF
}

function CntJoin(leftAux_0 : bool, leftCnt : int, leftF : bool, rightAux_0 : bool, rightCnt : int, rightF : bool): int
{
  (if (rightAux_0 && (leftF && true)) then ((rightCnt - 1) + leftCnt) else
    (rightCnt + leftCnt))
}


lemma BaseCaseAux_0(a : seq<bool>, R_a : seq<bool>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Aux_0(a + [R_a[0]]) == Aux_0Join(Aux_0(a), Aux_0([R_a[0]]))
  {}

lemma HomAux_0(a : seq<bool>, R_a : seq<bool>)
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

lemma HomF(a : seq<bool>, R_a : seq<bool>)
  ensures F(a + R_a) == FJoin(F(a), F(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    
     } else {
    calc{
    F(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    FJoin(F(a), F(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseCnt(a : seq<bool>, R_a : seq<bool>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Cnt(a + [R_a[0]]) == CntJoin(Aux_0(a), Cnt(a), F(a), Aux_0([R_a[0]]), Cnt([R_a[0]]), F([R_a[0]]))
  {}

lemma HomCnt(a : seq<bool>, R_a : seq<bool>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Cnt(a + R_a) == CntJoin(Aux_0(a), Cnt(a), F(a), Aux_0(R_a), Cnt(R_a), F(R_a))
  {
    if |R_a| == 1 
    {
    assert(a + R_a == a + [R_a[0]]);
    BaseCaseCnt(a, R_a);
    
     } else {
    calc{
    Cnt(a + R_a);
    =={
      HomAux_0(a, R_a[..|R_a| - 1]);
      HomF(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    CntJoin(Aux_0(a), Cnt(a), F(a), Aux_0(R_a), Cnt(R_a), F(R_a));
    } // End calc.
  } // End else.
} // End lemma.

