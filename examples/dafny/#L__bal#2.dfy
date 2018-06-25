function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMin(x: int, y: int): int { if x > y then y else x}

function Aux_bal4(a : seq<bool>): int
{
  if a == [] then
    0
    else
    DfMin((Cnt(a[..|a|-1]) + (if a[|a|-1] then 1 else (-1))), Aux_bal4(a[..|a|-1]))
}

function Cnt(a : seq<bool>): int
{
  if a == [] then 0 else (Cnt(a[..|a|-1]) + (if a[|a|-1] then 1 else (-1)))
}

function Bal(a : seq<bool>): bool
{
  if a == [] then
    true
    else
    (Bal(a[..|a|-1]) && ((Cnt(a[..|a|-1]) + (if a[|a|-1] then 1 else (-1))) >= 0))
}

function Aux_bal4Join(leftAux_bal4 : int, leftCnt : int, rightAux_bal4 : int, rightCnt : int): int
{
  DfMin((rightAux_bal4 + leftCnt), leftAux_bal4)
}

function CntJoin(leftAux_bal4 : int, leftCnt : int, rightAux_bal4 : int, rightCnt : int): int
{
  ((if false then rightAux_bal4 else rightCnt) + leftCnt)
}

function BalJoin(leftAux_bal4 : int, leftCnt : int, leftBal : bool, rightAux_bal4 : int, rightCnt : int, rightBal : bool): bool
{
  ((((if rightBal then (-2) else (-2)) + (1 + leftCnt)) >= ((-1) - rightAux_bal4)) && leftBal)
}


lemma BaseCaseAux_bal4(a : seq<bool>)
  ensures Aux_bal4(a) == Aux_bal4Join(Aux_bal4(a), Cnt(a), Aux_bal4([]), Cnt([]))
  {}

lemma HomAux_bal4(a : seq<bool>, R_a : seq<bool>)
  ensures Aux_bal4(a + R_a) == Aux_bal4Join(Aux_bal4(a), Cnt(a), Aux_bal4(R_a), Cnt(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_bal4(a);
    
     } else {
    calc{
    Aux_bal4(a + R_a);
    =={
      HomCnt(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Aux_bal4Join(Aux_bal4(a), Cnt(a), Aux_bal4(R_a), Cnt(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseCnt(a : seq<bool>)
  ensures Cnt(a) == CntJoin(Aux_bal4(a), Cnt(a), Aux_bal4([]), Cnt([]))
  {}

lemma HomCnt(a : seq<bool>, R_a : seq<bool>)
  ensures Cnt(a + R_a) == CntJoin(Aux_bal4(a), Cnt(a), Aux_bal4(R_a), Cnt(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseCnt(a);
    
     } else {
    calc{
    Cnt(a + R_a);
    =={
      HomAux_bal4(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    CntJoin(Aux_bal4(a), Cnt(a), Aux_bal4(R_a), Cnt(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseBal(a : seq<bool>)
  ensures Bal(a) == BalJoin(Aux_bal4(a), Cnt(a), Bal(a), Aux_bal4([]), Cnt([]), Bal([]))
  {}

lemma HomBal(a : seq<bool>, R_a : seq<bool>)
  ensures Bal(a + R_a) == BalJoin(Aux_bal4(a), Cnt(a), Bal(a), Aux_bal4(R_a), Cnt(R_a), Bal(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseBal(a);
    
     } else {
    calc{
    Bal(a + R_a);
    =={
      HomAux_bal4(a, R_a[..|R_a| - 1]);
      HomCnt(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    BalJoin(Aux_bal4(a), Cnt(a), Bal(a), Aux_bal4(R_a), Cnt(R_a), Bal(R_a));
    } // End calc.
  } // End else.
} // End lemma.

