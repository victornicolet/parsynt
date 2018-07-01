function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Mss(a : seq<int>): int
{
  if a == [] then 0 else DfMax(Mss(a[..|a|-1]), (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mts11(a : seq<int>): int
{
  if a == [] then 0 else (a[|a|-1] + Aux_mts11(a[..|a|-1]))
}

function Aux_mss15(a : seq<int>): int
{
  if a == [] then
    0
    else
    DfMax((a[|a|-1] + Aux_mts11(a[..|a|-1])), Aux_mss15(a[..|a|-1]))
}

function Mts(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mts(a[..|a|-1]) + a[|a|-1]))
}

function MssJoin(leftAux_mss15 : int, leftMss : int, leftMts : int, rightAux_mss15 : int, rightMss : int, rightMts : int): int
{
  DfMax(((1 + leftMts) + (1 + rightAux_mss15)), DfMax(leftMss, rightMss))
}

function Aux_mts11Join(leftAux_mts11 : int, rightAux_mts11 : int): int
{
  (rightAux_mts11 + leftAux_mts11)
}

function Aux_mss15Join(leftAux_mss15 : int, leftAux_mts11 : int, rightAux_mss15 : int, rightAux_mts11 : int): int
{
  DfMax((leftAux_mts11 + rightAux_mss15), leftAux_mss15)
}

function MtsJoin(leftAux_mts11 : int, leftMts : int, rightAux_mts11 : int, rightMts : int): int
{
  DfMax((leftMts + rightAux_mts11), rightMts)
}


lemma BaseCaseMss(a : seq<int>)
  ensures Mss(a) == MssJoin(Aux_mss15(a), Mss(a), Mts(a), Aux_mss15([]), Mss([]), Mts([]))
  {}

lemma HomMss(a : seq<int>, R_a : seq<int>)
  ensures Mss(a + R_a) == MssJoin(Aux_mss15(a), Mss(a), Mts(a), Aux_mss15(R_a), Mss(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMss(a);
    
     } else {
    calc{
    Mss(a + R_a);
    =={
      HomAux_mss15(a, R_a[..|R_a| - 1]);
      HomMts(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MssJoin(Aux_mss15(a), Mss(a), Mts(a), Aux_mss15(R_a), Mss(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_mts11(a : seq<int>)
  ensures Aux_mts11(a) == Aux_mts11Join(Aux_mts11(a), Aux_mts11([]))
  {}

lemma HomAux_mts11(a : seq<int>, R_a : seq<int>)
  ensures Aux_mts11(a + R_a) == Aux_mts11Join(Aux_mts11(a), Aux_mts11(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mts11(a);
    
     } else {
    calc{
    Aux_mts11(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_mts11Join(Aux_mts11(a), Aux_mts11(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_mss15(a : seq<int>)
  ensures Aux_mss15(a) == Aux_mss15Join(Aux_mss15(a), Aux_mts11(a), Aux_mss15([]), Aux_mts11([]))
  {}

lemma HomAux_mss15(a : seq<int>, R_a : seq<int>)
  ensures Aux_mss15(a + R_a) == Aux_mss15Join(Aux_mss15(a), Aux_mts11(a), Aux_mss15(R_a), Aux_mts11(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mss15(a);
    
     } else {
    calc{
    Aux_mss15(a + R_a);
    =={
      HomAux_mts11(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Aux_mss15Join(Aux_mss15(a), Aux_mts11(a), Aux_mss15(R_a), Aux_mts11(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMts(a : seq<int>)
  ensures Mts(a) == MtsJoin(Aux_mts11(a), Mts(a), Aux_mts11([]), Mts([]))
  {}

lemma HomMts(a : seq<int>, R_a : seq<int>)
  ensures Mts(a + R_a) == MtsJoin(Aux_mts11(a), Mts(a), Aux_mts11(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts(a);
    
     } else {
    calc{
    Mts(a + R_a);
    =={
      HomAux_mts11(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MtsJoin(Aux_mts11(a), Mts(a), Aux_mts11(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

