function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Aux_mss5(a : seq<int>): int
{
  if a == [] then
    0
    else
    DfMax((a[|a|-1] + Aux_mts0(a[..|a|-1])), Aux_mss5(a[..|a|-1]))
}

function Mss(a : seq<int>): int
{
  if a == [] then 0 else DfMax(Mss(a[..|a|-1]), (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mts0(a : seq<int>): int
{
  if a == [] then 0 else (a[|a|-1] + Aux_mts0(a[..|a|-1]))
}

function Mts(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mss5Join(leftAux_mss5 : int, leftAux_mts0 : int, rightAux_mss5 : int, rightAux_mts0 : int): int
{
  DfMax((rightAux_mss5 + leftAux_mts0), leftAux_mss5)
}

function MssJoin(leftAux_mss5 : int, leftMss : int, leftMts : int, rightAux_mss5 : int, rightMss : int, rightMts : int): int
{
  DfMax(((1 + leftMts) + (1 + rightAux_mss5)), DfMax(rightMss, leftMss))
}

function Aux_mts0Join(leftAux_mts0 : int, rightAux_mts0 : int): int
{
  (rightAux_mts0 + leftAux_mts0)
}

function MtsJoin(leftAux_mts0 : int, leftMts : int, rightAux_mts0 : int, rightMts : int): int
{
  DfMax(((leftMts - rightMts) + (rightAux_mts0 + rightMts)), rightMts)
}


lemma BaseCaseAux_mss5(a : seq<int>)
  ensures Aux_mss5(a) == Aux_mss5Join(Aux_mss5(a), Aux_mts0(a), Aux_mss5([]), Aux_mts0([]))
  {}

lemma HomAux_mss5(a : seq<int>, R_a : seq<int>)
  ensures Aux_mss5(a + R_a) == Aux_mss5Join(Aux_mss5(a), Aux_mts0(a), Aux_mss5(R_a), Aux_mts0(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mss5(a);
    
     } else {
    calc{
    Aux_mss5(a + R_a);
    =={
      HomAux_mts0(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Aux_mss5Join(Aux_mss5(a), Aux_mts0(a), Aux_mss5(R_a), Aux_mts0(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMss(a : seq<int>)
  ensures Mss(a) == MssJoin(Aux_mss5(a), Mss(a), Mts(a), Aux_mss5([]), Mss([]), Mts([]))
  {}

lemma HomMss(a : seq<int>, R_a : seq<int>)
  ensures Mss(a + R_a) == MssJoin(Aux_mss5(a), Mss(a), Mts(a), Aux_mss5(R_a), Mss(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMss(a);
    
     } else {
    calc{
    Mss(a + R_a);
    =={
      HomAux_mss5(a, R_a[..|R_a| - 1]);
      HomMts(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MssJoin(Aux_mss5(a), Mss(a), Mts(a), Aux_mss5(R_a), Mss(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_mts0(a : seq<int>)
  ensures Aux_mts0(a) == Aux_mts0Join(Aux_mts0(a), Aux_mts0([]))
  {}

lemma HomAux_mts0(a : seq<int>, R_a : seq<int>)
  ensures Aux_mts0(a + R_a) == Aux_mts0Join(Aux_mts0(a), Aux_mts0(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mts0(a);
    
     } else {
    calc{
    Aux_mts0(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_mts0Join(Aux_mts0(a), Aux_mts0(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMts(a : seq<int>)
  ensures Mts(a) == MtsJoin(Aux_mts0(a), Mts(a), Aux_mts0([]), Mts([]))
  {}

lemma HomMts(a : seq<int>, R_a : seq<int>)
  ensures Mts(a + R_a) == MtsJoin(Aux_mts0(a), Mts(a), Aux_mts0(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts(a);
    
     } else {
    calc{
    Mts(a + R_a);
    =={
      HomAux_mts0(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MtsJoin(Aux_mts0(a), Mts(a), Aux_mts0(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

