function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Aux_mss6(a : seq<int>): int
{
  if a == [] then
    0
    else
    DfMax((a[|a|-1] + Aux_mts2(a[..|a|-1])), Aux_mss6(a[..|a|-1]))
}

function Mss(a : seq<int>): int
{
  if a == [] then 0 else DfMax(Mss(a[..|a|-1]), (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mts2(a : seq<int>): int
{
  if a == [] then 0 else (a[|a|-1] + Aux_mts2(a[..|a|-1]))
}

function Mts(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mss6Join(leftAux_mss6 : int, leftAux_mts2 : int, rightAux_mss6 : int, rightAux_mts2 : int): int
{
  DfMax((leftAux_mts2 + rightAux_mss6), leftAux_mss6)
}

function MssJoin(leftAux_mss6 : int, leftMss : int, leftMts : int, rightAux_mss6 : int, rightMss : int, rightMts : int): int
{
  DfMax(((1 + leftMts) + (1 + rightAux_mss6)), DfMax(leftMss, rightMss))
}

function Aux_mts2Join(leftAux_mts2 : int, rightAux_mts2 : int): int
{
  (rightAux_mts2 + leftAux_mts2)
}

function MtsJoin(leftAux_mts2 : int, leftMts : int, rightAux_mts2 : int, rightMts : int): int
{
  DfMax((leftMts + rightAux_mts2), rightMts)
}


lemma BaseCaseAux_mss6(a : seq<int>)
  ensures Aux_mss6(a) == Aux_mss6Join(Aux_mss6(a), Aux_mts2(a), Aux_mss6([]), Aux_mts2([]))
  {}

lemma HomAux_mss6(a : seq<int>, R_a : seq<int>)
  ensures Aux_mss6(a + R_a) == Aux_mss6Join(Aux_mss6(a), Aux_mts2(a), Aux_mss6(R_a), Aux_mts2(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mss6(a);
    
     } else {
    calc{
    Aux_mss6(a + R_a);
    =={
      HomAux_mts2(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Aux_mss6Join(Aux_mss6(a), Aux_mts2(a), Aux_mss6(R_a), Aux_mts2(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMss(a : seq<int>)
  ensures Mss(a) == MssJoin(Aux_mss6(a), Mss(a), Mts(a), Aux_mss6([]), Mss([]), Mts([]))
  {}

lemma HomMss(a : seq<int>, R_a : seq<int>)
  ensures Mss(a + R_a) == MssJoin(Aux_mss6(a), Mss(a), Mts(a), Aux_mss6(R_a), Mss(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMss(a);
    
     } else {
    calc{
    Mss(a + R_a);
    =={
      HomAux_mss6(a, R_a[..|R_a| - 1]);
      HomMts(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MssJoin(Aux_mss6(a), Mss(a), Mts(a), Aux_mss6(R_a), Mss(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_mts2(a : seq<int>)
  ensures Aux_mts2(a) == Aux_mts2Join(Aux_mts2(a), Aux_mts2([]))
  {}

lemma HomAux_mts2(a : seq<int>, R_a : seq<int>)
  ensures Aux_mts2(a + R_a) == Aux_mts2Join(Aux_mts2(a), Aux_mts2(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mts2(a);
    
     } else {
    calc{
    Aux_mts2(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_mts2Join(Aux_mts2(a), Aux_mts2(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMts(a : seq<int>)
  ensures Mts(a) == MtsJoin(Aux_mts2(a), Mts(a), Aux_mts2([]), Mts([]))
  {}

lemma HomMts(a : seq<int>, R_a : seq<int>)
  ensures Mts(a + R_a) == MtsJoin(Aux_mts2(a), Mts(a), Aux_mts2(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts(a);
    
     } else {
    calc{
    Mts(a + R_a);
    =={
      HomAux_mts2(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MtsJoin(Aux_mts2(a), Mts(a), Aux_mts2(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

