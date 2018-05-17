function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Mss(a : seq<int>): int
{
  if a == [] then 0 else DfMax(Mss(a[..|a|-1]), (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_1(a : seq<int>): int
{
  if a == [] then 0 else (a[|a|-1] + Aux_1(a[..|a|-1]))
}

function Aux_3(a : seq<int>): int
{
  if a == [] then
    0
    else
    DfMax((a[|a|-1] + Aux_1(a[..|a|-1])), Aux_3(a[..|a|-1]))
}

function Mts(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mts(a[..|a|-1]) + a[|a|-1]))
}

function MssJoin(leftAux_3 : int, leftMss : int, leftMts : int, rightAux_3 : int, rightMss : int, rightMts : int): int
{
  DfMax(((leftMts + 1) + (rightAux_3 - 1)), DfMax(rightMss, leftMss))
}

function Aux_1Join(leftAux_1 : int, rightAux_1 : int): int
{
  ((leftAux_1 - (-30)) + (rightAux_1 + (-30)))
}

function Aux_3Join(leftAux_3 : int, leftAux_1 : int, rightAux_3 : int, rightAux_1 : int): int
{
  DfMax((rightAux_3 + leftAux_1), leftAux_3)
}

function MtsJoin(leftAux_1 : int, leftMts : int, rightAux_1 : int, rightMts : int): int
{
  DfMax(((rightAux_1 - 17134) + (leftMts + 17134)), rightMts)
}


lemma BaseCaseMss(a : seq<int>)
  ensures Mss(a) == MssJoin(Aux_3(a), Mss(a), Mts(a), Aux_3([]), Mss([]), Mts([]))
  {}

lemma HomMss(a : seq<int>, R_a : seq<int>)
  ensures Mss(a + R_a) == MssJoin(Aux_3(a), Mss(a), Mts(a), Aux_3(R_a), Mss(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMss(a);
    
     } else {
    calc{
    Mss(a + R_a);
    =={
      HomAux_3(a, R_a[..|R_a| - 1]);
      HomMts(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MssJoin(Aux_3(a), Mss(a), Mts(a), Aux_3(R_a), Mss(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_1(a : seq<int>)
  ensures Aux_1(a) == Aux_1Join(Aux_1(a), Aux_1([]))
  {}

lemma HomAux_1(a : seq<int>, R_a : seq<int>)
  ensures Aux_1(a + R_a) == Aux_1Join(Aux_1(a), Aux_1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_1(a);
    
     } else {
    calc{
    Aux_1(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_1Join(Aux_1(a), Aux_1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAux_3(a : seq<int>)
  ensures Aux_3(a) == Aux_3Join(Aux_3(a), Aux_1(a), Aux_3([]), Aux_1([]))
  {}

lemma HomAux_3(a : seq<int>, R_a : seq<int>)
  ensures Aux_3(a + R_a) == Aux_3Join(Aux_3(a), Aux_1(a), Aux_3(R_a), Aux_1(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_3(a);
    
     } else {
    calc{
    Aux_3(a + R_a);
    =={
      HomAux_1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    Aux_3Join(Aux_3(a), Aux_1(a), Aux_3(R_a), Aux_1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMts(a : seq<int>)
  ensures Mts(a) == MtsJoin(Aux_1(a), Mts(a), Aux_1([]), Mts([]))
  {}

lemma HomMts(a : seq<int>, R_a : seq<int>)
  ensures Mts(a + R_a) == MtsJoin(Aux_1(a), Mts(a), Aux_1(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts(a);
    
     } else {
    calc{
    Mts(a + R_a);
    =={
      HomAux_1(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MtsJoin(Aux_1(a), Mts(a), Aux_1(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

