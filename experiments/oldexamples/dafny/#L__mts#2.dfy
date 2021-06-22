function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Aux_mts7(a : seq<int>): int
{
  if a == [] then 0 else (a[|a|-1] + Aux_mts7(a[..|a|-1]))
}

function Mts(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mts7Join(leftAux_mts7 : int, rightAux_mts7 : int): int
{
  (rightAux_mts7 + leftAux_mts7)
}

function MtsJoin(leftAux_mts7 : int, leftMts : int, rightAux_mts7 : int, rightMts : int): int
{
  DfMax((leftMts + rightAux_mts7), rightMts)
}


lemma BaseCaseAux_mts7(a : seq<int>)
  ensures Aux_mts7(a) == Aux_mts7Join(Aux_mts7(a), Aux_mts7([]))
  {}

lemma HomAux_mts7(a : seq<int>, R_a : seq<int>)
  ensures Aux_mts7(a + R_a) == Aux_mts7Join(Aux_mts7(a), Aux_mts7(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mts7(a);
    
     } else {
    calc{
    Aux_mts7(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_mts7Join(Aux_mts7(a), Aux_mts7(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMts(a : seq<int>)
  ensures Mts(a) == MtsJoin(Aux_mts7(a), Mts(a), Aux_mts7([]), Mts([]))
  {}

lemma HomMts(a : seq<int>, R_a : seq<int>)
  ensures Mts(a + R_a) == MtsJoin(Aux_mts7(a), Mts(a), Aux_mts7(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts(a);
    
     } else {
    calc{
    Mts(a + R_a);
    =={
      HomAux_mts7(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MtsJoin(Aux_mts7(a), Mts(a), Aux_mts7(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

