function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Aux_mts8(a : seq<int>): int
{
  if a == [] then 0 else (a[|a|-1] + Aux_mts8(a[..|a|-1]))
}

function Mts(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mts(a[..|a|-1]) + a[|a|-1]))
}

function Aux_mts8Join(leftAux_mts8 : int, rightAux_mts8 : int): int
{
  (rightAux_mts8 + leftAux_mts8)
}

function MtsJoin(leftAux_mts8 : int, leftMts : int, rightAux_mts8 : int, rightMts : int): int
{
  DfMax((leftMts + rightAux_mts8), rightMts)
}


lemma BaseCaseAux_mts8(a : seq<int>)
  ensures Aux_mts8(a) == Aux_mts8Join(Aux_mts8(a), Aux_mts8([]))
  {}

lemma HomAux_mts8(a : seq<int>, R_a : seq<int>)
  ensures Aux_mts8(a + R_a) == Aux_mts8Join(Aux_mts8(a), Aux_mts8(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAux_mts8(a);
    
     } else {
    calc{
    Aux_mts8(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_mts8Join(Aux_mts8(a), Aux_mts8(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMts(a : seq<int>)
  ensures Mts(a) == MtsJoin(Aux_mts8(a), Mts(a), Aux_mts8([]), Mts([]))
  {}

lemma HomMts(a : seq<int>, R_a : seq<int>)
  ensures Mts(a + R_a) == MtsJoin(Aux_mts8(a), Mts(a), Aux_mts8(R_a), Mts(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMts(a);
    
     } else {
    calc{
    Mts(a + R_a);
    =={
      HomAux_mts8(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    MtsJoin(Aux_mts8(a), Mts(a), Aux_mts8(R_a), Mts(R_a));
    } // End calc.
  } // End else.
} // End lemma.

