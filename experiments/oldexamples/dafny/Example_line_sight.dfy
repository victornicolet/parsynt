function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Aux_1(a : seq<int>): int
requires |a| >= 1
{
  if |a| == 1 then a[0] else a[|a|-1]
}

function Amax(a : seq<int>): int
{
  if a == [] then 0 else DfMax(Amax(a[..|a|-1]), a[|a|-1])
}

function Visible(a : seq<int>): bool
{
  if a == [] then true else (Amax(a[..|a|-1]) <= a[|a|-1])
}

function Aux_1Join(leftAux_1 : int, rightAux_1 : int): int
{
  rightAux_1
}

function AmaxJoin(leftAmax : int, rightAmax : int): int
{
  DfMax(rightAmax, leftAmax)
}

function VisibleJoin(leftAux_1 : int, leftAmax : int, rightAux_1 : int, rightAmax : int): bool
{
  (DfMax(rightAmax, leftAmax) == (rightAux_1 - 0))
}


lemma BaseCaseAux_1(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Aux_1(a + [R_a[0]]) == Aux_1Join(Aux_1(a), Aux_1([R_a[0]]))
  {}

lemma HomAux_1(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Aux_1(a + R_a) == Aux_1Join(Aux_1(a), Aux_1(R_a))
  {
    if |R_a| == 1 
    {
    assert(a + R_a == a + [R_a[0]]);
    BaseCaseAux_1(a, R_a);
    
     } else {
    calc{
    Aux_1(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    Aux_1Join(Aux_1(a), Aux_1(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseAmax(a : seq<int>)
  ensures Amax(a) == AmaxJoin(Amax(a), Amax([]))
  {}

lemma HomAmax(a : seq<int>, R_a : seq<int>)
  ensures Amax(a + R_a) == AmaxJoin(Amax(a), Amax(R_a))
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseAmax(a);
    
     } else {
    calc{
    Amax(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    AmaxJoin(Amax(a), Amax(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseVisible(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Visible(a + [R_a[0]]) == VisibleJoin(Aux_1(a), Amax(a), Aux_1([R_a[0]]), Amax([R_a[0]]))
  {}

lemma HomVisible(a : seq<int>, R_a : seq<int>)
  requires |a| >= 1 && |R_a| >= 1
  ensures Visible(a + R_a) == VisibleJoin(Aux_1(a), Amax(a), Aux_1(R_a), Amax(R_a))
  {
    if |R_a| == 1 
    {
    assert(a + R_a == a + [R_a[0]]);
    BaseCaseVisible(a, R_a);
    
     } else {
    calc{
    Visible(a + R_a);
    =={
      HomAux_1(a, R_a[..|R_a| - 1]);
      HomAmax(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a;
      }
    VisibleJoin(Aux_1(a), Amax(a), Aux_1(R_a), Amax(R_a));
    } // End calc.
  } // End else.
} // End lemma.

