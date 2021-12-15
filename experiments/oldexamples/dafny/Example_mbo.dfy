function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x >= y then x else y}

function Cl(a : seq<bool>): int
{
  if a == [] then
    0
    else
    (if a[|a|-1] then (Cl(a[..|a|-1]) + 1) else 0)
}

function Ml(a : seq<bool>): int
{
  if a == [] then
    0
    else
    DfMax(Ml(a[..|a|-1]), Cl(a))
}

function Conj(a : seq<bool>): bool
{
  if a == [] then
    true
    else
    (a[|a|-1] && Conj(a[..|a|-1]))
}

function C(a : seq<bool>): int
{
    if a == [] then
    0
    else
    (C(a[..|a|-1]) + (if (a[|a|-1] && Conj(a[..|a|-1])) then 1 else 0))
}

function ClJoin(leftCl : int, rightCl : int, rightConj : bool) : int
{
  rightCl + if !rightConj then 0 else leftCl
}

function ConjJoin(leftConj : bool, rightConj : bool) : bool
{
    leftConj && rightConj
}

function CJoin(leftC : int, leftConj : bool, rightC : int) : int {
   leftC + if !leftConj then 0 else rightC
}

function MlJoin(leftMl : int, leftCl : int, rightMl : int, rightC : int) : int {
    DfMax(leftCl + rightC, DfMax(leftMl, rightMl))
}

lemma BaseCaseConj(a : seq<bool>)
  ensures Conj(a) == ConjJoin(Conj(a), Conj([]))
  {}

lemma HomConj(a : seq<bool>, R_a : seq<bool>)
ensures Conj(a + R_a) == ConjJoin(Conj(a), Conj(R_a))
  {
    if R_a == []
    {
    assert(a + [] == a);
    BaseCaseConj(a);

     } else {
    calc{
    Conj(a + R_a);
    =={
      assert(a + R_a[..|R_a|-1] + [R_a[|R_a|-1]] == a + R_a);
      }
      ConjJoin(Conj(a), Conj(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseC(a : seq<bool>)
  ensures C(a) == CJoin(C(a), Conj(a), C([]))
  {}

lemma HomC(a : seq<bool>, R_a : seq<bool>)
ensures C(a + R_a) == CJoin(C(a), Conj(a), C(R_a))
  {
    if R_a == []
    {
    assert(a + [] == a);
    BaseCaseC(a);

     } else {
    calc{
    C(a + R_a);
    =={
      HomConj(a, R_a[..|R_a| - 1]);
      assert(a + R_a[..|R_a|-1] + [R_a[|R_a|-1]] == a + R_a);
      }
      CJoin(C(a), Conj(a), C(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseCl(a : seq<bool>)
  ensures Cl(a) == ClJoin(Cl(a), Cl([]), Conj([]))
  {}

lemma HomCl(a : seq<bool>, R_a : seq<bool>)
  ensures Cl(a + R_a) == ClJoin(Cl(a), Cl(R_a), Conj(R_a))
  {
    if R_a == []
    {
    assert(a + [] == a);
    BaseCaseCl(a);

     } else {
        calc{
        Cl(a + R_a);
        =={
        HomConj(a, R_a[..|R_a| - 1]);
        assert(a + R_a[..|R_a|-1] + [R_a[|R_a|-1]] == a + R_a);
        }
        ClJoin(Cl(a), Cl(R_a), Conj(R_a));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMl(a : seq<bool>)
  ensures Ml(a) == MlJoin(Ml(a), Cl(a), Ml([]), C([]))
  {}

// External required hints
// Split case on Conj

// lemma ExtMlProp(a : seq<bool>, R_a : seq<bool>)
//   ensures !Conj(R_a) || Cl(a + R_a) == Cl(a) + C(R_a)

// lemma ExtMlProp2(a : seq<bool>, R_a : seq<bool>)
//   ensures Ml(a + R_a) >= Ml(R_a)
// End external hints

lemma HomMl(a : seq<bool>, R_a : seq<bool>)
  ensures Ml(a + R_a) == MlJoin(Ml(a), Cl(a),Ml(R_a),C(R_a))
  {
    if R_a == []
    {
    assert(a + [] == a);
    BaseCaseMl(a);

     } else {
      calc{
        Ml(a + R_a);
        == {
        HomC(a, R_a[..|R_a| - 1]);
        HomCl(a, R_a[..|R_a| - 1]);
        assert(a + R_a[..|R_a| - 1] + [R_a[|R_a|-1]] == a + R_a);
        ExtMlProp(a, R_a);
        ExtMlProp2(a, R_a);
        }
        MlJoin(Ml(a), Cl(a), Ml(R_a), C(R_a));
    } // End calc
  } // End else.
} // End lemma.


// Extras: manual proofs for external hints

lemma ExtMlProp(a : seq<bool>, R_a : seq<bool>)
  ensures !Conj(R_a) || Cl(a + R_a) == Cl(a) + C(R_a)
{
  if R_a == [] {
    assert(a + [] == a);
  } else
  {
    if(Conj(R_a)) {
      calc {
        Cl(a + R_a);
        == { assert(a + R_a[..|R_a| - 1] + [R_a[|R_a|-1]] == a + R_a);}
        Cl(a) + C(R_a);
      }
    } else {
      //
    }
  }
}

lemma ExtMlProp2ProvedAux(a : seq<bool>)
  ensures Ml(a) >= 0
{}

lemma ExtMlProp2ProvedAux2(a : seq<bool>)
  ensures Cl(a) >= 0
{}


lemma ExtMlProp2(a : seq<bool>, R_a : seq<bool>)
  ensures Ml(a + R_a) >= Ml(R_a)
{
  if R_a == [] {
    calc {
      Ml(a + []);
      == {assert(a + [] == a);}
      Ml(a);
      >={ ExtMlProp2ProvedAux(a); assert(Ml([]) == 0);}
      Ml([]);
    }
  } else {
      calc {
        Ml(a + R_a);
        == { assert(a + R_a[..|R_a| - 1] + [R_a[|R_a|-1]] == a + R_a);}
        DfMax(Ml(a + R_a[..|R_a|-1]), Cl(a+R_a));
        >= { assert(a + R_a[..|R_a| - 1] + [R_a[|R_a|-1]] == a + R_a);}
        DfMax(Ml(R_a[..|R_a|-1]), Cl(a + R_a));
        >= { HomCl(a, R_a); ExtMlProp2ProvedAux2(a); assert(Cl(a + R_a) >= Cl(R_a)); }
        DfMax(Ml(R_a[..|R_a|-1]), Cl(R_a));
      }
  }
}
