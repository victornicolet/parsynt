function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Mtp(a : seq<int>): int
{
  if a == [] then 0 else DfMax(0, (Mtp(a[..|a|-1]) * a[|a|-1]))
}

function MtpJoin(, ): int
{
  DfMax(((-1) - 1), ((1 - 1) * (1 - 1)))
}


lemma BaseCaseMtp(a : seq<int>)
  ensures Mtp(a) == MtpJoin(, )
  {}

lemma HomMtp(a : seq<int>, R_a : seq<int>)
  ensures Mtp(a + R_a) == MtpJoin(, )
  {
    if R_a == [] 
    {
    assert(a + [] == a);
    BaseCaseMtp(a);
    
     } else {
    calc{
    Mtp(a + R_a);
    =={ assert(a + R_a[..|R_a|-1]) + [R_a[|R_a|-1]] == a + R_a; }
    MtpJoin(, );
    } // End calc.
  } // End else.
} // End lemma.

