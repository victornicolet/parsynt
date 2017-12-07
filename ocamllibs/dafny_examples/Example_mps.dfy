function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMax(x: int, y: int): int { if x > y then x else y}

function Sum(a : seq<int>): int
{
  if dafny_seq_ == [] then
    0
    else
    (Sum(dafny_seq_[..|dafny_seq_|-1]) + dafny_seq_[|dafny_seq_|-1])
}

function Mps(a : seq<int>): int
{
  if dafny_seq_ == [] then
    0
    else
    DfMax((Sum(dafny_seq_[..|dafny_seq_|-1]) + dafny_seq_[|dafny_seq_|-1]), Mps(dafny_seq_[..|dafny_seq_|-1]))
}

function SumJoin(, ): int
{
  (R_x.sum + R_l.sum)
}

function MpsJoin(, ): int
{
  DfMax((R_l.sum + R_x.mps), R_l.mps)
}


lemma BaseCaseSum(a : seq<int>)
  ensures Sum(dafny_seq_) == SumJoin(, )
  {}

lemma HomSum(a : seq<int>, R_a : seq<int>)
  ensures Sum(dafny_seq_ + R_dafny_seq_) == SumJoin(, )
  {
    if R_dafny_seq_ == [] 
    {
    assert(dafny_seq_ + [] == dafny_seq_);
    BaseCaseSum(dafny_seq_);
    
     } else {
    calc{
    Sum(dafny_seq_ + R_dafny_seq_);
    =={
      assert(dafny_seq_ + R_dafny_seq_[..|R_dafny_seq_|-1]) + [R_dafny_seq_[|R_dafny_seq_|-1]] == dafny_seq_ + R_dafny_seq_;
      }
    SumJoin(, );
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseMps(a : seq<int>)
  ensures Mps(dafny_seq_) == MpsJoin(, )
  {}

lemma HomMps(a : seq<int>, R_a : seq<int>)
  ensures Mps(dafny_seq_ + R_dafny_seq_) == MpsJoin(, )
  {
    if R_dafny_seq_ == [] 
    {
    assert(dafny_seq_ + [] == dafny_seq_);
    BaseCaseMps(dafny_seq_);
    
     } else {
    calc{
    Mps(dafny_seq_ + R_dafny_seq_);
    =={
      assert(dafny_seq_ + R_dafny_seq_[..|R_dafny_seq_|-1]) + [R_dafny_seq_[|R_dafny_seq_|-1]] == dafny_seq_ + R_dafny_seq_;
      }
    MpsJoin(, );
    } // End calc.
  } // End else.
} // End lemma.

