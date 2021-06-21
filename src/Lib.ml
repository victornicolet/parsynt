module Log = Utils.Log
module Config = Utils.Config

module Lang = struct
  module AC = Lang.AcTerm
  module A = Lang.Analyze
  module E = Lang.SolutionDescriptors
  module N = Lang.Normalize

  module T = struct
    include Lang.Typ
    include Lang.Term
    module Pp = Lang.TermPp
  end

  module U = Lang.Unfold
  module R = Lang.ResourceModel
end

module Front = struct
  module C = Front.MinicFront
end

module C = Commands
module D = Recursion.Discover
module St = Solve.STerm
module Sf = Solve.SolverForms
module Smt = Solve.SmtLib
module Scripting = Solve.Scripting
module Builders = Recursion.SketchBuilders

(* Modules exposed for testing purposes *)
module Testing_RD = Recursion.RecursionDiscovery
