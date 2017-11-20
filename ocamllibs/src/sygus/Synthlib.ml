open Format
open Synthlib2ast
open Sylexer

let parseinputs s = Syparser.file Sylexer.token (Lexing.from_string s)
let parsechan ch = Syparser.file Sylexer.token (Lexing.from_channel ch)

let printsy = sypp_sygus std_formatter
