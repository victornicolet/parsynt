(lang dune 2.6)

(name Parsynt)

(version 0.3)

(license GNU-GPL)

(authors "Victor Nicolet")

(maintainers "victorn@cs.toronto.edu")

(homepage "https://github.com/victornicolet/parsynt")

(bug_reports "https://github.com/victornicolet/parsynt/issues")

(generate_opam_files true)

(using menhir 2.0)

(package
 (name Parsynt)
 (synopsis "Automatic Parallelization Tool")
 (description
  "Executable and libraries for automatically parallelizing various algorithms with loops.")
 (depends
  (base
   (>= v0.14.0))
  (fmt
   (>= 0.8.8))
  (getopt
   (>= 20120615))
  (menhir
   (>= 20200624))
  (parsexp
   (>= v0.14.0))
  (ppx_let
   (>= v0.14.0))
  (stdio
   (>= v0.14.0))
  (ppx_sexp_conv
   (>= v0.14.0))
  (fileutils
   (>= 0.6.3))
  (extlib
   (>= 1.7.7))
  (lwt
   (>= 5.4.0))
  (sexplib
   (>= v0.14.0))))
