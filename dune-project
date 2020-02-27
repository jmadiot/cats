(lang dune 2.0)
(authors "Jean-Marie Madiot Simon Castellan")
(using coq 0.1)
(name catincoq)
(generate_opam_files true)
(package
   (name Catincoq)
   (synopsis "A Coq library to reason about Cat models.")
   (description "This library provides  a way to reason in Coq about weak memory models written in Cat."))

(package
   (name Catincoq_Models)
   (synopsis "A collection of axiomatic weak memory models written in Coq.")
   (description "A collection of axiomatic weak memory models written in Coq."))
