(lang dune 3.5)
(using menhir 2.1)

(name lambda_d)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(documentation https://url/to/documentation)

(package
 (name lambda_d)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune menhir
  (ounit2 :with-test))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
