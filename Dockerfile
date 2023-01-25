ARG PROJ_DIR="/home/opam/lambda"

FROM ocaml/opam:alpine-ocaml-4.14 as build
ARG PROJ_DIR

WORKDIR ${PROJ_DIR}
COPY --chown=opam ./lambda_d.opam ${PROJ_DIR}
RUN opam install --deps-only .
COPY --chown=opam . ${PROJ_DIR}
RUN eval $(opam env) && dune build @install



FROM alpine:latest
ARG PROJ_DIR

COPY --from=build ${PROJ_DIR}/_build/default/bin/book.exe /usr/local/bin/book
COPY --from=build ${PROJ_DIR}/_build/default/bin/automake.exe /usr/local/bin/automake
COPY --from=build ${PROJ_DIR}/_build/default/bin/defconv.exe /usr/local/bin/defconv
WORKDIR /work