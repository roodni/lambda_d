ARG PROJ_DIR="/home/opam/lambda"

FROM ocaml/opam:alpine-ocaml-4.14 as build
ARG PROJ_DIR

COPY --chown=opam . ${PROJ_DIR}
WORKDIR ${PROJ_DIR}
RUN opam install --deps-only .
RUN eval $(opam env) && dune build @install



FROM alpine:latest
ARG PROJ_DIR

COPY --from=build ${PROJ_DIR}/_build/default/bin/main.exe /usr/local/bin/lambda_d
WORKDIR /work
ENTRYPOINT [ "/usr/local/bin/lambda_d" ]