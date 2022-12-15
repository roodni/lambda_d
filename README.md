# 代数学特論


## 実行方法1 (とにかく実行したい)
必要なソフトウェア: docker

ビルド
```
docker compose build
```

実行
```
docker compose run --rm lambda inputs/...
```

`inputs/`以下のファイルにはコンテナからアクセス可能です


## 実行方法2 (dockerを使いたくない)
必要なソフトウェア: opam (2.x), ocaml (4.14)

ビルド
```sh
opam install --deps-only .
dune build @install
```

実行
```sh
_build/default/bin/main.exe inputs/...
```