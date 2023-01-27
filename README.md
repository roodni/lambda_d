# MCS.T417

## どうなったか

- 11章 (inputs/exdef.txt): 通ります
- 12章 (inputs/def8m.txt): 2秒、メモリ500MB程度で通ります
- 13章: 通りません

## 実行方法1 (とにかく実行したい)
必要なソフトウェア: docker

ビルド
```
docker compose build
```

実行
```
docker compose run --rm lambda
```
コンテナ内で
- `book` `automake` `defconv` コマンドを使えます
- `inputs/`以下のファイルにアクセス可能です


## 実行方法2 (dockerを使いたくない)
必要なソフトウェア: opam (2.x), ocaml (4.14)

ビルド
```sh
opam install --deps-only .
dune build @install
```

実行
- `_build/default/bin/book.exe`
  + 授業配付のtest_book3と引数に互換性があります
- `_build/default/bin/automake.exe`
  + 授業配付のtest_automake3と引数に互換性があります
- `_build/default/bin/defconv.exe <exdef>`
  + Definition記述言語(例: inputs/exdef.txt) を読み込んで授業文法に変換します