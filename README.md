# goovm

LLVM のコンパイル速度を、新しい言語 [Goose](https://github.com/aardappel/goose) で書き直すことで改善できるかを検証した研究リポジトリです。

## 結論の要約

- **LLVM を Goose で全面的に書き直すのは成り立たない。** 規模、Goose コンパイラ自体の伸び方、C++ との連携の制約が理由です。
- **C++ から Goose で書いた部品を呼ぶ局所的な置き換えは動いた。** C++ と同じ設計の Goose 版バックエンドは、C++ 版とバイト単位で同一の出力を出し、2.1〜2.4倍速く動きました。
  - 速さの原因は言語ではなく、メモリモデルです。C++ で同じ仕組みを手作りすると、差は約1.2倍まで縮みます。
- **ただし、ビルド全体への効果は小さい。** CTMark の `-O0` で、バックエンドを LLVM の14.6倍速くしても、全体では約1.09倍です。時間の大半は C/C++ のフロントエンドとプロセスの起動が占めます。
- **場面ごとに、より効く既存の手段がある。**
  - デバッグビルド：TPDE
  - LLVM 自身のビルド：PCH（1.96倍。main ではすでに既定）

## 報告書

- [初期調査（2026-11-05）](docs/research/2026-11-05-goose-llvm-investigation.md)
- [検証結果：フェーズ0〜2（2026-11-06）](docs/research/2026-11-06-results.md)
- [Goose で作ったコンパイラの実装結果（2026-11-07）](docs/research/2026-11-07-goose-compilers.md)

## マイルストーン B5：goosecc のデバッグ情報

`goosecc -g` が、clang-20 `-O0 -g` と同じ DWARF 5 を出すようになりました。行テーブルに加えて、変数、引数、型、スコープ、ラベル、大域変数（関数内の static 変数を含む）、文字列リテラルです。型はビットフィールド、VLA、列挙型、関数ポインタ、ベクトル、複素数、`_Atomic`、typedef（書かれたとおりの名前）を含めてすべて出します。DIE は goosecc 自身の AST と型から作り、GIR の `dies`/`dattrs` 表でバックエンドに渡します。バックエンド、GIR、`tools/` は変えていません。設計は [`frontend-goose/DESIGN.md`](frontend-goose/DESIGN.md) の §11、記録は [`frontend-goose/NOTES.md`](frontend-goose/NOTES.md) の12節です。

- **clang との突き合わせ**（`tests/dwarf_diff.py`）：コーパスの C ファイル2,357本のうち、両方がコンパイルできる2,288本で、正規化した `llvm-dwarfdump --debug-info` が2,231本（97.5%）で clang と同一でした。さらに13本は、フレーム上の位置の書き方だけが違います。残る44本の差は、すべて生成コードの違いから来ます（clang が const 変数の読み出しを畳み込む、`always_inline` を `-O0` でもインライン展開する、など）。CTMark の C ファイルでは、両方がコンパイルできる324本のうち316本が同一です。goosecc の `-g` オブジェクト2,288個は、すべて `llvm-dwarfdump --verify` を通ります。
- **gdb での比較**（`tests/gdb_oracle.py --goosecc`）：GDB_SUMMARY_JA
- **速さ**：BENCH_SUMMARY_JA
- **回帰なし**：REGRESSION_SUMMARY_JA

## 現在の状態（マイルストーン A3）

A3 で、Goose 版バックエンドの出力がデバッガと例外処理で使えるようになり、C++ もコンパイルできるようになりました。設計は [`backend-goose/DESIGN.md`](backend-goose/DESIGN.md) の §9〜§12、記録は [`backend-goose/NOTES.md`](backend-goose/NOTES.md) の10節です。

- **巻き戻し情報**：すべての関数に `.eh_frame` の FDE を出します。CFI は命令境界ごとに正確です（プロローグの push、エピローグの pop、可変長 alloca、レッドゾーン、スタック渡しの引数を持つ invoke の `DW_CFA_GNU_args_size`）。`tests/gdb_oracle.py --unwind` で、全関数を1命令ずつ実行してバックトレースを確かめます。
- **C++**：invoke / landingpad / resume、パーソナリティ、`.gcc_except_table` の LSDA、comdat（ELF のセクショングループ）、初期化の優先順位、`thread_local` の動的初期化、モジュールレベルのアセンブリ。SingleSource の C++ コーパス（107本）と CTMark の C++ 4本（7zip、Bullet、kimwitu++、tramp3d-v4）が、LLVM へのフォールバックなしに参照出力と一致します。goovm-llc と goovm-cc の両方で確かめています。
- **DWARF 5**：clang-20 `-g` と同じものを出します。行テーブル（is_stmt、prologue_end、epilogue_begin）、コンパイル単位、サブプログラム、引数と局所変数の位置、レキシカルブロック、インライン展開された関数、すべての型です。エクスポータが LLVM 20 の DwarfDebug を移植して DIE の木を作り、バックエンドはコードのアドレス、フレーム上の位置、範囲を埋めます。
- 正しさ：全コーパス（C と C++ の1,921本、clang で通る1,915本）の全変種（O0、g、mem2reg、goovm-cc の cc と cc-g）で失敗0、フォールバック0です。`-g` の全オブジェクト（5,266個）が `llvm-dwarfdump --verify` を通ります。clang `-O0 -g` との gdb のやりとりの比較（`tests/gdb_oracle.py`、93本、1,389回の停止）は87本で一致します。残りの差は既知の LLVM との違いです（NOTES.md の10節）。全関数を1命令ずつ実行する巻き戻し検査は91本で不一致0です（2本は再帰が深く時間切れ）。
- goosecc は `frontend-goose/` を変えずに、`-g` で行テーブルを出すようになりました（GIR の追加は後方互換です）。`tests/run.py --goosecc` は98/98です。
- 速さ：`-g` なしのバックエンドの時間は A2 の1.04〜1.10倍です（goovm-llc 全体では1.02〜1.07倍、うち `.eh_frame` が2〜4%）。`-g` ではバックエンドが2〜4倍、エクスポータが4〜6倍になりますが、LLVM の `-O0 -g` のコード生成より、sqlite3 と tramp3d-v4 で8.5倍速いままです。

## マイルストーン A2：レジスタ割り付け

バックエンドは Goose 版だけを育てます。A1 で、clang-20 が `-O0`（`-g` 付き、`mem2reg` 後を含む）で出す C の LLVM IR をすべて扱う `-O0` バックエンドになりました。A2 で、出力コードの質が LLVM の `-O0`（FastISel + RegAllocFast）と同じ水準になりました。

- レジスタ割り付けを入れました。ブロック内の値はレジスタに置き、ブロックをまたぐ値はスタック上の置き場所に書き通します。比較と分岐の融合、即値・メモリオペランド・アドレス形式の畳み込み、xmm レジスタ上の浮動小数点と 8/16 バイトのベクトルも扱います。設計は [`backend-goose/DESIGN.md`](backend-goose/DESIGN.md) です。
- `bench/codequal` の実行時間は llc -O0 の 0.98 倍、`.text` は 1.05 倍です（A1 は 1.72 倍と 4.2 倍）。CTMark の C プログラムの実行時間は clang -O0 の 0.95〜1.01 倍（幾何平均 0.99、A1 は 2.78）、Vector/build2 は 1.15 倍（A1 は 10.9 倍）です。
- バックエンドの時間は A1 の 1.04〜1.32 倍です。エクスポータを2倍速くしたので、goovm 全体（書き出しとバックエンド）は A1 より速く、gen-20000 と spass では TPDE の Compile より速いままです（typeset では 1.17 倍）。
- 計測結果は [`bench/results/a2-2026-11-06/`](bench/results/a2-2026-11-06/) と [`backend-goose/NOTES.md`](backend-goose/NOTES.md) の9節にあります。

A1 から変わらない点:

- GIR は版2になりました（型表、i128・f80・集約・ベクトル、デバッグ位置、ABI 属性、TLS、別名、セクションなど）。仕様は [`gir/README.md`](gir/README.md) です。
- 書き出せない IR に出会うと、終了コード2と理由を出して止まります。`--fallback` を付けると、その入力だけ LLVM の `-O0` コード生成に任せ、標準エラーにそう書きます。
- 正しさは [`tests/suite.py`](tests/README.md) で確かめます（gcc-c-torture、llvm-test-suite の SingleSource と CTMark）。
- C++ 版バックエンド（v0）はコミット `8f55b18` で凍結し、既定のビルドから外しました（[`backend-cpp/README.md`](backend-cpp/README.md)）。

## マイルストーン B2：LLVM なしの C コンパイラ

`frontend-goose/` の `goosecc` が、C のソースから x86-64 の ELF オブジェクトまでを一つの Goose プログラムで作るコンパイラになりました（`goosecc -c file.c -o file.o`）。型付き AST を GIR 版2に下ろし、Goose 版バックエンドを同じプロセス内でパッケージとして呼びます。LLVM は使いません。

- 意味は clang-20 の `-O0` に合わせています（SysV の呼び出し規約、`va_arg`、ビットフィールド、VLA、静的データと再配置、組み込み関数、アトミック、TLS、インラインアセンブリ、`-g` のデバッグ位置）。設計は [`frontend-goose/DESIGN.md`](frontend-goose/DESIGN.md) の §7 です。
- 正しさは [`tests/suite_goosecc.py`](tests/README.md) で確かめます。gcc-c-torture、SingleSource、CTMark の6本で、clang-20 `-O0` で通る1,804件すべてが、`-g` の有無の両方で通ります（3,608回、失敗0）。
- 速さは [`tests/bench_goosecc.py`](tests/README.md) で測ります。CTMark の C ファイル284個で `clang-20 -O0 -c` の6.05倍速く（sqlite3.c で10.3倍）、最大メモリは17〜26 MB（clang は103〜137 MB）です。TinyCC はさらに1.4倍速いです。出力コードは A1 のバックエンドのもので、clang `-O0` より大きく遅いです（sqlite3 の `.text` は3.5倍）。

## 構成

| 場所 | 内容 |
|---|---|
| `gir/` | 平坦 IR（GIR 版2）の仕様。C++ と Goose の間で、コピーせずに受け渡す |
| `tools/goovm-llc/` | LLVM 20 のビットコードを GIR に書き出し、Goose 版バックエンドで ELF にするドライバ |
| `backend-goose/` | Goose で書いた x86-64 `-O0` バックエンド（設計は `DESIGN.md`、移植と開発の記録は `NOTES.md`） |
| `backend-cpp/` | v0 の C++ 版バックエンド。`8f55b18` で凍結し、ビルドしない |
| `frontend-goose/` | Goose で一から書いた C コンパイラ `goosecc`（プリプロセッサ・構文解析・型検査・GIR への変換。Goose 版バックエンドを同じプロセスで呼び、LLVM なしで ELF オブジェクトを出す） |
| `tools/goovm-cc/` | clang のフロントエンドを同じプロセス内で動かし、LLVM IR をそのままバックエンドへ渡す `clang -c` 代替 |
| `tests/` | `suite.py`（C と C++ の各コーパスでの正しさの検証、`--verify-dwarf`）、`gdb_oracle.py`（clang `-O0 -g` との gdb の比較と巻き戻しの検査）、`suite_goosecc.py`（同じコーパスを goosecc で）、`bench_goosecc.py`（goosecc の速さ）、C と C++ のテストプログラム52本（`run.py`） |
| `bench/` | CTMark、LLVM 自身のビルド、バックエンド、要因の切り分け、出力コードの質、全体への効果の計測 |
| `poc/` | Goose コンパイラの伸び方、C++ との接続、変更可能な IR グラフの試作 |

## ビルド

```bash
# 必要なもの: clang-20 / llvm-20-dev / lld-20 (Ubuntu 24.04)、cmake、ninja、ビルド済みの goose
GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib backend-goose/build.sh build
tests/run.py --goovm build/tools/goovm-llc/goovm-llc
tests/suite.py --goovm build/tools/goovm-llc/goovm-llc --cc build/tools/goovm-cc/goovm-cc \
    --variants O0,g,mem2reg,cc,cc-g --verify-dwarf --work /tmp/suite -j3 --report report.md
tests/gdb_oracle.py --goovm build/tools/goovm-llc/goovm-llc -j3            # clang -O0 -g と gdb で比較
tests/gdb_oracle.py --goovm build/tools/goovm-llc/goovm-llc --unwind -j3   # 1命令ずつの巻き戻し検査
# goosecc（LLVM 不要）
GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib frontend-goose/build.sh
tests/suite_goosecc.py --goosecc frontend-goose/build/goosecc --work /tmp/sgc -j3 --report report-goosecc.md
tests/bench_goosecc.py --goosecc frontend-goose/build/goosecc -n 3 --md bench-goosecc.md
```

`backend-goose/build.sh` は CMake に `-DGOOVM_GOOSE=… -DGOOVM_GOOSE_STDLIB=…` を渡すだけです。v0 を作り直す方法は `backend-cpp/README.md` にあります。フェーズ0〜2の詳しい再現方法は、検証結果の報告書の §8 にあります。
