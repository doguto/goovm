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

## 現在の状態（マイルストーン C1）

C1 で、浮動小数点を多く使うコードの実行時間が clang `-O0` と同等になりました。CTMark の全10本が clang `-O0` の0.95〜1.02倍です（幾何平均0.98倍。C1 前は1.07倍）。Bullet は1.69倍から0.97倍、tramp3d-v4 は1.19倍から1.02倍になりました。設計は [`backend-goose/DESIGN.md`](backend-goose/DESIGN.md) の §14、原因とその割合、計測は [`backend-goose/NOTES.md`](backend-goose/NOTES.md) の11節と [`bench/results/c1-2026-11-07/`](bench/results/c1-2026-11-07/) です。

- **原因は浮動小数点の演算ではありませんでした。** 加減乗除・比較・変換の命令列は、もともと LLVM の FastISel と同等でした。
  - Bullet（差の100%）：`btVector3` のような小さな構造体の戻り値を、狭い幅で書いて広い幅で読み直していました。ストアからロードへの転送が失敗して、1回ごとに約15サイクル待ちます。呼び出しの戻り値を戻りのレジスタのまま受け取り、`extractvalue` を読み込みにし、小さな `memcpy` を FastISel と同じ8バイト単位で写すようにしました。
  - tramp3d-v4（差の95%）：関数の出口の `leave` です。このホストでは戻りごとに約5サイクル余分にかかります。出口を LLVM と同じ `add rsp, n; pop rbp` にしました。
- **SingleSource の浮動小数点ベンチマーク**：変換命令の偽の依存（書き込み先の前の値を待つ）を断ち、配列の読み込みをプログラムの順にしました。spectral-norm は1.63倍から0.53倍、fp-convert は1.53倍から0.77倍、Linpack は1.14倍から0.98倍です。
- 整数のカーネル集（`bench/codequal`）は llc `-O0` の1.03倍から0.99倍。バックエンドのコンパイル時間は A3 の1.02倍です。
- テストを足しました：`tests/ll/`（手書きの LLVM IR と C の呼び出し側。`tests/run.py` が扱います）、`tests/cxx/03_fp_structs.cpp`、`tests/c/50_fp_classify.c`、`tests/c/51_fp_convert.c`。
- 正しさ：全コーパス（C と C++ の1,921本、clang で通る1,915本）の全変種（O0、g、mem2reg、cc、cc-g）で失敗0、フォールバック0。`-g` の全オブジェクト（5,266個）が `llvm-dwarfdump --verify` を通ります。

## マイルストーン D1：goosecc の C++ フロントエンド（第一段階）

`goosecc` に、Goose で書いた C++ のフロントエンドの第一段階を加えました（`frontend-goose/src/cx_*.goose`、約11,400行）。設計とロードマップ（D2：テンプレートの実体化、D3：例外と残りのコード生成、D4：C++20）は [`frontend-goose/DESIGN.md`](frontend-goose/DESIGN.md) の §13、記録は [`frontend-goose/NOTES.md`](frontend-goose/NOTES.md) の14節、報告書の §7、計測と検証の記録は [`bench/results/d1-2026-11-08/`](bench/results/d1-2026-11-08/) です。バックエンド、GIR、`tools/` は変えていません。

- **前処理：** C++ のコーパス423本と、libstdc++ の全ヘッダを6つの規格で読む647本が、`clang++-20 -E` とトークン単位で同一です。
- **構文解析と宣言：** 423本すべてを誤ったエラーなしで受け付けます。libstdc++ のヘッダは C++98〜C++17 で全部、`gnu++20` では concepts を使う75本が未対応です。レイアウト（30.7万個の `static_assert`）と Itanium のマングル名（8,528個。誤り0、テンプレート内の171個は未出力）を clang と突き合わせて一致しています。
- **コード生成（「クラス付きの C」）：** クラス、仮想関数（vtable と typeinfo）、コンストラクタとデストラクタ、参照、オーバーロードと演算子、名前空間、`new`/`delete`、静的初期化、メンバへのポインタ。SingleSource の C++ テスト111本のうち28本が `-O0` と `-g` で通り、残りはテンプレート・例外などの「未対応」のエラーで止まります（誤ったコードは0本）。
- **速さ**（CTMark の C++ 316本、3回の最良値）：`-E` は clang++ の3.9倍（温まったヘッダキャッシュで13.9倍）、`-fsyntax-only` は8.7倍速い（ただし D1 はテンプレートを実体化しないので、仕事の量が違います）。
- **C は変わっていません：** C のコーパス2,357本の全出力（`-E`、構文木、レイアウト、`-c`、`-c -g`）が D1 前とバイト単位で同一で、C の全オラクルと 1,804件のテスト（`-O0`、`-g`）も通ります。C のコンパイル時間は +1.4%（キャッシュあり +0.6%）です。

## マイルストーン G1：goosecc の起動、構文解析のキャッシュ、clang の畳み込み

G1 で、`goosecc` のプロセス起動を1ミリ秒よりずっと短くし、ヘッダの宣言の構文解析と型検査を永続キャッシュで再生するようにし、clang-20 が `-O0` でも行う畳み込みとインライン展開を取り入れました。設計は [`frontend-goose/DESIGN.md`](frontend-goose/DESIGN.md) の §12、記録は [`frontend-goose/NOTES.md`](frontend-goose/NOTES.md) の13節、ランタイムへのパッチと Goose の作者への提案は [`frontend-goose/runtime-patches/README.md`](frontend-goose/runtime-patches/README.md)、計測と検証の記録は [`bench/results/g1-2026-11-07/`](bench/results/g1-2026-11-07/) です。バックエンド、GIR、`tools/` は変えていません。

- **起動：** 1行のファイルのコンパイルが1.19 ms から0.65 ms になりました（静かなマシンで、`exec` と終了を含む）。以前の半分は、Goose ランタイムが420個のデータスタック領域を1つずつ `mmap` していた時間です。生成された C に埋め込まれたランタイムに `build.sh` がパッチを当て、全領域を1回の予約の中の枠にしました。枠は最初に触れたときに SIGSEGV ハンドラが `mprotect` で有効にします。ほぼ毎回使う146領域は先頭に詰め、起動時に有効にします。
- **構文解析のキャッシュ：** ファイル先頭の `#include` の並びを読み終えた時点の構文解析器の状態（29個の表と辞書）を差分として保存し、同じ並びで始まる次のコンパイルで再生します。キーはインクルードごとのヘッダキャッシュの blob、オプション、組み込みの定義です。ソース上の位置は、メインファイルの長さの差だけずらします。CTMark の構文解析と型検査は218 ms から153 ms になりました。
- **速さ**（`tests/bench_hcache.py -n 3`、CTMark の C ファイル316本を1本ずつ単独で、3回の最良値。マシンは別の作業と共用で、負荷平均1.6〜3）：

  | 設定 | G1 前 | G1 | TinyCC | clang `-O0` |
  |---|---:|---:|---:|---:|
  | キャッシュなし | 1.60秒 | **1.48秒** | 1.61秒 | 13.45秒 |
  | 温まったキャッシュ | 1.33秒 | **1.19秒（TinyCC の1.35倍、clang の11.3倍速い）** | | |

  - 目標の「温まったキャッシュで TinyCC の1.3倍以上」と「キャッシュなしで TinyCC より遅くない」は満たしました。
  - **sqlite3.c 単体は TinyCC に届きませんでした**（キャッシュなしで34.0 ms、G1 前は37.5 ms。TinyCC は24.5 ms）。25万行のほぼ全部が自分のコードで、どちらのキャッシュも効きません。実行命令数は約2.8億で、TinyCC の約2.1億より多く、その4分の1が前処理のマクロ展開と字句解析です。
- **clang との一致：** const 変数の読み出し（`DW_AT_const_value` を含む）、アドレスの差、`strlen`/`memchr`、`__builtin_constant_p`、GNU モードの配列の長さ、NRVO、`nodebug` 関数、`always_inline` かつ `nodebug` の関数（x86 の組み込み関数）のインライン展開を、clang と同じにしました。
  - `tests/dwarf_diff.py`：両方がコンパイルできる2,289本のうち、clang と同一の DWARF が2,231本から2,268本に、違うものが44本から9本になりました。CTMark では324本中323本が同一です。残る9本のうち8本は、デバッグ情報を持つ `always_inline` 関数です（clang は展開して `DW_TAG_inlined_subroutine` で記述し、goosecc は呼び出します）。
  - gdb での比較：B5 と同じ79本のうち、やりとり全体が一致したのは46本（B5 は45本）。
- **正しさ：** 構文解析のキャッシュを含めて、`cache_check.py`（2,357本、44,783回。構文解析器の全状態のチェックサムも比較）、`pcache_check.py`（メインファイルを水増しして全位置をずらした再生、9,428回）、敵対的な試験17件がすべて一致しました。`tests/suite_goosecc.py`（1,804件、`-O0` と `-g`）、`tests/run.py --goosecc`（108/108）、フロントエンドの4つの突き合わせも失敗0です。G1 前とのオブジェクトの差113本は、すべて意図した変更のどれかに由来することを確かめました（`noinit` 1本、const の畳み込み74本、`strlen`・NRVO など34本、組み込み関数の展開4本）。
- `__attribute__((noinit))` がコンパイルできるようになりました（clang-20 は x86-64 では無視するので、同じく無視します）。

## マイルストーン B5：goosecc のデバッグ情報

`goosecc -g` が、clang-20 `-O0 -g` と同じ DWARF 5 を出すようになりました。行テーブルに加えて、変数、引数、型、スコープ、ラベル、大域変数（関数内の static 変数を含む）、文字列リテラルです。型はビットフィールド、VLA、列挙型、関数ポインタ、ベクトル、複素数、`_Atomic`、typedef（書かれたとおりの名前）を含めてすべて出します。DIE は goosecc 自身の AST と型から作り、GIR の `dies`/`dattrs` 表でバックエンドに渡します。バックエンド、GIR、`tools/` は変えていません。設計は [`frontend-goose/DESIGN.md`](frontend-goose/DESIGN.md) の §11、記録は [`frontend-goose/NOTES.md`](frontend-goose/NOTES.md) の12節です。

- **clang との突き合わせ**（`tests/dwarf_diff.py`）：コーパスの C ファイル2,357本のうち、両方がコンパイルできる2,288本で、正規化した `llvm-dwarfdump --debug-info` が2,231本（97.5%）で clang と同一でした。さらに13本は、フレーム上の位置の書き方だけが違います。残る44本の差は、すべて生成コードの違いから来ます（clang が const 変数の読み出しを畳み込む、`always_inline` を `-O0` でもインライン展開する、など）。CTMark の C ファイルでは、両方がコンパイルできる324本のうち316本が同一です。goosecc の `-g` オブジェクト2,288個は、すべて `llvm-dwarfdump --verify` を通ります。
- **gdb での比較**（`tests/gdb_oracle.py --goosecc`）：C のプログラム79本（`tests/c` の49本、llvm-test-suite の24本、CTMark の C 6本を入力付きで）、1,458回の停止で、各停止ごとに引数と局所変数すべての `ptype` と `print` も比べました。やりとり全体が一致したのは45本です。ただし両方が同じ場所で止まった6,859回の停止では、両方に現れる変数の `ptype` は1件を除いてすべて一致し（例外は goosecc が VLA にする `const int` 長の配列）、`print` の値も98.9%が一致しました。残りの値の差は、未初期化のメモリの中身と、同じ行の別の命令で止まったことによるものです。やりとりが違う34本のうち32本は、止まる行そのものが違います。これは B4 からの行テーブルの差（たとえば goosecc は then 節から抜ける分岐に `}` の行を付ける）で、B5 では文の行（is_stmt の行）を変えていません。
- **速さ**（`tests/bench_goosecc.py --g`、CTMark の C ファイル284本）：`-g` を付けると goosecc は1.25倍の時間になります（1.73秒 → 2.17秒、sqlite3.c は1.57倍）。それでも clang-20 `-O0 -g`（19.8秒）より9.1倍速いです。最大メモリは24 MB から35 MB になります（clang は182 MB）。
- **回帰なし**：`tests/suite_goosecc.py`（1,804件、`-O0` と `-g`）、`tests/run.py --goosecc`（98/98）、フロントエンドの4つの突き合わせ（前処理、構文、レイアウト、型付き構文木）、`cache_check.py`（2,357本、44,783回）がすべて B4 と同じ結果です。`-g` なしのオブジェクトは2,288本中2,239本が B4 とバイト単位で同一で、残る49本は `__PRETTY_FUNCTION__`（主に `assert` 経由）を使うファイルで、その文字列のセクションだけが違います（`.text` は同一）。B5 で `__PRETTY_FUNCTION__` を clang と同じ文字列にしたためです（以前は関数名だけでした）。

## マイルストーン A3：デバッガ、例外、C++

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
| `tests/` | `suite.py`（C と C++ の各コーパスでの正しさの検証、`--verify-dwarf`）、`gdb_oracle.py`（clang `-O0 -g` との gdb の比較と巻き戻しの検査）、`suite_goosecc.py`（同じコーパスを goosecc で）、`bench_goosecc.py`（goosecc の速さ）、C、C++、LLVM IR のテストプログラム57本（`run.py`） |
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
