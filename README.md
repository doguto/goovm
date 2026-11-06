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

## 現在の状態（マイルストーン A1）

バックエンドは Goose 版だけを育てます。A1 で、clang-20 が `-O0`（`-g` 付き、`mem2reg` 後を含む）で出す C の LLVM IR をすべて扱う `-O0` バックエンドになりました。

- GIR は版2になりました（型表、i128・f80・集約・ベクトル、デバッグ位置、ABI 属性、TLS、別名、セクションなど）。仕様は [`gir/README.md`](gir/README.md) です。
- 書き出せない IR に出会うと、終了コード2と理由を出して止まります。`--fallback` を付けると、その入力だけ LLVM の `-O0` コード生成に任せ、標準エラーにそう書きます。
- 正しさは [`tests/suite.py`](tests/README.md) で確かめます（gcc-c-torture、llvm-test-suite の SingleSource と CTMark）。
- C++ 版バックエンド（v0）はコミット `8f55b18` で凍結し、既定のビルドから外しました（[`backend-cpp/README.md`](backend-cpp/README.md)）。

## 構成

| 場所 | 内容 |
|---|---|
| `gir/` | 平坦 IR（GIR 版2）の仕様。C++ と Goose の間で、コピーせずに受け渡す |
| `tools/goovm-llc/` | LLVM 20 のビットコードを GIR に書き出し、Goose 版バックエンドで ELF にするドライバ |
| `backend-goose/` | Goose で書いた x86-64 `-O0` バックエンド（設計は `DESIGN.md`、移植と開発の記録は `NOTES.md`） |
| `backend-cpp/` | v0 の C++ 版バックエンド。`8f55b18` で凍結し、ビルドしない |
| `frontend-goose/` | Goose で一から書いた C フロントエンド `goosecc`（プリプロセッサ・構文解析・型検査。clang-20 と出力を突き合わせて検証） |
| `tools/goovm-cc/` | clang のフロントエンドを同じプロセス内で動かし、LLVM IR をそのままバックエンドへ渡す `clang -c` 代替 |
| `tests/` | `suite.py`（各コーパスでの正しさの検証）と、C テストプログラム44本（`run.py`） |
| `bench/` | CTMark、LLVM 自身のビルド、バックエンド、要因の切り分け、出力コードの質、全体への効果の計測 |
| `poc/` | Goose コンパイラの伸び方、C++ との接続、変更可能な IR グラフの試作 |

## ビルド

```bash
# 必要なもの: clang-20 / llvm-20-dev / lld-20 (Ubuntu 24.04)、cmake、ninja、ビルド済みの goose
GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib backend-goose/build.sh build
tests/run.py --goovm build/tools/goovm-llc/goovm-llc
tests/suite.py --goovm build/tools/goovm-llc/goovm-llc --work /tmp/suite -j3 --report report.md
```

`backend-goose/build.sh` は CMake に `-DGOOVM_GOOSE=… -DGOOVM_GOOSE_STDLIB=…` を渡すだけです。v0 を作り直す方法は `backend-cpp/README.md` にあります。フェーズ0〜2の詳しい再現方法は、検証結果の報告書の §8 にあります。
