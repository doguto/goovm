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

## 構成

| 場所 | 内容 |
|---|---|
| `gir/` | 平坦 IR（GIR）の仕様。C++ と Goose の間で、コピーせずに受け渡す |
| `tools/goovm-llc/` | LLVM 20 のビットコードを GIR に書き出し、各バックエンドで ELF にするドライバ |
| `backend-cpp/` | 一発生成型の x86-64 バックエンド（C++） |
| `backend-goose/` | 同じバックエンドを Goose へ1対1で移植したもの（`NOTES.md` に移植の記録） |
| `tests/` | C テストプログラム35本による正しさの検証 |
| `bench/` | CTMark、LLVM 自身のビルド、バックエンド、要因の切り分け、出力コードの質、全体への効果の計測 |
| `poc/` | Goose コンパイラの伸び方、C++ との接続、変更可能な IR グラフの試作 |

## ビルド

```bash
# 必要なもの: clang-20 / llvm-20-dev / lld-20 (Ubuntu 24.04)、cmake、ninja。Goose 版にはビルド済みの goose
cmake -G Ninja -S . -B build -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=clang-20 \
  -DCMAKE_CXX_COMPILER=clang++-20 -DLLVM_DIR=/usr/lib/llvm-20/lib/cmake/llvm && ninja -C build
tests/run.py --goovm build/tools/goovm-llc/goovm-llc
# Goose 版も含める場合
GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib backend-goose/build.sh build-goose
```

詳しい再現方法は、検証結果の報告書の §8 にあります。
