# Reversi_5C
大学2の時、開発実習で作成したリバーシのAI
名前は5回作り直したからと、高速化のためにPython -> C++ に言語を変えたからこうなった。

実機のロボットに組み込み、GUIで操作できるように作成したが遊べるようにするのが大変だったので
C++で書いた部分(思考ルーチンのみ)を置いておく。

今見直すとソースコードがかなり汚くてはずかしすぎるｗ

## 探索
基本的には αβ探索 & 置換表 を組み合わせたMTD(f)を使用してIDDFS探索を行う。
高速化のためボードにはビットボードを使ったり、終盤には専用にチューニングしたαβ探索 & 置換表を用いるような工夫をしている。

## 評価関数
評価関数にはLogistelloを参考にしたパターンによるものを使用した。
基本的には重線形回帰を用い、30通りの評価関数を用いる(ボードは64マス、初期設置4個なので60手あるので2手毎に評価関数が変わる)。
インターネットから取得した棋譜データ約30万件を最小二乗法を用いて学習させた。

## 探索速度（だいたい）
|中盤探索（20ターン目） | 探索時間 (s)| ノード数 |
|---------------------|------------|----------|
|6手読み               | 0.0488     | 28084    |
|9手読み               | 0.582      | 539765   |


|終盤探索（読み切り）   | 探索時間 (s)|ノード数   |
|---------------------|------------|-----------|
|15手読み              | 0.0822    | 812462     |
|20手読み              | 11.1      | 105727987  |

おすすめコンパイルオプション
```console
g++ -fPIC -O3 -flto -mtune=native -march=native robot_c.cpp
```

# 参考ページ
- リバーシプログラムの作り方
http://www.es-cube.net/es-cube/reversi/sample/index.html
- オセロプログラムの作り方
http://hp.vector.co.jp/authors/VA015468/platina/algo/
- 強いオセロプログラムの内部動作
http://www.amy.hi-ho.ne.jp/okuhara/howtoj.htm
- マイケル・ブロー(1997)「Experiments with Multi-ProbCut and a New
High-Quality Evaluation Function for Othello」
https://skatgame.net/mburo/publications.html
