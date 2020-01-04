// #include <boost/python.hpp>
#include <stdio.h>
#include <time.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>

// 探索深さの設定
#define SEARCH_DEPTH 9
#define END_DEPTH 19  // 読み切り

//評価値出力にかけられている
#define RVC 1

//定数宣言
#define NONE -9999
#define MAX_VAL 29999
#define MIN_VAL -29999

//置換表の宣言
#define HASH_BUFFER_SIZE_MEGA_BYTE 900//ハッシュテーブルのサイズ[MB]
#define HASH_BUFFER_SIZE (int)((double)HASH_BUFFER_SIZE_MEGA_BYTE / (5.0 * 4.0 / 1000000.0) )//要素数を計算
#define HASH_BUFFER_RANGE  HASH_BUFFER_SIZE * 0.9 //これ以上の領域は、レコードの競合時使われる

//棋譜宣言
#define KIHU_ALL_DATA 326000//660000 326000
#define KIHU_TEST_DATA 36000

//MPC宣言
#define MPC_PAIR_NUM 8//MPCのペア数
#define MPC_STAGE 50//ステージ分割数
#define MPC_MAX 13//最大深度
#define MPC_MIN 3//最小深度

double MPC_parameter[MPC_PAIR_NUM][MPC_STAGE][3];//MPCのパラメータ 0:a(傾き) 1:b(切片) 2:e(標準偏差)

//カットペア
int MPC_pair[MPC_PAIR_NUM][2] ={
                            {3,2},{4,2},
                            {5,2},{6,3},
                            {7,3},{8,3},
                            {9,4},{10,4}
                            };

//評価関数の宣言
#define USE_PTN 11
#define STAGE_PTN 30//現在の評価関数は、過去のものに対して約66%の勝率がある
#define WEIGHT_NUMBER  (3321*4 + 1134*1 + 378*1 + 243*1 +45*1 + 29645*2 + 9963*1) //20MB程度

int node_count = 0;//展開されたノードの数を数える

uint64_t *hash_hash;
int *hash_next;
int *hash_depth;
int *hash_upper;
int *hash_lower;
int hash_last_index;
int hash_malloc_flag = 0;

uint64_t adrs[64];

int MergeSort_temp_base[60];
uint64_t MergeSort_temp_to[60];

time_t timeout;

void init_data_table();
void clear_hash();

//ハッシュテーブルの領域を確保する, alpha_beta 以外の探索で必須
void hash_malloc(){
    if(hash_malloc_flag == 1) return;
    hash_malloc_flag = 1;

    hash_hash =  (uint64_t *)malloc(HASH_BUFFER_SIZE *sizeof(uint64_t));
    hash_next  = (int *)malloc(HASH_BUFFER_SIZE * sizeof(int));
    hash_depth = (int *)malloc(HASH_BUFFER_SIZE * sizeof(int));
    hash_upper = (int *)malloc(HASH_BUFFER_SIZE * sizeof(int));
    hash_lower = (int *)malloc(HASH_BUFFER_SIZE * sizeof(int));
    printf("Hash malloc ok\n");
    clear_hash();
}

//ハッシュテーブルの領域を開放する
void hash_free(){
    if(hash_malloc_flag == 0) return;
    hash_malloc_flag = 0;

    free(hash_hash);
    free(hash_next);
    free(hash_depth);
    free(hash_lower);
    free(hash_upper);
    printf("Hash free ok\n");
}

//64bit counter uint64_t型を引数に、立ち上がっているビットの数を返す
inline int bitcnt64(uint64_t x){
    x = ((x & 0xaaaaaaaaaaaaaaaaUL) >> 1)
      +  (x & 0x5555555555555555UL);
    x = ((x & 0xccccccccccccccccUL) >> 2)
      +  (x & 0x3333333333333333UL);
    x = ((x & 0xf0f0f0f0f0f0f0f0UL) >> 4)
      +  (x & 0x0f0f0f0f0f0f0f0fUL);
    x = ((x & 0xff00ff00ff00ff00UL) >> 8)
      +  (x & 0x00ff00ff00ff00ffUL);
    x = ((x & 0xffff0000ffff0000UL) >> 16)
      +  (x & 0x0000ffff0000ffffUL);
    x = ((x & 0xffffffff00000000UL) >> 32)
      +  (x & 0x00000000ffffffffUL);
    return (int)x;
}

//マージソート ムーブオーダリングで使用している
void MergeSort(int base[ ],uint64_t to[ ], int left, int right){
    int mid, i, j, k;

    if (left >= right)              /* 配列の要素がひとつなら */
        return;                     /* 何もしないで戻る */

                                    /* ここでは分割しているだけ */
    mid = (left + right) / 2;       /* 中央の値より */
    MergeSort(base ,to , left, mid);        /* 左を再帰呼び出し */
    MergeSort(base , to, mid + 1, right);   /* 右を再帰呼び出し */

      /* x[left] から x[mid] を作業領域にコピー */
    for (i = left; i <= mid; i++){
        MergeSort_temp_base[i] = base[i];
        MergeSort_temp_to[i] = to[i];
    }


      /* x[mid + 1] から x[right] は逆順にコピー */
    for (i = mid + 1, j = right; i <= right; i++, j--){
        MergeSort_temp_base[i] = base[j];
        MergeSort_temp_to[i] = to[j];
    }


    i = left;         /* i とj は作業領域のデーターを */
    j = right;        /* k は配列の要素を指している */

    for (k = left; k <= right; k++){
        /* 小さい方から配列に戻す */
        /* ここでソートされる */
        if (MergeSort_temp_base[i] <= MergeSort_temp_base[j]){
            base[k] = MergeSort_temp_base[i];
            to[k] = MergeSort_temp_to[i++];
        }else{
            base[k] = MergeSort_temp_base[j];
            to[k] = MergeSort_temp_to[j--];

        }
    }

}

  /* 配列の要素を交換する */
void Swap(int base[],uint64_t to[], int i, int j){
    int temp;
    uint64_t temp_64;

    temp = base[i];
    base[i] = base[j];
    base[j] = temp;

    temp_64 = to[i];
    to[i] = to[j];
    to[j] = temp_64;
}

//typedef unsigned int uint32_t
//typedef unsigned long long int uint64_t

class board{
public:
    uint64_t black;//黒用
    uint64_t white;//白用
    uint64_t can;//合法手
    int cannum;//合法手の数
    int turn;//手番
    int pass_flag;//前回パスが発生
    int end_flag;//ゲーム終了
    int phase;
    int board_size;//ボード1ぺんの長さ
    uint64_t board_mask;//ボードのマスク

    void init_board(int size=8){
        black = adrs[3*8+4] | adrs[4*8+3];//初期配置を作成
        white = adrs[3*8+3] | adrs[4*8+4];

        turn = 1;
        can = 0;
        cannum = 0;
        phase = 0;
        end_flag = 0;

        switch(size){
            case 4:
                board_mask = 0x00003C3C3C3C0000;//周り2マスを削る
                board_size = 4;
            break;
            case 6:
                board_mask = 0x007E7E7E7E7E7E00;//周り1マスを削る
                board_size = 6;
            break;
            default:
                board_size = 6;
                board_mask = 0xFFFFFFFFFFFFFFFF;
        }

        search();
    }

    board(int size = 8){//コンストラクタ
        init_data_table();
        init_board(size);
    }

    ~board(){//ディストラクタ
    }

    void search(){//合法手の座標及び数を、can,cannumへ格納
        uint64_t me,enemy,masked_enemy,blank,t;

        if(turn == 1){
            me = black;
            enemy = white;
        }else{
            me = white;
            enemy = black;
        }

        blank = ~(black | white) ;

        masked_enemy = enemy & 0x7e7e7e7e7e7e7e7eUL;
        t = masked_enemy & (me << 1);
        t |= masked_enemy & (t << 1);
        t |= masked_enemy & (t << 1);
        t |= masked_enemy & (t << 1);
        t |= masked_enemy & (t << 1);
        t |= masked_enemy & (t << 1);
        can = blank & (t << 1);

        masked_enemy = enemy & 0x7e7e7e7e7e7e7e7eUL;
        t = masked_enemy & (me >> 1);
        t |= masked_enemy & (t >> 1);
        t |= masked_enemy & (t >> 1);
        t |= masked_enemy & (t >> 1);
        t |= masked_enemy & (t >> 1);
        t |= masked_enemy & (t >> 1);
        can |= blank & (t >> 1);


        masked_enemy = enemy & 0x00ffffffffffff00UL;
        t = masked_enemy & (me << 8);
        t |= masked_enemy & (t << 8);
        t |= masked_enemy & (t << 8);
        t |= masked_enemy & (t << 8);
        t |= masked_enemy & (t << 8);
        t |= masked_enemy & (t << 8);
        can |= blank & (t << 8);


        masked_enemy = enemy & 0x00ffffffffffff00UL;
        t = masked_enemy & (me >> 8);
        t |= masked_enemy & (t >> 8);
        t |= masked_enemy & (t >> 8);
        t |= masked_enemy & (t >> 8);
        t |= masked_enemy & (t >> 8);
        t |= masked_enemy & (t >> 8);
        can |= blank & (t >> 8);


        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        t = masked_enemy & (me << 7);
        t |= masked_enemy & (t << 7);
        t |= masked_enemy & (t << 7);
        t |= masked_enemy & (t << 7);
        t |= masked_enemy & (t << 7);
        t |= masked_enemy & (t << 7);
        can |= blank & (t << 7);


        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        t = masked_enemy & (me << 9);
        t |= masked_enemy & (t << 9);
        t |= masked_enemy & (t << 9);
        t |= masked_enemy & (t << 9);
        t |= masked_enemy & (t << 9);
        t |= masked_enemy & (t << 9);
        can |= blank & (t << 9);

        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        t = masked_enemy & (me >> 9);
        t |= masked_enemy & (t >> 9);
        t |= masked_enemy & (t >> 9);
        t |= masked_enemy & (t >> 9);
        t |= masked_enemy & (t >> 9);
        t |= masked_enemy & (t >> 9);
        can |= blank & (t >> 9);


        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        t = masked_enemy & (me >> 7);
        t |= masked_enemy & (t >> 7);
        t |= masked_enemy & (t >> 7);
        t |= masked_enemy & (t >> 7);
        t |= masked_enemy & (t >> 7);
        t |= masked_enemy & (t >> 7);
        can |= blank & (t >> 7);

        can &=  board_mask;

        cannum = bitcnt64(can);//canの数を保持しておく
    }

    int put_xy(int x,int y){//x=0~7 y=0~7で指定して置く
        if(x >= 0 && x<8 && y >= 0 && y < 8){
            return put(adrs[y*8+x]);
        }
        printf("Out of range. X,Y(0~7)\n");
        return 0;

    }

    int put(uint64_t pos ,int check_mask = 0){//置くためのビットボードを入力する。
        uint64_t rev=0;
        uint64_t me,enemy,masked_enemy,rev_cand,copied_pos;

        if(check_mask == 0 && (pos & can)==0){
            printf("Can't put here.\n");
            return 0;
        }

        if(turn == 1){
            me = black;
            enemy = white;
        }else{
            me = white;
            enemy = black;
        }

        masked_enemy = enemy & 0x7e7e7e7e7e7e7e7eUL;
        copied_pos =pos >> 1;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos >> 1;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos >> 1;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos >> 1;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos >> 1;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos >> 1;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos >> 1;
                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                rev |= rev_cand;
            }

        }

        // 左方向
        masked_enemy = enemy & 0x7e7e7e7e7e7e7e7eUL;
        copied_pos =pos << 1;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos << 1;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos << 1;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos << 1;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos << 1;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos << 1;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos << 1;
                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                rev |= rev_cand;
            }
        }

        // 上方向

        masked_enemy = enemy & 0x00ffffffffffff00UL;
        copied_pos =pos << 8;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos << 8;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos << 8;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos << 8;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos << 8;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos << 8;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos << 8;
                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                 rev |= rev_cand;
             }
        }
        // 下方向

        masked_enemy = enemy & 0x00ffffffffffff00UL;
        copied_pos =pos >> 8;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos >> 8;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos >> 8;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos >> 8;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos >> 8;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos >> 8;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos >> 8;

                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                 rev |= rev_cand;
             }
        }
        // 右上方向

        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        copied_pos =pos << 7;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos << 7;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos << 7;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos << 7;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos << 7;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos << 7;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos << 7;

                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                 rev |= rev_cand;
             }
        }
        // 左上方向

        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        copied_pos =pos << 9;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos << 9;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos << 9;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos << 9;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos << 9;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos << 9;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos << 9;
                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                 rev |= rev_cand;
             }
        }

        // 右下方向

        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        copied_pos =pos >> 9;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos >> 9;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos >> 9;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos >> 9;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos >> 9;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos >> 9;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos >> 9;
                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                 rev |= rev_cand;
             }
        }


        // 左下方向

        masked_enemy = enemy & 0x007e7e7e7e7e7e00UL;
        copied_pos =pos >> 7;
        if( (copied_pos & masked_enemy) != 0){
            rev_cand = copied_pos;
            copied_pos =copied_pos >> 7;
            if( (copied_pos & masked_enemy) != 0){
                rev_cand |= copied_pos;
                copied_pos =copied_pos >> 7;
                if( (copied_pos & masked_enemy) != 0){
                    rev_cand |= copied_pos;
                    copied_pos =copied_pos >> 7;
                    if( (copied_pos & masked_enemy) != 0){
                        rev_cand |= copied_pos;
                        copied_pos =copied_pos >> 7;
                        if( (copied_pos & masked_enemy) != 0){
                            rev_cand |= copied_pos;
                            copied_pos =copied_pos >> 7;
                            if( (copied_pos & masked_enemy) != 0){
                                rev_cand |= copied_pos;
                                copied_pos =copied_pos >> 7;
                            }
                        }
                    }
                }
            }
            if( ( copied_pos & me) != 0 ){
                 rev |= rev_cand;
             }
        }

        if(turn == 1){
            black ^= rev;
            black |= pos;
            white ^= rev;
        }else{
            white ^= rev;
            white |= pos;
            black ^= rev;
        }
        next_turn();
        return 1;
    }

    void display(){//盤面を展開・表示する
        int y,x;
        printf("   0 1 2 3 4 5 6 7  (X)\n");
        printf("  -----------------\n");
        for(y=0;y<8;y++){
            printf("%d|",y);
            for(x=0;x<8;x++){
                if((adrs[y*8+x]&black) != 0){
                    printf(" @");
                }else if((adrs[y*8+x]&white) != 0){
                    printf(" O");
                }else if((adrs[y*8+x]&can) != 0){
                    printf(" x");
                }else{
                    printf("  ");
                }
            }
            printf(" |\n");
        }
        printf("  -----------------\n");
        printf("(Y)\n");
    }

    void next_turn(){//石を置いた後のターン切り替えやパス・ゲーム終了判定を行う
        pass_flag = 0;
        end_flag = 0;
        cannum = 0;
        turn *= -1;

        search();
        if(cannum == 0){
            pass_flag = 1;
            turn *= -1;
            search();
            if(cannum == 0){
                end_flag = 1;

            }
        }
    }
};

inline int evaluator(board &obj,int turn);
int alpha_beta_with_memory(board &obj,int depth,int al,int bt,int my_turn);
int MTDf(board &obj,int depth,int my_turn);
int search_for_end_game(board &obj,int depth,int al,int bt,int my_turn);
int IDDFS(board &obj,int depth,int my_turn,int time_lim=6);
int IDDFS_MPC(board &obj,int depth,int my_turn,int time_lim);

void init_data_table(){
    static int flag = 0;
    uint64_t num = 1;
    int i;

    if(flag != 0) return;
    flag = 1;

    for(i =0;i<64;i++){
        adrs[i] = num;
        num <<= 1;
    }


    printf("Data table init ok\n");
}

//xor32-SHIFT64による高速な乱数生成器
uint64_t xor64() {
    static uint64_t x = 98623644139ULL;
    x = x ^ ( x<< 13);
    x = x ^(x >> 7);
    return x = x^(x<<17);
}

//ハッシュテーブルのクリア
void clear_hash(){
    int i;
    if(hash_malloc_flag == 0) return;

    hash_last_index = HASH_BUFFER_RANGE;
    for(i = 0;i<HASH_BUFFER_SIZE;i++){
        hash_hash[i] = 0;
        hash_next[i] = -1;
        hash_depth[i] = -1;
        hash_upper[i]= MAX_VAL;
        hash_lower[i]= MIN_VAL;
    }
    //printf("hash table clear ok\n");
}

//ハッシュキーの生成
uint64_t get_hash(board &obj,int my_turn){
    static int flag = 0;
    static uint64_t hs_b[60];
    static uint64_t hs_w[60];
    static uint64_t hs_blnk[60];
    static uint64_t hs_pb[2][60];
    static uint64_t hs_pw[2][60];

    int i;
    uint64_t idx;
    uint64_t hs=0;

    if(flag == 0){
        flag = 1;
        for(i=0;i<60;i++){
            hs_b[i] = xor64();
            hs_w[i] = xor64();
            hs_blnk[i] = xor64();
            hs_pb[0][i] = xor64();
            hs_pw[0][i] = xor64();
            hs_pb[1][i] = xor64();
            hs_pw[1][i] = xor64();
        }

    }

    if(my_turn == 1){
        hs = hs_pb[0][obj.phase];
    }else{
        hs = hs_pw[0][obj.phase];
    }
    if(obj.turn == 1){
        hs ^= hs_pb[1][obj.phase];
    }else{
        hs ^= hs_pw[1][obj.phase];
    }


    idx = 1;
    for(i=0;i<60;i++){
        if((obj.black & idx) != 0){
            hs ^= hs_b[i];
        }else if((obj.white & idx) != 0){
            hs ^= hs_w[i];
        }else{
            hs ^= hs_blnk[i];
        }
        idx <<= 1;
    }
    return hs;
}

//テーブルからキーを検索
int search_index_from_hash_table(uint64_t hs,int depth){
    int idx;

    if(hs <= 0) return NONE;

    idx  = (hs%HASH_BUFFER_RANGE);
    while(1){
        if(hash_hash[idx] == 0){//なかった
            return NONE;
        }

        if(hash_hash[idx] == hs){//発見
            if(hash_depth[idx] < depth){//読み深さが小さいものだったら取り消し
                return NONE;
            }
            return idx;

        }else if(hash_next[idx]==-1){//続きなかった
            return NONE;
        }else{
            idx = hash_next[idx];
        }
    }
    return NONE;
}

void update_hash(uint64_t hs,int depth,int low = NONE, int up = NONE){//テーブルの更新
    int idx;

    if(hs <= 0) return;

    idx  = (hs%HASH_BUFFER_RANGE);

    while(1){

        if(hash_hash[idx] == hs){//上書き更新
            if(hash_depth[idx] < depth){
                if(up != NONE) hash_upper[idx] = up;
                if(low != NONE) hash_lower[idx] = low;

                hash_depth[idx] = depth;
            }
            break;
        }

        if(hash_hash[idx] == 0){//空だった
            hash_hash[idx] = hs;
            if(up != NONE) hash_upper[idx] = up;
            if(low != NONE) hash_lower[idx] = low;

            hash_depth[idx] = depth;
            break;
        }else{
            if(hash_next[idx]==-1){//続きなかった
                if(hash_last_index >= HASH_BUFFER_SIZE-1){//満杯だった
                    //printf("Hash table is full !\n");
                    clear_hash();
                }
                hash_hash[hash_last_index] = hs;
                if(up != NONE) hash_upper[hash_last_index] = up;
                if(low != NONE) hash_lower[hash_last_index] = low;
                hash_depth[hash_last_index] = depth;

                hash_next[idx] = hash_last_index;
                hash_last_index ++;
                break;

            }else{//続きあった、次のインデックスへ
                idx = hash_next[idx];
            }

        }
    }

}

//アルファベータサーチ
int alpha_beta(board &obj,int depth,int al,int bt,int my_turn){
    int i;
    int evl;
    uint64_t adrs_num = 1;
    uint64_t can_copy;
    uint64_t black_copy;
    uint64_t white_copy;
    int turn_copy;
    int cannum_copy;

    node_count ++;

    if(depth==0 || obj.end_flag == 1 || obj.cannum == 0){
        return evaluator(obj,my_turn);
    }
    //obj.search();


    black_copy = obj.black;
    white_copy = obj.white;
    can_copy = obj.can;
    cannum_copy = obj.cannum;
    turn_copy = obj.turn;

    if(obj.turn == my_turn){//自分のノード
        for(i=0;i<cannum_copy;i++){

            if(cannum_copy == 1){
                obj.put(can_copy);
            }else{
                while((adrs_num & can_copy)==0) adrs_num <<= 1;
                obj.put(adrs_num,1);
                adrs_num <<= 1;
            }
            obj.phase ++;

            evl = alpha_beta(obj,depth-1,al,bt,my_turn);

            obj.phase --;
            obj.black = black_copy;
            obj.white = white_copy;
            obj.turn = turn_copy;
            //obj.can = can_copy;
            //obj.cannum = cannum_copy;

            if(al < evl){
                al = evl;
            }
            if(bt<=al){
                return bt;
            }
        }
        return al;
    }else{//相手のノード
        for(i=0;i<cannum_copy;i++){

            if(cannum_copy == 1){
                obj.put(can_copy);
            }else{
                while((adrs_num & can_copy)==0) adrs_num <<= 1;
                obj.put(adrs_num,1);
                adrs_num <<= 1;
            }
            obj.phase ++;
            evl = alpha_beta(obj,depth-1,al,bt,my_turn);

            obj.phase --;
            obj.black = black_copy;
            obj.white = white_copy;
            obj.turn = turn_copy;
            //obj.can = can_copy;
            //obj.cannum = cannum_copy;

            if(bt > evl){
                bt = evl;
            }
            if(bt<=al){
                return al;
            }
        }
        return bt;
    }
}

// int can_rnk[64]={90,10,40,20,20,40,10,90,
//                  10, 5,30,40,40,30, 5,10,
//                  40,30,20,15,15,20,30,40,
//                  20,40,15,36,36,15,40,20,
//                  20,40,15,36,36,15,40,20,
//                  40,30,20,15,15,20,30,40,
//                  10, 5,30,40,40,30, 5,10,
//                  90,10,40,20,20,40,10,90};

//ハッシュテーブルを用いた,アルファベータサーチ
int alpha_beta_with_memory(board &obj,int depth,int al,int bt,int my_turn){
    int i,g;
    int AB,evl;
    uint64_t hs = 0;
    int hs_idx;
    uint64_t adrs_num;
    uint64_t can_copy;
    uint64_t black_copy;
    uint64_t white_copy;
    int upper,lower;
    int turn_copy;
    int cannum_copy;
    uint64_t can_list[30];
    int can_list_rnk[30];

    node_count ++;
    if(timeout < time(NULL)) return NONE;

    if(depth==0 || obj.end_flag == 1 || obj.cannum == 0){
        g =  evaluator(obj,my_turn);
    }else {
        if(depth >= 4 ){//depthがこの値以下の時、ハッシュテーブルは使用されない(実験的な値)

            hs = get_hash(obj,my_turn);
            hs_idx = search_index_from_hash_table(hs,depth);
            if(hs_idx != NONE){//見つかった
                lower = hash_lower[hs_idx];
                if(bt <= lower) return lower;

                upper = hash_upper[hs_idx];
                if(upper <= al) return upper;

                if(upper == lower) return upper;

                if(al < lower) al = lower;

                if(bt > upper) bt = upper;

            }
        }

        adrs_num = 1;
        black_copy = obj.black;
        white_copy = obj.white;
        can_copy = obj.can;
        cannum_copy = obj.cannum;
        turn_copy = obj.turn;

        if(cannum_copy >= 2){//Move ordring を行う条件
            g = 1;
        }else{
            g = 0;
        }

        if(cannum_copy != 1){
            for(i=0;i<cannum_copy;i++){
                while((adrs_num & can_copy)==0) adrs_num <<= 1;
                if(g){
                    obj.put(adrs_num,1);
                    obj.search();
                    if(obj.pass_flag){
                        can_list_rnk[i] = -1;
                    }else{
                        can_list_rnk[i] = obj.cannum;
                    }

                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;
                }
                can_list[i] = adrs_num;

                adrs_num <<= 1;
            }

            if(g){
                MergeSort(can_list_rnk,can_list,0,cannum_copy-1);
            }
        }

        if(turn_copy == my_turn){//自分のノード
            g = MIN_VAL;
            AB = al;

            if(cannum_copy == 1){//おける場所がひとつ
                obj.put(can_copy,1);
                obj.phase ++;
                g = alpha_beta_with_memory(obj,depth-1,AB,bt,my_turn);
                obj.phase --;

                if(g == NONE) return NONE;
                return g;
                // obj.black = black_copy;
                // obj.white = white_copy;
                // obj.turn = turn_copy;
            }else{
                for(i=0;i<cannum_copy;i++){

                    /*
                    while((adrs_num & can_copy)==0) adrs_num <<= 1;
                    obj.put(adrs_num,1);
                    adrs_num <<= 1;
                    */
                    obj.put(can_list[i],1);

                    obj.phase ++;
                    evl = alpha_beta_with_memory(obj,depth-1,AB,bt,my_turn);

                    obj.phase --;
                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;

                    if(g == NONE) return NONE;

                    if(evl > g){
                        g = evl;//g <- MAX
                        if(bt <= g){//beta cut
                            break;
                        }
                    }
                    if(AB < g) AB = g;
                }
            }

        }else{//相手のノード
            g = MAX_VAL;
            AB = bt;

            if(cannum_copy == 1){//盤面の生成
                obj.put(can_copy,1);
                obj.phase ++;
                g = alpha_beta_with_memory(obj,depth-1,al,AB,my_turn);

                obj.phase --;

                if(g == NONE) return NONE;
                return g;
                // obj.black = black_copy;
                // obj.white = white_copy;
                // obj.turn = turn_copy;
            }else{
                for(i=0;i<cannum_copy;i++){

                    /*
                    while((adrs_num & can_copy)==0) adrs_num <<= 1;
                    obj.put(adrs_num,1);
                    adrs_num <<= 1;
                    */
                    obj.put(can_list[i],1);
                    obj.phase ++;

                    evl = alpha_beta_with_memory(obj,depth-1,al,AB,my_turn);

                    obj.phase --;
                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;

                    if(g == NONE) return NONE;

                    if(g > evl){
                        g = evl;//g <- MIN
                        if(g <= al){//Alpha cut
                            break;
                        }
                    }

                    if(AB > g) AB = g;
                }
            }
        }
    }

    if(hs != 0){
        if(g > al && g<bt){
            if(64-obj.phase <= depth){//全探索の時、depth = 60
                update_hash(hs,60,g,g);
            }else{
                update_hash(hs,depth,g,g);
            }
        }
        if( g <= al) update_hash(hs,depth,NONE,g);
        if( bt <= g) update_hash(hs,depth,g,NONE);
    }

    return g;
}

//終盤探索のためにチューニング済み 評価は石の差のみを返すサーチ
int search_for_end_game(board &obj,int depth,int al,int bt,int my_turn){
    int i,g;
    int AB,evl;
    uint64_t hs = 0;
    int hs_idx;
    uint64_t adrs_num;
    uint64_t can_copy;
    uint64_t black_copy;
    uint64_t white_copy;
    int upper,lower;
    int turn_copy;
    int cannum_copy;
    int black_cnt,white_cnt;
    uint64_t can_list[30];
    int can_list_rnk[30];


    node_count ++;

    if(depth==0 || obj.end_flag == 1 || obj.cannum == 0){//評価部分

        if(obj.black == 0){
            if(my_turn == 1) g = -999;
            else g = 999;

        }else if(obj.white == 0){
            if(my_turn == -1) g = -999;
            else g = 999;

        }else{
            black_cnt = bitcnt64(obj.black);
            white_cnt = bitcnt64(obj.white);
            if(my_turn == 1) g = (black_cnt - white_cnt) * 10;
            else g = (black_cnt - white_cnt) * -10;
        }

        g *= RVC;

    }else {

        if(depth >= 6 && obj.cannum >= 6 ){//depthがこの値以下の時、ハッシュテーブルは使用されない(実験的な値)

            hs = get_hash(obj,my_turn);
            hs_idx = search_index_from_hash_table(hs,depth);
            if(hs_idx != NONE){//見つかった
                lower = hash_lower[hs_idx];
                if(bt <= lower) return lower;

                upper = hash_upper[hs_idx];
                if(upper <= al) return upper;

                if(upper == lower) return upper;

                if(al < lower) al = lower;

                if(bt > upper) bt = upper;
            }
        }

        adrs_num = 1;
        evl = 0;
        black_copy = obj.black;
        white_copy = obj.white;
        can_copy = obj.can;
        cannum_copy = obj.cannum;
        turn_copy = obj.turn;

        if(cannum_copy >= 3 && depth >= 5){//Move ordring を行う条件
            g = 1;
        }else{
            g = 0;
        }

        if(cannum_copy != 1){//手数が少ない場所から探索するようにソート
            for(i=0;i<cannum_copy;i++){
                while((adrs_num & can_copy)==0){
                    adrs_num <<= 1;
                    evl ++;
                }

                if(g){
                    obj.put(adrs_num,1);
                    obj.search();
                    if(obj.pass_flag){
                        can_list_rnk[i] = -1;
                    }else{
                        can_list_rnk[i] = obj.cannum;
                    }


                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;
                }
                can_list[i] = adrs_num;

                adrs_num <<= 1;
            }
            if(g){
                MergeSort(can_list_rnk,can_list,0,cannum_copy-1);
            }
        }

        if(turn_copy == my_turn){//自分のノード
            g = MIN_VAL;
            AB = al;

            if(cannum_copy == 1){//おける場所がひとつ
                obj.put(can_copy,1);
                obj.phase++;
                evl = search_for_end_game(obj,depth-1,AB,bt,my_turn);

                obj.phase--;
                obj.black = black_copy;
                obj.white = white_copy;
                obj.turn = turn_copy;

                if(evl > g) g = evl;//g <- MAX
            }else{
                for(i=0;i<cannum_copy;i++){

                    obj.put(can_list[i],1);
                    obj.phase++;
                    evl = search_for_end_game(obj,depth-1,AB,bt,my_turn);

                    obj.phase--;
                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;

                    if(evl > g){
                        g = evl;//g <- MAX
                        if(bt <= g){//beta cut
                            break;
                        }
                    }
                    if(AB < g) AB = g;
                }
            }

        }else{//相手のノード
            g = MAX_VAL;
            AB = bt;

            if(cannum_copy == 1){//盤面の生成
                obj.put(can_copy,1);

                obj.phase++;
                evl = search_for_end_game(obj,depth-1,al,AB,my_turn);

                obj.phase--;
                obj.black = black_copy;
                obj.white = white_copy;
                obj.turn = turn_copy;

                if(g > evl) g = evl;//g <- MIN
            }else{
                for(i=0;i<cannum_copy;i++){

                    obj.put(can_list[i],1);
                    obj.phase++;
                    evl = search_for_end_game(obj,depth-1,al,AB,my_turn);

                    obj.phase--;
                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;

                    if(g > evl){
                        g = evl;//g <- MIN
                        if(g <= al){//Alpha cut
                            break;
                        }
                    }

                    if(AB > g) AB = g;
                }
            }
        }
    }

    if(hs != 0){
        if(g > al && g<bt)update_hash(hs,depth,g,g);
        if( g <= al) update_hash(hs,depth,NONE,g);
        if( bt <= g) update_hash(hs,depth,g,NONE);
    }

    return g;
}

#define MPC_T 1.0//許容誤差倍率
//ハッシュテーブルを用いた,アルファベータサーチ
int MPC_with_memory(board &obj,int depth,int al,int bt,int my_turn){
    int i,g;
    int AB,evl;
    uint64_t hs = 0;
    int hs_idx;
    uint64_t adrs_num;
    uint64_t can_copy;
    uint64_t black_copy;
    uint64_t white_copy;
    int upper,lower;
    int turn_copy;
    int cannum_copy;
    uint64_t can_list[30];
    int can_list_rnk[30];
    int mini_depth,bound,stage;

    node_count ++;


    if(depth==0 || obj.end_flag == 1 || obj.cannum == 0){
        g =  evaluator(obj,my_turn);
    }else {
        if(depth >= 4 ){//depthがこの値以下の時、ハッシュテーブルは使用されない(実験的な値)

            hs = get_hash(obj,my_turn);
            hs_idx = search_index_from_hash_table(hs,depth);
            if(hs_idx != NONE){//見つかった
                lower = hash_lower[hs_idx];
                if(bt <= lower) return lower;

                upper = hash_upper[hs_idx];
                if(upper <= al) return upper;

                if(upper == lower) return upper;

                if(al < lower) al = lower;

                if(bt > upper) bt = upper;

            }
        }

        adrs_num = 1;
        black_copy = obj.black;
        white_copy = obj.white;
        can_copy = obj.can;
        cannum_copy = obj.cannum;
        turn_copy = obj.turn;

        if( (depth <= MPC_MAX) && (depth >= MPC_MIN) && (obj.phase < MPC_STAGE) && (al != MIN_VAL) && (bt != MAX_VAL)){//MPCが行われるかもしれない
                stage = obj.phase;

                i = depth - MPC_MIN;
                mini_depth = MPC_pair[i][1];

                bound = (int)(( MPC_T * MPC_parameter[i][stage][2] + bt - MPC_parameter[i][stage][1] ) / MPC_parameter[i][stage][0]);
                if(MPC_parameter[i][stage][0] < 0) bound *= -1;
                evl = MPC_with_memory(obj,mini_depth,bound-1,bound,my_turn);
                if(evl >= bound){//CUT
                    return bt;
                }

                bound = (int)(( -MPC_T * MPC_parameter[i][stage][2] + al - MPC_parameter[i][stage][1] ) / MPC_parameter[i][stage][0]);
                if(MPC_parameter[i][stage][0] < 0) bound *= -1;
                evl = MPC_with_memory(obj,mini_depth,bound,bound+1,my_turn);

                if(evl <= bound){//CUT
                    return al;
                }
            }

        if(cannum_copy >= 2){//Move ordring を行う条件
            g = 1;
        }else{
            g = 0;
        }

        if(cannum_copy != 1){
            for(i=0;i<cannum_copy;i++){
                while((adrs_num & can_copy)==0) adrs_num <<= 1;
                if(g){
                    obj.put(adrs_num,1);
                    obj.search();
                    if(obj.pass_flag){
                        can_list_rnk[i] = -1;
                    }else{
                        can_list_rnk[i] = obj.cannum;
                    }

                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;
                }
                can_list[i] = adrs_num;

                adrs_num <<= 1;
            }

            if(g){
                MergeSort(can_list_rnk,can_list,0,cannum_copy-1);
            }
        }

        if(turn_copy == my_turn){//自分のノード
            g = MIN_VAL;
            AB = al;

            if(cannum_copy == 1){//おける場所がひとつ
                obj.put(can_copy,1);
                obj.phase ++;
                g = MPC_with_memory(obj,depth-1,AB,bt,my_turn);

                obj.phase --;

                return g;
                // obj.black = black_copy;
                // obj.white = white_copy;
                // obj.turn = turn_copy;
            }else{
                for(i=0;i<cannum_copy;i++){

                    /*
                    while((adrs_num & can_copy)==0) adrs_num <<= 1;
                    obj.put(adrs_num,1);
                    adrs_num <<= 1;
                    */
                    obj.put(can_list[i],1);

                    obj.phase ++;
                    evl = MPC_with_memory(obj,depth-1,AB,bt,my_turn);

                    obj.phase --;
                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;

                    if(evl > g){
                        g = evl;//g <- MAX
                        if(bt <= g){//beta cut
                            break;
                        }
                    }
                    if(AB < g) AB = g;
                }
            }

        }else{//相手のノード
            g = MAX_VAL;
            AB = bt;

            if(cannum_copy == 1){//盤面の生成
                obj.put(can_copy,1);
                obj.phase ++;
                g = MPC_with_memory(obj,depth-1,al,AB,my_turn);

                obj.phase --;
                return g;
                // obj.black = black_copy;
                // obj.white = white_copy;
                // obj.turn = turn_copy;
            }else{
                for(i=0;i<cannum_copy;i++){

                    /*
                    while((adrs_num & can_copy)==0) adrs_num <<= 1;
                    obj.put(adrs_num,1);
                    adrs_num <<= 1;
                    */
                    obj.put(can_list[i],1);
                    obj.phase ++;

                    evl = MPC_with_memory(obj,depth-1,al,AB,my_turn);

                    obj.phase --;
                    obj.black = black_copy;
                    obj.white = white_copy;
                    obj.turn = turn_copy;

                    if(g > evl){
                        g = evl;//g <- MIN
                        if(g <= al){//Alpha cut
                            break;
                        }
                    }

                    if(AB > g) AB = g;
                }
            }
        }
    }

    if(hs != 0){
        if(g > al && g<bt){
            if(64-obj.phase <= depth){//全探索の時、depth = 60
                update_hash(hs,60,g,g);
            }else{
                update_hash(hs,depth,g,g);
            }
        }
        if( g <= al) update_hash(hs,depth,NONE,g);
        if( bt <= g) update_hash(hs,depth,g,NONE);
    }

    return g;
}


//MTD(f)[Memory-enhanced Test Driver with node n and value f]を用いたサーチ
int MTDf(board &obj,int depth,int my_turn){
    static int fg = 0;
    int g = 0;
    int upper = MAX_VAL;
    int lower = MIN_VAL;
    int beta;

    uint64_t black_copy;
    uint64_t white_copy;
    int turn_copy;


    black_copy = obj.black;
    white_copy = obj.white;
    turn_copy = obj.turn;
    obj.search();

    g = fg;

    while(lower < upper){
        if(g == lower){
            beta = g+1;
        }else{
            beta = g;
        }

        obj.search();
        g = alpha_beta_with_memory(obj,depth,beta-1,beta,my_turn);

        if(timeout < time(NULL) || g == NONE){
            g=NONE;
            break;
        }

        if( g<beta){
            upper = g;
        }else{
            lower = g;
        }
    }

    obj.black = black_copy;
    obj.white = white_copy;
    obj.turn = turn_copy;
    obj.search();

    if( g != NONE )fg = g;
    return g;
}

//反復進化探索
int IDDFS(board &obj,int depth,int my_turn,int time_lim){
    int d;
    int score;
    int evl;

    timeout = time(NULL) + (time_t)time_lim ;

    d=4;
    if(depth <= d){
        d = 1;
    }

    for(;d<depth;d++){
        obj.search();
        evl = MTDf(obj,d,my_turn);
        if(evl != NONE){
            score = evl;
        }else{
            break;
        }
    }
    //printf("D=%d \n",d);

    return score;
}

double rand_double(){//0.0~1.0
    static int flag = 0;
    if(flag == 0){
        srand((unsigned int)time(NULL));
        flag = 1;
    }

    return (double)rand()/((double)RAND_MAX+1);
}

//配列のデータを並び替える
void shuffle(int array[],int size){
    int i;
    int j;
    int t;
    for(i=0;i<size;i++){
        j = rand()%size;
        t = array[i];
        array[i] = array[j];
        array[j] = t;
    }
}

//------------------------------- EVALUATOR ------------------------------------

int ptn_idx_list[USE_PTN][4][10];//抽出対象のインデックス＋回転させたもの
double weight[STAGE_PTN][WEIGHT_NUMBER];//パターンの重みを格納する
int weight_light[STAGE_PTN][WEIGHT_NUMBER];//↓計算高速化のためにweights*10kで保持

int jump_table[7][59049];//(3^4)81=45  (3^5)243=>135  (3^6)729=>378  (3^7)2187=>1134 (3^8)6561=>3321 (3^9)19683=>9963 (3^10)59049=>29645抽出した値から、WeightのINDEXを探す
int ptn_bit[] = {10,8,8,8,9,4,5,6,7,8,10};//各-パターンで使用されるマスの数


void kihu_cnv(int ids,int phs,int x,int y,int flag = 0){//pythonように作った棋譜データをC++用に変換するための関数
    static int kihuc[KIHU_ALL_DATA][61];

    if(flag == 0){//変換モード
        if(phs != 0){
            if(x == -1 ){
                kihuc[ids][phs] = -1;
            }else{
                kihuc[ids][phs] = (y-1)*8 + (x-1);
            }

        }else{
            kihuc[ids][phs] = x;
        }
    }

    if(flag == 1){
        FILE *fp;

        fp = fopen("./kihu_c.dat","wb");
        if( fp == NULL) return;//open filed

        fwrite(kihuc,sizeof(int),KIHU_ALL_DATA*61,fp);
        fclose(fp);

        printf("kihu save ok\n");
    }
}

int kihu_load(int kihu[KIHU_ALL_DATA][61]){
    FILE *fp;

    fp = fopen("./kihu_c.dat","rb");
    if( fp == NULL){
        printf("<ERROR> kihu_c.dat is not found.\n");
        return 0;//open filed
    }

    fread(kihu,sizeof(int),KIHU_ALL_DATA*61,fp);
    fclose(fp);

    printf("kihu load ok\n");
    return 1;
}

inline int stage_selecter(int phase){
    // int out;
    // static int flag = 0;
    // static int sel[60];
    // if(flag==0){
    //     for(flag=0;flag<60;flag++){
    //
    //         sel[flag] = (int)((double)flag * (1.0 / (60.0/(STAGE_PTN))));
    //
    //         // sel[flag] = 0;
    //         // if(flag >= 10){
    //         //     sel[flag] ++;
    //         //     if(flag>=20){
    //         //         sel[flag] += 1+(flag-20) / 2;
    //         //     }
    //         // }
    //
    //         //printf("%d => %d\n",flag,sel[flag]);
    //     }
    //     flag = 1;
    // }
    // return sel[phase];
    return (int)((double)phase * (1.0 / (60.0/(STAGE_PTN))));
}

void weight_init(){
    int i,j;
    for(i=0;i<STAGE_PTN;i++){
        for(j=0;j<WEIGHT_NUMBER;j++){
            weight[i][j] = rand_double()*2.0 - 1.0;
        }
    }
    printf("Weights_c initialize ok\n");
}

void weight_save(int num=-1){
    FILE *fp;
    char filename[100];

    if(num == -1){
        sprintf(filename,"./weights_c.dat");
    }else{
        sprintf(filename,"./weights_c_%d.dat",num);
    }

    fp = fopen(filename,"wb");


    if( fp == NULL){
        printf("<ERROR> Cannot save the file of weights_c.dat.\n");
        exit(1);
    }

    fwrite(weight,sizeof(weight),1,fp);
    fclose(fp);

    printf("weights_c save ok\n");
}

void weight_load(){
    FILE *fp;
    fp = fopen("./weights_c.dat","rb");

    if( fp == NULL){
        printf("<ERROR> Cannot load the file of weights_c.dat.\n");
        return;
    }

    fread(weight,sizeof(weight),1,fp);
    fclose(fp);

    printf("weights_c load ok\n");
}

void MPC_save(){//12通りのパターンで,a,bを格納する
    FILE *fp;
    char filename[100];

    sprintf(filename,"data/system/MPC_c.dat");


    fp = fopen(filename,"wb");


    if( fp == NULL){
        printf("<ERROR> Cannot save the file of MPC_c.dat.\n");
        exit(1);
    }

    fwrite(MPC_parameter,sizeof(MPC_parameter),1,fp);
    fclose(fp);

    printf("MPC_c save ok\n");
}

void MPC_load(){
    FILE *fp;

    fp = fopen("data/system/MPC_c.dat","rb");
    if( fp == NULL){
        printf("<ERROR> MPC_c.dat is not found.\n");
        return;
    }

    fread(MPC_parameter,sizeof(MPC_parameter),1,fp);
    fclose(fp);


    printf("MPC_c load ok\n");

}

void set_pattern(){
    int cell[10];
    int x,y,i,j,k,a,b,c,idx,max_num;
    int turn_table[64];
    int jp_bf[59049];

    //パターン抽出用インデックスの登録
    idx = 0;

    //#1 辺に対する部分 A
    ptn_idx_list[idx][0][0] = 0;ptn_idx_list[idx][0][1] = 1;ptn_idx_list[idx][0][2] = 2;
    ptn_idx_list[idx][0][3] = 3;ptn_idx_list[idx][0][4] = 4;ptn_idx_list[idx][0][5] = 5;
    ptn_idx_list[idx][0][6] = 6;ptn_idx_list[idx][0][7] = 7;ptn_idx_list[idx][0][8] = 9;
    ;ptn_idx_list[idx][0][9] = 14;
    idx ++;

    //#2 辺B
    ptn_idx_list[idx][0][0] = 8;ptn_idx_list[idx][0][1] = 9;ptn_idx_list[idx][0][2] = 10;
    ptn_idx_list[idx][0][3] = 11;ptn_idx_list[idx][0][4] = 12;ptn_idx_list[idx][0][5] = 13;
    ptn_idx_list[idx][0][6] = 14;ptn_idx_list[idx][0][7] = 15;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#3 辺C
    ptn_idx_list[idx][0][0] = 16;ptn_idx_list[idx][0][1] = 17;ptn_idx_list[idx][0][2] = 18;
    ptn_idx_list[idx][0][3] = 19;ptn_idx_list[idx][0][4] = 20;ptn_idx_list[idx][0][5] = 21;
    ptn_idx_list[idx][0][6] = 22;ptn_idx_list[idx][0][7] = 23;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#4 辺D
    ptn_idx_list[idx][0][0] = 24;ptn_idx_list[idx][0][1] = 25;ptn_idx_list[idx][0][2] = 26;
    ptn_idx_list[idx][0][3] = 27;ptn_idx_list[idx][0][4] = 28;ptn_idx_list[idx][0][5] = 29;
    ptn_idx_list[idx][0][6] = 30;ptn_idx_list[idx][0][7] = 31;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#5 角周り
    ptn_idx_list[idx][0][0] = 0;ptn_idx_list[idx][0][1] = 1;ptn_idx_list[idx][0][2] = 2;
    ptn_idx_list[idx][0][3] = 8;ptn_idx_list[idx][0][4] = 9;ptn_idx_list[idx][0][5] = 10;
    ptn_idx_list[idx][0][6] = 16;ptn_idx_list[idx][0][7] = 17;ptn_idx_list[idx][0][8] = 18;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#6 斜めA
    ptn_idx_list[idx][0][0] = 3;ptn_idx_list[idx][0][1] = 10;ptn_idx_list[idx][0][2] = 17;
    ptn_idx_list[idx][0][3] = 24;ptn_idx_list[idx][0][4] = -1;ptn_idx_list[idx][0][5] = -1;
    ptn_idx_list[idx][0][6] = -1;ptn_idx_list[idx][0][7] = -1;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#7 斜めB
    ptn_idx_list[idx][0][0] = 4;ptn_idx_list[idx][0][1] = 11;ptn_idx_list[idx][0][2] = 18;
    ptn_idx_list[idx][0][3] = 25;ptn_idx_list[idx][0][4] = 32;ptn_idx_list[idx][0][5] = -1;
    ptn_idx_list[idx][0][6] = -1;ptn_idx_list[idx][0][7] = -1;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#8 斜めC
    ptn_idx_list[idx][0][0] = 5;ptn_idx_list[idx][0][1] = 12;ptn_idx_list[idx][0][2] = 19;
    ptn_idx_list[idx][0][3] = 26;ptn_idx_list[idx][0][4] = 33;ptn_idx_list[idx][0][5] = 40;
    ptn_idx_list[idx][0][6] = -1;ptn_idx_list[idx][0][7] = -1;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#9 斜めD
    ptn_idx_list[idx][0][0] = 6;ptn_idx_list[idx][0][1] = 13;ptn_idx_list[idx][0][2] = 20;
    ptn_idx_list[idx][0][3] = 27;ptn_idx_list[idx][0][4] = 34;ptn_idx_list[idx][0][5] = 41;
    ptn_idx_list[idx][0][6] = 48;ptn_idx_list[idx][0][7] = -1;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#10 斜めE
    ptn_idx_list[idx][0][0] = 7;ptn_idx_list[idx][0][1] = 14;ptn_idx_list[idx][0][2] = 21;
    ptn_idx_list[idx][0][3] = 28;ptn_idx_list[idx][0][4] = 35;ptn_idx_list[idx][0][5] = 42;
    ptn_idx_list[idx][0][6] = 49;ptn_idx_list[idx][0][7] = 56;ptn_idx_list[idx][0][8] = -1;
    ;ptn_idx_list[idx][0][9] = -1;
    idx ++;

    //#11 長方形
    ptn_idx_list[idx][0][0] = 0;ptn_idx_list[idx][0][1] = 1;ptn_idx_list[idx][0][2] = 2;
    ptn_idx_list[idx][0][3] = 3;ptn_idx_list[idx][0][4] = 4;ptn_idx_list[idx][0][5] = 8;
    ptn_idx_list[idx][0][6] = 9;ptn_idx_list[idx][0][7] = 10;ptn_idx_list[idx][0][8] = 11;
    ;ptn_idx_list[idx][0][9] = 12;


    for(x=0;x<8;x++){//ターンテーブルの生成
        for(y=0;y<8;y++){
            turn_table[ (7-y)*8+x ] = x * 8 + y;
        }
    }

    for(idx=0;idx<USE_PTN;idx++){//90° 180° 270°のものを生成する
        for(i=1;i<4;i++){
            for(j=0;j<10;j++){
                if(ptn_idx_list[idx][i-1][j]==-1) break;
                ptn_idx_list[idx][i][j] = turn_table[ ptn_idx_list[idx][i-1][j] ];
            }
        }
    }

    for(i=0;i<6;i++){
        for(j=0;j<59049;j++){
            jump_table[i][j] = 0;
        }
    }

    for(i=4;i<(10+1);i++){

        for(j=0;j<10;j++){//初期化
            cell[j] = 0;
        }
        for(j=0;j<59049;j++){
            jp_bf[j] = -1;
        }
        max_num = (int)pow(3,i);

        idx = 0;

        for(j=0;j<max_num;j++){//対象性のあるものを登録する 4,5,6,7,8

            cell[0] ++;//cell配列を3ビットのビット列としてみなし、インクリメント
            for(k=0;k<10;k++){
                if(cell[k] == 3){
                    cell[k] = 0;
                    cell[k+1] ++;
                }else{
                    break;
                }
            }

            a = 0;
            b = 0;
            for(k=0;k<i;k++){
                a += cell[k]*pow(3.0,k);
                b += cell[k]*pow(3.0,i-k-1);
            }

            if(a>b){
                c = b;
            }else{
                c = a;
            }
            for(k=0;k<max_num;k++){
                if(jp_bf[k]==c){
                    break;
                }
                if(jp_bf[k]==-1){
                    jp_bf[idx] = c;
                    jump_table[i-4][a] = idx;
                    jump_table[i-4][b] = idx;
                    idx ++;
                    break;
                }
            }
        }//USE_PTN loop
        //printf("MAX=%d Num=%d\n",max_num,idx);

    }
}

int get_pattern(board &obj,int array[USE_PTN*4],int stage = -1){//
    static int flag = 0;
    static int tree_pow[10];
    int key,j,bias;
    int ptn_id,turn_id,i;
    int out = 0;

    if(flag == 0){//パターンインデックスの格納と初期設定をしておく
        if((60 % STAGE_PTN) != 0){
            j = -1;
            bias = 0;
            for(i=0;i<60;i++){
                bias = stage_selecter(i);
                //printf("%d ",bias);
                if((j+1) == bias){
                    j ++;
                }
            }
            if(j != STAGE_PTN-1){
                printf("<ERROR> STAGE_PTN must be a number divisible by \"60\" \n");
                exit(1);
            }

        }

        flag = 1;

        for(i=0;i<10;i++){//予め３の塁上は計算しておく
            tree_pow[i] = pow(3,i);
        }

        //int weight_light[STAGE_PTN][WEIGHT_NUMBER];//↓計算高速化のためにweights*10kで保持
        for(i = 0;i<STAGE_PTN;i++){
            for(j = 0;j<WEIGHT_NUMBER;j++){
                weight_light[i][j] = (int)((double)weight[i][j]*10000.0);
            }
        }

        set_pattern();
        // printf("Pattern set ok\n");
    }

    j = 0;
    bias = 0;
    //パターンの検索を行う
    for(ptn_id=0;ptn_id<USE_PTN;ptn_id++){//パターンの種類

        for(turn_id=0;turn_id<4;turn_id++){//４回転させたもの
            key = 0;
            for(i=0;i<ptn_bit[ptn_id];i++){//要素を抽出 空白:0 黒:1 白:2
                if((adrs[ ptn_idx_list[ptn_id][turn_id][i] ] & obj.black) != 0){//Black
                    key += tree_pow[i];
                }else if((adrs[ ptn_idx_list[ptn_id][turn_id][i] ] & obj.white) != 0){//white
                    key +=  tree_pow[i]+tree_pow[i];
                }
            }

            if(stage == -1){
                array[j] = jump_table[ptn_bit[ptn_id]-4][key] + bias;
            }else{
                //out += weight[stage][jump_table[ptn_bit[ptn_id]-4][key] + bias];
                out += weight_light[stage][jump_table[ptn_bit[ptn_id]-4][key] + bias];
            }

            j ++;
        }

        switch(ptn_bit[ptn_id]){
            case 4:
                bias += 45;
            break;

            case 5:
                bias += 243;
            break;

            case 6:
                bias += 378;
            break;

            case 7:
                bias += 1134;
            break;

            case 8:
                bias += 3321;
            break;

            case 9:
                bias += 9963;
            break;

            case 10:
                bias += 29645;
            break;
        }
    }

    if(stage == -1){
        return 0;
    }
    out = (int)((double)out*0.001);

    return out;

}

inline int evaluator(board &obj,int turn){
    int out;
    int stage_id;
    int array[USE_PTN*4];
    int black_cnt,white_cnt;


    if(obj.black == 0){
        if(turn == 1) return -999 * RVC;
        else return 999 * RVC;

    }else if(obj.white == 0){
        if(turn == -1) return -999 * RVC;
        else return 999 * RVC;

    }

    //printf(" PHASE=%d ",phase);
    if(obj.phase == 60 || obj.end_flag == 1||obj.cannum == 0){
        black_cnt = bitcnt64(obj.black);
        white_cnt = bitcnt64(obj.white);
        out = black_cnt - white_cnt;
        if(turn == 1) return out * 10 * RVC;
        else return out * -10 * RVC;
    }

    stage_id =  stage_selecter(obj.phase);

    out = get_pattern(obj,array,stage_id);

    //for(i=0;i<USE_PTN*4;i++){
    //    out += weight[stage_id][array[i]];
    //}
    //printf(" BSCORE=%lf ",out);

    return (out*turn) * RVC;
}

void evaluatorn_of_this_evaluator(){//モデルを評価するため、ターンごとの誤差を算出する

    static int kihu[KIHU_ALL_DATA][61];
    static int kihu_index[KIHU_ALL_DATA];

    board game;
    int array[USE_PTN*4];
    int i,j,k,phase,stage_id,smpl;
    double loss_a,loss_b,ans,value;

    double loss_phase[60];
    double smp_phase[60];

    srand((unsigned long)time(NULL));
    init_data_table();
    kihu_load(kihu);
    weight_load();


    for(i=0;i<60;i++){
        loss_phase[i] = 0;
        smp_phase[i] = 0;
    }

    srand((unsigned long)time(NULL));
    init_data_table();
    kihu_load(kihu);

    for(i=0;i<KIHU_ALL_DATA;i++){//インデックスを入れ込む
        kihu_index[i] = i;
    }
    shuffle(kihu_index,KIHU_ALL_DATA);



    loss_a = 0;
    loss_b = 0;
    smpl = 0;
    for(j=0;smpl<300000;j++){
        ans = (double)kihu[ kihu_index[j] ] [0];
        game.init_board();
        for(phase=0;phase<60;phase++){
            if(kihu[ kihu_index[j] ][phase+1] == -1) break;
            if(game.put(adrs[ kihu[kihu_index[j]][phase+1]]) == 0) break;

            get_pattern(game,array);
            stage_id = stage_selecter(phase);
            value = 0.0;
            for(k=0;k<(USE_PTN*4);k++){
                value += weight[stage_id][array[k]];
            }

            loss_a = (value - ans);
            if(loss_a < 0 ) loss_a = -loss_a;

            loss_b += loss_a;
            loss_phase[phase] += loss_a;
            smp_phase[phase] ++;

            smpl ++;
        }
    }

    for(i=0;i<60;i++){
        printf("[%d] PHASE  Loss=%lf\n",i,loss_phase[i]/smp_phase[i]);
    }
    printf("Average Loss = %lf\n",loss_b/smpl);
    exit(1);

}

void learn(int epoch){
    static int flag = 0;

    static int kihu[KIHU_ALL_DATA][61];
    static int kihu_index[KIHU_ALL_DATA];
    static int tearch_index[KIHU_ALL_DATA-KIHU_TEST_DATA];
    static int test_index[KIHU_TEST_DATA];

    //Adam のハイパパラメータ
    static int weight_cnt[STAGE_PTN][WEIGHT_NUMBER];
    static double weight_v[STAGE_PTN][WEIGHT_NUMBER];
    static double weight_m[STAGE_PTN][WEIGHT_NUMBER];
    double vt,mt;

    //int loop_unit = (KIHU_ALL_DATA-KIHU_TEST_DATA);
    int loop_unit = 1000;

    double betaA = 0.9;
    double betaB = 0.999;
    double alpha = 0.0001;
    double eq = 0.000001;

    board game;
    int array[USE_PTN*4];
    int i,j,k,n,phase,stage_id,smpl;
    double grad,loss_a,loss_b,ans,value;
    time_t st = time(NULL);

    if(flag == 0){
        flag = 1;
        srand((unsigned long)time(NULL));
        init_data_table();
        kihu_load(kihu);
        hash_malloc();

        for(i=0;i<STAGE_PTN;i++){
            for(j=0;j<WEIGHT_NUMBER;j++){
                weight_cnt[i][j] = 0;
                weight_v[i][j] = 0;
                weight_m[i][j] = 0;
            }
        }
    }

    for(i=0;i<KIHU_ALL_DATA;i++){//インデックスを入れ込む
        kihu_index[i] = i;
    }
    printf("\n");
    for(i=0;i<epoch;i++){//エポック

        if(i%5 == 0 && i != 0){
            weight_save();

            shuffle(kihu_index,KIHU_ALL_DATA);
            for(j=0;j<(KIHU_ALL_DATA-KIHU_TEST_DATA);j++){//インデックスを入れ込む
                tearch_index[j] = kihu_index[j];
            }
            for(j=(KIHU_ALL_DATA-KIHU_TEST_DATA);j<KIHU_TEST_DATA;j++){
                test_index[j] = kihu_index[i-1];
            }
        }



        //********************************評価用で評価****************************
        loss_a = 0;
        loss_b = 0;
        smpl = 0;
        for(j=0;smpl<10000;j++){
            ans = (double)kihu[ test_index[j] ] [0];
            game.init_board();
            for(phase=0;phase<60;phase++){
                if(kihu[ test_index[j] ][phase+1] == -1) break;
                if(game.put(adrs[ kihu[test_index[j]][phase+1]]) == 0) break;

                get_pattern(game,array);
                stage_id = stage_selecter(phase);
                value = 0.0;
                for(k=0;k<(USE_PTN*4);k++){
                    value += weight[stage_id][array[k]];
                }
                loss_a += (value - ans) * (value - ans);

                smpl ++;
            }
        }
        loss_a /= (double)smpl;

        smpl = 0 ;
        for(j=0;smpl<10000;j++){
            ans = (double)kihu[ tearch_index[j] ][0];
            game.init_board();
            for(phase=0;phase<60;phase++){
                if(kihu[ tearch_index[j] ][phase+1] == -1) break;
                if(game.put(adrs[ kihu[tearch_index[j]][phase+1]]) == 0) break;

                get_pattern(game,array);
                stage_id =  stage_selecter(phase);
                value = 0.0;
                for(k=0;k<(USE_PTN*4);k++){
                    value += weight[stage_id][array[k]];
                }
                loss_b += (value - ans) * (value - ans);
                smpl ++;
            }


        }

        loss_b /= (double)smpl;
        printf("Epoch:%3d   Test-Loss:%8.3lf    Tearch-Loss:%8.3lf    time=%d\n",i,loss_a,loss_b,(int)(time(NULL)-st));



        //**********************************************************************


        //******************************学習************************************
        for(j=0;j<loop_unit;j++){
            printf("\r%3.2lf％",(double)(100*j/loop_unit));

            ans = kihu[ tearch_index[j] ][0];
            game.init_board();

            for(phase=0;phase<60;phase++){
                if(kihu[ tearch_index[j] ][phase+1] == -1) break;
                if(game.put(adrs[ kihu[tearch_index[j]][phase+1]]) == 0){
                    game.display();
                    printf("%d %d\n",kihu[tearch_index[j]][phase+1]/8,kihu[tearch_index[j]][phase+1]%8);
                    exit(1);
                    break;
                }

                get_pattern(game,array);
                stage_id =  stage_selecter(phase);
                value = 0.0;
                for(k=0;k<(USE_PTN*4);k++){
                    value += weight[stage_id][array[k]];
                }


                if(phase >= 40){//終盤手の補正
                    game.search();
                    ans = (double)search_for_end_game(game,20,MIN_VAL,MAX_VAL,1) * 0.01;
                    game.search();
                }else{
                    game.search();
                    ans = IDDFS(game,15,1) * 0.01;
                    game.search();
                }

                grad = value - ans;

                for(k=0;k<(USE_PTN*4);k++){//Adamによる勾配降下
                    n = array[k];
                    weight_cnt[stage_id][n] ++;
                    weight_m[stage_id][n] = betaA * weight_m[stage_id][n]+(1-betaA)*grad;
                    weight_v[stage_id][n] = betaB * weight_v[stage_id][n]+(1-betaB)*(grad*grad);
                    mt = weight_m[stage_id][n] / (1-pow(betaA,weight_cnt[stage_id][n]));
                    vt = weight_v[stage_id][n] / (1-pow(betaB,weight_cnt[stage_id][n]));
                    weight[stage_id][n] -= alpha * mt/(sqrt(vt)+eq);
                }
            }
        }
        //*********************************************************************

    }
}

#define MPC_SAMPLES 2000
//phase_low ~ phase_high の範囲で計算する 0~45を学習させる
void MPC_CALC(int depth_big,int depth_mini ,int phase_low,int phase_high,double anser[3]){
    int i,j;
    int idx = 0;
    int work;
    static int kihu[KIHU_ALL_DATA][61];
    static int kihu_index[KIHU_ALL_DATA];
    static double X[MPC_SAMPLES];
    static double Y[MPC_SAMPLES];
    double X_AVG = 0.0;//平均
    double Y_AVG = 0.0;
    double STD_DEV = 0.0;//標準偏差

    double AA = 0.0,BB= 0.0,CC=0.0;//計算用(分子?)

    double eq = 0.00001;//ゼロ除算防止
    static int flag = 0;
    board game;

    if(depth_big < depth_mini){
        work = depth_big;
        depth_big = depth_mini;
        depth_mini = work;
    }

    if(flag == 0){
        flag = 1;

        init_data_table();
        hash_malloc();
        kihu_load(kihu);
        weight_load();
        srand((unsigned long)time(NULL));//乱数初期化
    }
    //hash_clear();


    for(i=0;i<MPC_SAMPLES;i++){
        X[i] = 0.0;
        Y[i] = 0.0;
    }

    for(i=0;i<KIHU_ALL_DATA;i++){
        kihu_index[i] = i; //シャッフルする
    }
    shuffle(kihu_index,KIHU_ALL_DATA);
    //V = a * v + b

    // a = () / ()
    fflush(stdout);

    for(i = 0; i < MPC_SAMPLES ; i++){//平均値を算出
        printf("\r%3.1lf％",(double)((100*i)/(MPC_SAMPLES)));

        game.init_board();
        for(j=0;j<phase_high+1;j++){

            if(kihu[ kihu_index[i] ][j+1] == -1) break;
            if(game.put(adrs[ kihu[kihu_index[i]][j+1]]) == 0) break;

            if(j >= phase_low && phase_high >= j){
                X[idx] = IDDFS(game,depth_mini,1);
                Y[idx] = IDDFS(game,depth_big,1);

                X_AVG += X[idx];
                Y_AVG += Y[idx];
                STD_DEV += (X[idx] - Y [idx]) * (X[idx] - Y [idx]);
                idx ++;
            }
        }

    }

    X_AVG /= idx;
    Y_AVG /= idx;
    //    double AA = 0.0,BB= 0.0,CC=0.0;//計算用(分子)
    //    double EE = 0.0,FF= 0.0;//計算用(分母)

    for(i = 0; i < idx ; i++){//計算の準備
        AA += (X[i] - X_AVG) * (Y[i] - Y_AVG);
        BB += (X[i] - X_AVG) * (X[i] - X_AVG);
        //CC += Y[i];
        //EE += X[i] * X[i];
    }
        //FF = BB * BB;
    //計算
    anser[0] = AA / (BB + eq);//(AA - (BB * CC)) / (EE - FF + eq);//a
    anser[1] = Y_AVG - (anser[0] * X_AVG);//( (EE * CC) - (AA * BB) ) / (EE - FF + eq);//b

    for(i = 0; i < idx ; i++){//計算の準備
        CC = Y[i] - (X[i] * anser[0]) + anser[1];
        STD_DEV +=CC * CC;
    }
    STD_DEV = sqrt(STD_DEV/idx);

    anser[2] = STD_DEV;
    printf("\n Depth_BIG=%d Depth_mini=%d : a=%lf b=%lf e=%lf\n",depth_big,depth_mini,anser[0],anser[1],anser[2]);
}

//Pythonから呼び出す。最善手を打ち合った時の Depth 手先の評価値を返す。ただしここでの評価値は最後まで打ち合った時の 石差ｘ１００ とする
int thouth_from_python(uint64_t black_pos,uint64_t white_pos,int turn,int my_turn,int depth,int search_method = 0,int board_size = 8){
    int static flag=0;
    int out = NONE;
    int d=0;
    int black_cnt,white_cnt;
    board game;

    game.init_board(board_size);

    //node_count = 0;

    if(flag == 0){//初期設定
        flag = 1;
        srand((unsigned long)time(NULL));
        init_data_table();
        weight_init();
        weight_load();
        MPC_load();
    }

    game.black = black_pos;
    game.white = white_pos;
    game.turn = turn;
    game.search();

    d = depth;
    timeout = time(NULL) + (time_t)300;

    black_cnt = bitcnt64(game.black);
    white_cnt = bitcnt64(game.white);
    game.phase = black_cnt + white_cnt - 4  + (64 - board_size * board_size);//フェーズ計算省略のために、予め計算しておく

    if(search_method==0){
        out = alpha_beta(game,d,MIN_VAL,MAX_VAL,my_turn);
    }
    if(search_method==1){
        hash_malloc();
        out = alpha_beta_with_memory(game,d,MIN_VAL,MAX_VAL,my_turn);
    }
    if(search_method==2){
        hash_malloc();
        out = MTDf(game,d,my_turn);
    }
    if(search_method==3){
        hash_malloc();
        out = search_for_end_game(game,d,MIN_VAL,MAX_VAL,my_turn);
    }
    if(search_method==4){
        hash_malloc();
        out = IDDFS(game,d,my_turn,3);
    }
    if(search_method==5){
        hash_malloc();
        //out = MPC_with_memory(game,d,MIN_VAL,MAX_VAL,my_turn);
        out = IDDFS(game,d,my_turn,1);
    }

    if(out == NONE){
        printf("<ERROR>Can you use this search-method\'s ID \"%d\" \n",search_method);
        exit(0);
    }

    if(0){//ノード数の表示、簡略化するか
        if(node_count < 1000){
            printf("nodes=%.1f\n",(double)node_count);
        }else if(node_count < (1000 * 1000 )){
            printf("nodes=%.1fK\n",(double)node_count/1000);
        }else{
            printf("nodes=%.1fM\n",(double)node_count/(1000 * 1000) );
        }
    }else{
        //printf("nodes=%.1f\n",(double)node_count);
    }


    if(out >= 1000 || out <= -1000){
        out /= 10;
    }
    return out;
}

int node_controll(int reset = 0){
    if(reset == 1){
        node_count = 0;
    }
    return node_count;
}


int main(){
    int sel =0;
    int i,j,k,l;
    int out;
    int max_num;
    double num;
    uint64_t pos;
    uint64_t max_pos;
    uint64_t black_bf;
    uint64_t white_bf;
    uint64_t can_bf;
    int turn_bf;

    int black_cnt, white_cnt;

    time_t st;
    board game;

    // evaluatorn_of_this_evaluator();  // モデル評価

    srand((unsigned long)time(NULL));
    init_data_table();


    printf("Menu Please choose by number\n*0 Learning\n*1 SearchTest\n*2 Game\n>>");
    scanf("%d",&sel);
    if(sel<0 || sel >3){
        printf("Error\n");
        return 0;
    }

    if(sel == 0){
        weight_init();
        printf("Load weight? Y=1 N=0\n>>");
        scanf("%d",&i,1);

        if(i==1) weight_load();

        while(1){
            printf("Please enter to epoch number\n>>");
            scanf("%d",&i);
            if(i < 0){
                printf("Error\n");
                return 0;
            }

            learn(i);
            weight_save();
        }

    }
    if(sel == 1){
        hash_malloc();
        weight_init();
        weight_load();
        printf("Please enter to search config\n");

        printf("Depth >>");
        scanf("%d",&k);

        clear_hash();

        game.init_board();
        st = time(NULL);
        out = alpha_beta(game,k,MIN_VAL,MAX_VAL,1);
        st = time(NULL) - st;
        printf("ALPHA-BETA-SEARCH       Score=%5d  t=%5d\n",out,(int)st);

        clear_hash();
        game.init_board();
        st = time(NULL);
        out = alpha_beta_with_memory(game,k,MIN_VAL,MAX_VAL,1);
        st = time(NULL) - st;
        printf("ALPHA-BETA-WITH-MEMORY  Score=%5d  t=%5d\n",out,(int)st);

        clear_hash();
        game.init_board();
        st = time(NULL);
        out = MTDf(game,k,1);
        st = time(NULL) - st;
        printf("MTD(f)                  Score=%5d  t=%5d\n",out,(int)st);
    }
    if(sel == 2){
        hash_malloc();
        max_num = MIN_VAL;
        pos = 1;
        max_pos = 0;

        weight_init();
        weight_load();
        game.init_board();

        while(game.end_flag == 0){
            printf("\n\n");
            if(game.turn == 1){
                printf("    @ BLACK TURN @\n\n");
            }else{
                printf("    O WHITE TURN O\n\n");
            }
            game.display();
            j = evaluator(game,game.turn);
            printf("Evaluation : %d\n",j);

            black_cnt = bitcnt64(game.black);
            white_cnt = bitcnt64(game.white);
            printf("Count: @x%d Ox%d\n", black_cnt, white_cnt);

            if(game.turn==1){//黒はプレイヤー
                printf("XY>>");
                scanf("%d",&i);
                game.put_xy(i/10,i%10);
            }else{//白はロボット
                max_num = MIN_VAL;
                pos = 1;
                max_pos = 0;
                k=0;

                white_bf = game.white;
                black_bf = game.black;
                turn_bf = game.turn;

                game.search();
                can_bf = game.can;
                j = game.cannum;

                for(l=0;l<j;l++){

                    while((can_bf & pos)==0) pos <<= 1;
                    game.put(pos,1);
                    if(64 - (black_cnt + white_cnt) > END_DEPTH){
                        k = IDDFS(game, SEARCH_DEPTH, -1, 3);
                    }else{
                        k = search_for_end_game(game, END_DEPTH, MIN_VAL, MAX_VAL, -1);
                    }
                    if(max_num <= k){
                        max_num = k;
                        max_pos = pos;
                    }
                    pos <<= 1;
                    game.white = white_bf;
                    game.black = black_bf;
                    game.turn = turn_bf;

                }
                game.white = white_bf;
                game.black = black_bf;
                game.turn = turn_bf;
                game.search();

                game.put(max_pos);
            }
        }

        game.display();

        black_cnt = bitcnt64(game.black);
        white_cnt = bitcnt64(game.white);
        printf("\nResult: @x%d Ox%d ", black_cnt, white_cnt);
        if(black_cnt > white_cnt){
            printf("You win!\n");
        }else if(black_cnt < white_cnt){
            printf("You lose..\n");
        }else{
            printf("Draw~\n");
        }
    }

    return 0;
}


//Python ラッパー
// BOOST_PYTHON_MODULE( robot_c ){
//     using namespace boost::python;
//     def( "thout_c",&thouth_from_python);
//     def( "hash_clear",&clear_hash);
//     def( "hash_free",&hash_free);
//     def( "node_cnt",&node_controll);
// }
